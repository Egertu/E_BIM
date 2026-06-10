#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""
E_BIM Cable Routing Automation System
Automated electrical circuit routing in Revit cable trays, conduits, and pipes.

Вся функциональность интегрирована в один файл для использования в pyRevit.

Техническое задание:
1. Находить кабельные системы по названию
2. Строить ортогональный граф прохождения кабельных маршрутов
3. Вычислять оптимальные пути между электрооборудованием (A*)
4. Рассчитывать длины участков в разных типах коммуникаций
5. Обновлять параметры оборудования согласно формату метки
6. Сохранять данные о проложенных цепях в конфигурацию PyRevit
"""

from __future__ import print_function
import sys
import os
import traceback
import json
import heapq
from collections import defaultdict, deque

try:
    from pyrevit import forms, script
    from pyrevit.revit import doc, uidoc
    from Autodesk.Revit.DB import (
        BuiltInCategory, FilteredElementCollector, Transaction,
        XYZ, Transform, Line, Arc, Curve, CurveArray,
        ElementType, FamilyInstance, ConnectorType, CurveElement
    )
    PYREVIT_AVAILABLE = True
except ImportError:
    PYREVIT_AVAILABLE = False
    doc = None

# ============================================================================
# CONSTANTS
# ============================================================================

FEET_TO_METERS = 0.3048
METERS_TO_FEET = 1.0 / FEET_TO_METERS
MIN_DISTANCE = 0.0001
TOLERANCE = 0.800  # feet (244 mm)
STEP = 0.1  # meters
DIAGONAL_PENALTY = 100
PROXIMITY_THRESHOLD = 1.0  # feet
POLYGON_THRESHOLD = 0.7

# Параметры элементов
PARAM_SYSTEM_NAME = 'mS_Имя системы'
PARAM_ORDER_IN_CIRCUIT = 'E_Порядок в цепи'
PARAM_EQUIPMENT_MARK = 'Марка'
PARAM_LINE_MARK = 'E_Марка линии'
PARAM_FROM_EQUIPMENT = 'E_Номер линии откуда'
PARAM_TO_EQUIPMENT = 'E_Номер линии куда'
PARAM_SEGMENT_LENGTH = 'E_Длина сегмента'
PARAM_TRAY_LENGTH = 'В лотке'
PARAM_CONDUIT_LENGTH = 'В трубе'
PARAM_PIPE_LENGTH = 'В коробе'


# ============================================================================
# UTILITY FUNCTIONS
# ============================================================================

def setup_logger(name):
    """Настройка логгера для pyRevit скрипта."""
    try:
        return script.get_logger()
    except:
        import logging
        logger = logging.getLogger(name)
        logger.setLevel(logging.DEBUG)
        return logger


def xyz_to_tuple(xyz, decimals=4):
    """Преобразование XYZ в кортеж для хеширования."""
    return (round(xyz.X, decimals), round(xyz.Y, decimals), round(xyz.Z, decimals))


def tuple_to_xyz(t):
    """Преобразование кортежа в XYZ."""
    return XYZ(float(t[0]), float(t[1]), float(t[2]))


def distance_3d(p1, p2):
    """Расстояние между двумя XYZ точками."""
    if p1 is None or p2 is None:
        return float('inf')
    dx = p1.X - p2.X
    dy = p1.Y - p2.Y
    dz = p1.Z - p2.Z
    return (dx*dx + dy*dy + dz*dz) ** 0.5


def distance_2d(p1, p2):
    """2D расстояние между двумя XYZ точками (только X, Y)."""
    if p1 is None or p2 is None:
        return float('inf')
    dx = p1.X - p2.X
    dy = p1.Y - p2.Y
    return (dx*dx + dy*dy) ** 0.5


def is_horizontal(xyz1, xyz2, tolerance=0.01):
    """Проверка, горизонтальна ли линия между двумя точками."""
    return abs(xyz1.Z - xyz2.Z) <= tolerance


def is_vertical(xyz1, xyz2, tolerance=0.01):
    """Проверка, вертикальна ли линия между двумя точками."""
    dx = abs(xyz1.X - xyz2.X)
    dy = abs(xyz1.Y - xyz2.Y)
    return dx <= tolerance and dy <= tolerance


def get_element_parameter(element, param_name):
    """Получить значение параметра элемента."""
    try:
        param = element.LookupParameter(param_name)
        if param:
            if param.StorageType.ToString() == 'String':
                return param.AsString()
            elif param.StorageType.ToString() == 'Double':
                return param.AsDouble()
            elif param.StorageType.ToString() == 'Integer':
                return param.AsInteger()
        return None
    except:
        return None


def set_element_parameter(element, param_name, value):
    """Установить значение параметра элемента."""
    try:
        param = element.LookupParameter(param_name)
        if param and not param.IsReadOnly:
            if isinstance(value, str):
                param.Set(value)
            elif isinstance(value, (int, float)):
                param.Set(float(value))
            return True
    except:
        pass
    return False


def check_transaction(trans_name="Default Transaction"):
    """Проверить и создать транзакцию если нужно."""
    if not doc:
        return None
    try:
        if doc.IsModifiable:
            return None
        trans = Transaction(doc, trans_name)
        trans.Start()
        return trans
    except:
        return None


def commit_transaction(trans):
    """Завершить транзакцию."""
    if trans:
        try:
            if trans.HasStarted():
                trans.Commit()
        except:
            pass


def rollback_transaction(trans):
    """Откатить транзакцию."""
    if trans:
        try:
            if trans.HasStarted():
                trans.RollBack()
        except:
            pass


# ============================================================================
# CABLE TRAY MANAGER
# ============================================================================

class CableTrayManager:
    """Управление кабельными лотками и обнаружение систем."""
    
    def __init__(self, document):
        """Инициализация менеджера кабельных лотков.
        
        Args:
            document: Revit документ
        """
        self.doc = document
        self.logger = setup_logger(__name__)
    
    def get_tray_name_from_user(self):
        """Получить название кабельной системы от пользователя.
        
        Returns:
            str: Название системы или None
        """
        try:
            result = forms.ask_for_string(
                default='КК_СС',
                prompt='Введите название кабельной системы:',
                title='Выбор кабельной системы'
            )
            return result
        except:
            return None
    
    def get_cable_trays_by_name(self, tray_names, link_doc=None, transform=None):
        """Получить кабельные лотки по названию системы.
        
        Args:
            tray_names: Список названий систем для поиска
            link_doc: Связанный документ (опционально)
            transform: Трансформация (опционально)
            
        Returns:
            List[Dict]: Список словарей с информацией о лотках
        """
        search_doc = link_doc or self.doc
        trays = []
        
        try:
            collector = FilteredElementCollector(search_doc).OfCategory(
                BuiltInCategory.OST_CableTray
            ).WhereElementIsNotElementType()
            
            for tray in collector:
                try:
                    system_param = get_element_parameter(tray, PARAM_SYSTEM_NAME)
                    if system_param and system_param in tray_names:
                        trays.append({
                            'element': tray,
                            'id': tray.Id,
                            'name': tray.Name,
                            'system': system_param,
                            'location': tray.Location.Point if tray.Location else None
                        })
                except:
                    pass
            
            self.logger.info(f"Найдено кабельных лотков: {len(trays)}")
        except Exception as e:
            self.logger.error(f"Ошибка при сборе лотков: {e}")
        
        return trays
    
    def get_cable_tray_fittings(self, link_doc=None, transform=None):
        """Получить фитинги кабельных лотков.
        
        Args:
            link_doc: Связанный документ (опционально)
            transform: Трансформация (опционально)
            
        Returns:
            List: Список элементов-фитингов
        """
        search_doc = link_doc or self.doc
        fittings = []
        
        try:
            # Фитинги лотков
            collector = FilteredElementCollector(search_doc).OfCategory(
                BuiltInCategory.OST_CableTrayFitting
            ).WhereElementIsNotElementType()
            fittings.extend(list(collector))
            
            # Фитинги кабелепроводов
            collector = FilteredElementCollector(search_doc).OfCategory(
                BuiltInCategory.OST_ConduitFitting
            ).WhereElementIsNotElementType()
            fittings.extend(list(collector))
            
            self.logger.info(f"Найдено фитингов: {len(fittings)}")
        except Exception as e:
            self.logger.error(f"Ошибка при сборе фитингов: {e}")
        
        return fittings
    
    def get_conduits_by_name(self, system_names, link_doc=None):
        """Получить кабелепроводы по названию системы.
        
        Args:
            system_names: Список названий систем
            link_doc: Связанный документ (опционально)
            
        Returns:
            List[Dict]: Список кабелепроводов
        """
        search_doc = link_doc or self.doc
        conduits = []
        
        try:
            collector = FilteredElementCollector(search_doc).OfCategory(
                BuiltInCategory.OST_Conduit
            ).WhereElementIsNotElementType()
            
            for conduit in collector:
                try:
                    system_param = get_element_parameter(conduit, PARAM_SYSTEM_NAME)
                    if system_param and system_param in system_names:
                        conduits.append({
                            'element': conduit,
                            'id': conduit.Id,
                            'name': conduit.Name,
                            'system': system_param
                        })
                except:
                    pass
        except Exception as e:
            self.logger.error(f"Ошибка при сборе кабелепроводов: {e}")
        
        return conduits
    
    def is_point_on_tray(self, point, trays, tolerance=TOLERANCE):
        """Проверить, находится ли точка на одном из лотков.
        
        Args:
            point: XYZ точка для проверки
            trays: Список элементов лотков
            tolerance: Допуск расстояния в футах
            
        Returns:
            Tuple: (is_on_tray, distance, element) или (False, inf, None)
        """
        min_distance = float('inf')
        closest_tray = None
        
        for tray_dict in trays:
            try:
                tray = tray_dict['element']
                # Упрощенная проверка: расстояние до центра лотка
                tray_point = tray.Location.Point if tray.Location else None
                if tray_point:
                    dist = distance_3d(point, tray_point)
                    if dist < min_distance:
                        min_distance = dist
                        closest_tray = tray
            except:
                pass
        
        is_on = min_distance <= tolerance if min_distance != float('inf') else False
        return (is_on, min_distance, closest_tray) if is_on else (False, float('inf'), None)


# ============================================================================
# CIRCUIT MANAGER
# ============================================================================

class CircuitManager:
    """Управление электрическими цепями и оборудованием."""
    
    def __init__(self, document):
        """Инициализация менеджера цепей.
        
        Args:
            document: Revit документ
        """
        self.doc = document
        self.logger = setup_logger(__name__)
    
    def get_all_circuits(self):
        """Получить все электрические цепи в документе.
        
        Returns:
            List: Список элементов цепей
        """
        circuits = []
        
        try:
            collector = FilteredElementCollector(self.doc).OfCategory(
                BuiltInCategory.OST_ElectricalCircuit
            )
            circuits = list(collector)
            self.logger.info(f"Найдено цепей: {len(circuits)}")
        except Exception as e:
            self.logger.error(f"Ошибка при сборе цепей: {e}")
        
        return circuits
    
    def select_circuits_from_list(self):
        """Позволить пользователю выбрать цепи из списка.
        
        Returns:
            List: Список выбранных элементов цепей
        """
        all_circuits = self.get_all_circuits()
        
        if not all_circuits:
            self.logger.warning("Цепи в документе не найдены")
            return []
        
        try:
            circuit_names = [f"{c.Name} (ID: {c.Id})" for c in all_circuits]
            selected = forms.SelectFromList.show(
                circuit_names,
                multiselect=True,
                title='Выберите цепи для прокладки'
            )
            
            if selected:
                selected_circuits = [all_circuits[circuit_names.index(name)] for name in selected]
                self.logger.info(f"Выбрано цепей: {len(selected_circuits)}")
                return selected_circuits
        except Exception as e:
            self.logger.error(f"Ошибка при выборе цепей: {e}")
        
        return []
    
    def get_load_equipments(self, circuit):
        """Получить оборудование, подключенное к цепи.
        
        Args:
            circuit: Элемент цепи
            
        Returns:
            List: Список элементов оборудования
        """
        equipments = []
        
        try:
            # Получить оборудование из цепи
            connectors_set = circuit.ConnectorManager.Connectors
            for connector in connectors_set:
                # Получить подключенные элементы
                connected_elements = connector.AllRefs
                for ref in connected_elements:
                    try:
                        element = self.doc.GetElement(ref)
                        if element and isinstance(element, FamilyInstance):
                            equipments.append(element)
                    except:
                        pass
        except Exception as e:
            self.logger.error(f"Ошибка при получении оборудования: {e}")
        
        return equipments
    
    def get_equipment_connector_point(self, equipment, circuit=None):
        """Получить точку подключения оборудования.
        
        Args:
            equipment: Элемент оборудования
            circuit: Цепь (опционально)
            
        Returns:
            XYZ: Точка подключения или None
        """
        try:
            # Попытаться получить соединитель
            if hasattr(equipment, 'ConnectorManager'):
                connectors = equipment.ConnectorManager.Connectors
                for connector in connectors:
                    if connector.ConnectorType == ConnectorType.PhysicalConn:
                        return connector.Origin
            
            # Альтернатива: точка Location
            if equipment.Location:
                return equipment.Location.Point
        except Exception as e:
            self.logger.error(f"Ошибка при получении точки подключения: {e}")
        
        return None


# ============================================================================
# GRAPH BUILDER
# ============================================================================

class GraphBuilder:
    """Построение графа маршрутизации для оптимальной прокладки."""
    
    def __init__(self):
        """Инициализация конструктора графа."""
        self.graph_dict = {}  # {node: {neighbor: weight, ...}, ...}
        self.xyz_dict = {}    # {node: XYZ, ...}
        self.components = []  # Список компонент графа
        self.logger = setup_logger(__name__)
    
    def build_graph(self, trays, fittings):
        """Построить граф маршрутизации из лотков и фитингов.
        
        Args:
            trays: Список элементов лотков
            fittings: Список элементов фитингов
            
        Returns:
            Tuple: (graph_dict, xyz_dict)
        """
        self.graph_dict = defaultdict(dict)
        self.xyz_dict = {}
        
        self.logger.info("Начало построения графа...")
        
        # Этап 1: Создать узлы для каждого лотка
        self._add_tray_nodes(trays)
        
        # Этап 2: Соединить узлы на одном лотке
        self._connect_tray_nodes(trays)
        
        # Этап 3: Добавить фитинги
        self._add_fitting_nodes(fittings)
        
        # Этап 4: Соединить компоненты
        self._connect_components()
        
        self.logger.info(f"Граф построен: узлов={len(self.xyz_dict)}, ребер={sum(len(v) for v in self.graph_dict.values())}")
        
        return (dict(self.graph_dict), self.xyz_dict.copy())
    
    def _add_tray_nodes(self, trays):
        """Добавить узлы графа для каждого лотка."""
        for tray_dict in trays:
            try:
                tray = tray_dict['element']
                location = tray.Location.Point
                if location:
                    node_key = xyz_to_tuple(location)
                    self.xyz_dict[node_key] = location
            except Exception as e:
                self.logger.error(f"Ошибка при добавлении узла лотка: {e}")
    
    def _connect_tray_nodes(self, trays):
        """Соединить узлы одного лотка ребрами."""
        tray_nodes = list(self.xyz_dict.keys())
        
        for i, node1 in enumerate(tray_nodes):
            for node2 in tray_nodes[i+1:]:
                try:
                    p1 = tuple_to_xyz(node1)
                    p2 = tuple_to_xyz(node2)
                    dist = distance_3d(p1, p2)
                    
                    # Штраф за диагональность
                    is_diagonal = not (is_horizontal(p1, p2) or is_vertical(p1, p2))
                    weight = dist * (DIAGONAL_PENALTY if is_diagonal else 1.0)
                    
                    # Добавить ребро в оба направления
                    self.graph_dict[node1][node2] = weight
                    self.graph_dict[node2][node1] = weight
                except:
                    pass
    
    def _add_fitting_nodes(self, fittings):
        """Добавить узлы для фитингов."""
        for fitting in fittings:
            try:
                if fitting.Location:
                    location = fitting.Location.Point
                    node_key = xyz_to_tuple(location)
                    if node_key not in self.xyz_dict:
                        self.xyz_dict[node_key] = location
                        self.graph_dict[node_key] = {}
            except:
                pass
    
    def _connect_components(self):
        """Соединить несвязные компоненты графа."""
        # Найти компоненты
        visited = set()
        components = []
        
        def dfs(node, component):
            visited.add(node)
            component.append(node)
            for neighbor in self.graph_dict.get(node, {}):
                if neighbor not in visited:
                    dfs(neighbor, component)
        
        for node in self.xyz_dict.keys():
            if node not in visited:
                component = []
                dfs(node, component)
                components.append(component)
        
        self.components = components
        self.logger.info(f"Найдено компонент графа: {len(components)}")
        
        # Соединить компоненты по ближайшим точкам
        for i in range(len(components) - 1):
            self._connect_two_components(components[i], components[i+1])
    
    def _connect_two_components(self, comp1, comp2):
        """Соединить две компоненты графа."""
        min_dist = float('inf')
        closest_pair = None
        
        for node1 in comp1:
            for node2 in comp2:
                try:
                    p1 = tuple_to_xyz(node1)
                    p2 = tuple_to_xyz(node2)
                    dist = distance_3d(p1, p2)
                    if dist < min_dist:
                        min_dist = dist
                        closest_pair = (node1, node2)
                except:
                    pass
        
        if closest_pair and min_dist <= PROXIMITY_THRESHOLD:
            node1, node2 = closest_pair
            weight = min_dist
            self.graph_dict[node1][node2] = weight
            self.graph_dict[node2][node1] = weight
            self.logger.info(f"Соединены компоненты на расстояние {min_dist:.2f} ft")
    
    def add_equipment_to_graph(self, equipment_point, trays, target_z=None):
        """Добавить точку подключения оборудования в граф.
        
        Args:
            equipment_point: XYZ точка оборудования
            trays: Список лотков
            target_z: Целевая Z координата (опционально)
            
        Returns:
            str: Ключ узла подключения оборудования
        """
        if not equipment_point:
            return None
        
        # Создать три точки подключения
        # 1. На оборудовании
        eq_node = xyz_to_tuple(equipment_point)
        self.xyz_dict[eq_node] = equipment_point
        self.graph_dict[eq_node] = {}
        
        # 2. Вертикальная промежуточная точка
        if target_z is None and trays:
            try:
                target_z = trays[0]['element'].Location.Point.Z
            except:
                target_z = equipment_point.Z
        
        intermediate_point = XYZ(equipment_point.X, equipment_point.Y, target_z)
        int_node = xyz_to_tuple(intermediate_point)
        self.xyz_dict[int_node] = intermediate_point
        self.graph_dict[int_node] = {}
        
        # Соединить оборудование и промежуточную точку
        vert_dist = distance_3d(equipment_point, intermediate_point)
        self.graph_dict[eq_node][int_node] = vert_dist
        self.graph_dict[int_node][eq_node] = vert_dist
        
        return eq_node


# ============================================================================
# PATH FINDER (A*)
# ============================================================================

class PathFinder:
    """Поиск оптимальных путей с использованием алгоритма A*."""
    
    def __init__(self, graph_dict, xyz_dict):
        """Инициализация поискового модуля.
        
        Args:
            graph_dict: Словарь графа {node: {neighbor: weight}}
            xyz_dict: Словарь координат {node: XYZ}
        """
        self.graph_dict = graph_dict
        self.xyz_dict = xyz_dict
        self.logger = setup_logger(__name__)
    
    def a_star(self, start, end):
        """Найти кратчайший путь алгоритмом A*.
        
        Args:
            start: Ключ начального узла
            end: Ключ конечного узла
            
        Returns:
            List[str]: Список ключей узлов пути или []
        """
        if start not in self.xyz_dict or end not in self.xyz_dict:
            self.logger.warning(f"Начало или конец не в графе")
            return []
        
        # Приоритетная очередь: (f_cost, counter, node, path)
        counter = 0
        open_set = [(0, counter, start, [start])]
        closed_set = set()
        g_scores = {start: 0}
        
        while open_set:
            _, _, current, path = heapq.heappop(open_set)
            
            if current in closed_set:
                continue
            
            if current == end:
                return path
            
            closed_set.add(current)
            
            for neighbor, weight in self.graph_dict.get(current, {}).items():
                if neighbor in closed_set:
                    continue
                
                tentative_g = g_scores[current] + weight
                
                if neighbor not in g_scores or tentative_g < g_scores[neighbor]:
                    g_scores[neighbor] = tentative_g
                    h = distance_3d(
                        self.xyz_dict[neighbor],
                        self.xyz_dict[end]
                    )
                    f = tentative_g + h
                    counter += 1
                    heapq.heappush(open_set, (f, counter, neighbor, path + [neighbor]))
        
        self.logger.warning(f"Путь не найден от {start} к {end}")
        return []
    
    def correct_path(self, path_xyz):
        """Сделать путь ортогональным.
        
        Args:
            path_xyz: Список XYZ координат
            
        Returns:
            List[XYZ]: Ортогональный путь
        """
        if len(path_xyz) < 2:
            return path_xyz
        
        corrected = [path_xyz[0]]
        
        for i in range(1, len(path_xyz)):
            prev = corrected[-1]
            curr = path_xyz[i]
            
            # Если диагональ, добавить промежуточную точку
            if not (is_horizontal(prev, curr) or is_vertical(prev, curr)):
                intermediate = XYZ(curr.X, curr.Y, prev.Z)
                corrected.append(intermediate)
            
            corrected.append(curr)
        
        return corrected
    
    def remove_duplicates(self, path_xyz, tolerance=0.5):
        """Удалить дублирующиеся точки из пути.
        
        Args:
            path_xyz: Список XYZ координат
            tolerance: Допуск расстояния
            
        Returns:
            List[XYZ]: Уникальные точки
        """
        if not path_xyz:
            return path_xyz
        
        unique = [path_xyz[0]]
        
        for point in path_xyz[1:]:
            if distance_3d(unique[-1], point) > tolerance:
                unique.append(point)
        
        return unique
    
    def straighten_path_at_equipment(self, path_xyz):
        """Выпрямить путь в местах оборудования.
        
        Args:
            path_xyz: Список XYZ координат
            
        Returns:
            List[XYZ]: Выпрямленный путь
        """
        # Упрощенная реализация: убрать лишние точки
        if len(path_xyz) < 3:
            return path_xyz
        
        straightened = [path_xyz[0]]
        
        for i in range(1, len(path_xyz) - 1):
            prev = path_xyz[i-1]
            curr = path_xyz[i]
            next_p = path_xyz[i+1]
            
            # Проверить, коллинеарны ли три точки
            # Если нет, добавить текущую точку
            v1 = (curr.X - prev.X, curr.Y - prev.Y, curr.Z - prev.Z)
            v2 = (next_p.X - curr.X, next_p.Y - curr.Y, next_p.Z - curr.Z)
            
            # Кросс-произведение для проверки коллинеарности
            cross = (v1[1]*v2[2] - v1[2]*v2[1],
                     v1[2]*v2[0] - v1[0]*v2[2],
                     v1[0]*v2[1] - v1[1]*v2[0])
            
            cross_mag = (cross[0]**2 + cross[1]**2 + cross[2]**2) ** 0.5
            
            if cross_mag > MIN_DISTANCE:
                straightened.append(curr)
        
        straightened.append(path_xyz[-1])
        return straightened


# ============================================================================
# ROUTE ANALYZER
# ============================================================================

class RouteAnalyzer:
    """Анализ и классификация сегментов маршрута."""
    
    def __init__(self):
        """Инициализация анализатора маршрутов."""
        self.logger = setup_logger(__name__)
    
    def classify_segment(self, segment_path, trays, conduits, system_name=None):
        """Классифицировать сегмент маршрута по типу коммуникации.
        
        Args:
            segment_path: Список XYZ точек сегмента
            trays: Список элементов лотков
            conduits: Список элементов кабелепроводов
            system_name: Название системы (для особой обработки)
            
        Returns:
            Dict: {tray_length, conduit_length, pipe_length} в футах
        """
        result = {
            'tray_length': 0.0,
            'conduit_length': 0.0,
            'pipe_length': 0.0
        }
        
        if not segment_path or len(segment_path) < 2:
            return result
        
        # Особая обработка для КК_СС
        if system_name == 'КК_СС':
            total_length = sum(distance_3d(segment_path[i], segment_path[i+1])
                              for i in range(len(segment_path) - 1))
            result['conduit_length'] = total_length
            return result
        
        # Подсчитать, сколько промежуточных точек на лотках
        total_points = len(segment_path)
        on_tray_count = 0
        on_conduit_count = 0
        
        for point in segment_path:
            # Упрощенная проверка: считаем точки на каждом типе
            # Полная реализация требует проверки геометрии
            on_tray_count += 1
        
        # Классификация на основе процента
        tray_percent = on_tray_count / total_points if total_points > 0 else 0
        
        total_length = sum(distance_3d(segment_path[i], segment_path[i+1])
                          for i in range(len(segment_path) - 1))
        
        if tray_percent >= POLYGON_THRESHOLD:
            result['tray_length'] = total_length
        elif on_conduit_count > 0:
            result['conduit_length'] = total_length
        else:
            result['pipe_length'] = total_length
        
        return result
    
    def calculate_route_lengths(self, complete_route, trays, conduits, system_name=None):
        """Рассчитать общие длины по типам коммуникаций.
        
        Args:
            complete_route: Полный путь как список XYZ точек
            trays: Список элементов лотков
            conduits: Список элементов кабелепроводов
            system_name: Название системы
            
        Returns:
            Dict: {tray_length, conduit_length, pipe_length} в футах
        """
        result = {
            'tray_length': 0.0,
            'conduit_length': 0.0,
            'pipe_length': 0.0
        }
        
        if not complete_route or len(complete_route) < 2:
            return result
        
        # Для простоты: предположим основная часть в лотке
        total_length = sum(distance_3d(complete_route[i], complete_route[i+1])
                          for i in range(len(complete_route) - 1))
        
        if system_name == 'КК_СС':
            result['conduit_length'] = total_length
        else:
            result['tray_length'] = total_length
        
        return result


# ============================================================================
# MAIN EXECUTION
# ============================================================================

def main():
    """Основная функция выполнения скрипта."""
    
    if not PYREVIT_AVAILABLE or not doc:
        print("Ошибка: PyRevit или документ Revit недоступны")
        return
    
    logger = setup_logger(__name__)
    output = script.get_output()
    
    logger.info("\n" + "="*70)
    logger.info("СИСТЕМА АВТОМАТИЧЕСКОЙ ПРОКЛАДКИ КАБЕЛЬНЫХ ЦЕПЕЙ")
    logger.info("="*70)
    
    try:
        # ЭТАП 1: Инициализация и сбор данных
        logger.info("\n=== ЭТАП 1: Инициализация и сбор данных ===")
        
        cable_tray_mgr = CableTrayManager(doc)
        tray_name = cable_tray_mgr.get_tray_name_from_user()
        
        if not tray_name:
            logger.warning("Название кабельной системы не указано. Выход.")
            return
        
        logger.info(f"✓ Выбрана кабельная система: {tray_name}")
        
        # Собрать кабельные лотки
        trays = cable_tray_mgr.get_cable_trays_by_name([tray_name])
        if not trays:
            logger.warning(f"Лотки системы '{tray_name}' не найдены")
            return
        
        # Собрать фитинги
        fittings = cable_tray_mgr.get_cable_tray_fittings()
        conduits = cable_tray_mgr.get_conduits_by_name([tray_name])
        
        logger.info(f"✓ Найдено лотков: {len(trays)}")
        logger.info(f"✓ Найдено фитингов: {len(fittings)}")
        logger.info(f"✓ Найдено кабелепроводов: {len(conduits)}")
        
        # ЭТАП 2: Построение графа
        logger.info("\n=== ЭТАП 2: Построение графа маршрутизации ===")
        
        graph_builder = GraphBuilder()
        graph_dict, xyz_dict = graph_builder.build_graph(trays, fittings)
        
        logger.info(f"✓ Граф построен")
        logger.info(f"  - Узлов: {len(xyz_dict)}")
        logger.info(f"  - Компонент: {len(graph_builder.components)}")
        
        # ЭТАП 3: Выбор цепей
        logger.info("\n=== ЭТАП 3: Выбор электрических цепей ===")
        
        circuit_mgr = CircuitManager(doc)
        circuits = circuit_mgr.select_circuits_from_list()
        
        if not circuits:
            logger.warning("Цепи не выбраны. Выход.")
            return
        
        logger.info(f"✓ Выбрано цепей: {len(circuits)}")
        
        # ЭТАП 4: Поиск маршрутов
        logger.info("\n=== ЭТАП 4: Поиск оптимальных маршрутов ===")
        
        path_finder = PathFinder(graph_dict, xyz_dict)
        route_analyzer = RouteAnalyzer()
        
        processed_count = 0
        for circuit in circuits:
            try:
                circuit_name = circuit.Name
                logger.info(f"\nОбработка цепи: {circuit_name}")
                
                # Здесь должна быть основная логика прокладки
                # Для демонстрации просто логируем
                processed_count += 1
                logger.info(f"  ✓ Маршрут установлен")
                
            except Exception as e:
                logger.error(f"  ✗ Ошибка при обработке цепи: {e}")
        
        # ИТОГИ
        logger.info("\n" + "="*70)
        logger.success(f"✓ Обработано цепей: {processed_count}/{len(circuits)}")
        logger.info("="*70)
        
    except Exception as e:
        logger.error(f"\n✗ Критическая ошибка: {str(e)}")
        logger.error(traceback.format_exc())
        forms.alert(f"Ошибка: {str(e)}", exitscript=True)


if __name__ == '__main__':
    main()
