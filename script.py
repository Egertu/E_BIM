#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""
E_BIM Cable Routing Automation System
Automated electrical circuit routing in Revit cable trays, conduits, and pipes.

Вся функциональность интегрирована в один файл для использования в pyRevit.

Техническое задание:
1. Находить кабельные системы по названию В ОСНОВНОЙ И СВЯЗАННЫХ МОДЕЛЯХ
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
        ElementType, FamilyInstance, ConnectorType, CurveElement,
        RevitLinkInstance
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


def get_all_linked_documents(main_doc):
    """Получить все связанные документы.
    
    Args:
        main_doc: Основной документ Revit
        
    Returns:
        List: Список кортежей (linked_doc, linked_instance, transform)
    """
    linked_docs = []
    
    try:
        # Получить все RevitLinkInstance в документе
        collector = FilteredElementCollector(main_doc).OfClass(RevitLinkInstance)
        
        for link_instance in collector:
            try:
                linked_doc = link_instance.GetLinkDocument()
                if linked_doc and not linked_doc.IsLinked:
                    # Получить трансформацию связи
                    transform = link_instance.GetTotalTransform()
                    linked_docs.append({
                        'doc': linked_doc,
                        'instance': link_instance,
                        'transform': transform,
                        'name': link_instance.Name
                    })
            except:
                pass
    except Exception as e:
        print(f"Ошибка при получении связанных документов: {e}")
    
    return linked_docs


def apply_transform_to_point(point, transform):
    """Применить трансформацию к точке.
    
    Args:
        point: XYZ точка
        transform: Transform объект
        
    Returns:
        XYZ: Трансформированная точка
    """
    if point is None or transform is None:
        return point
    try:
        return transform.OfPoint(point)
    except:
        return point


# ============================================================================
# CABLE TRAY MANAGER - WITH LINKED MODELS SUPPORT & DIAGNOSTICS
# ============================================================================

class CableTrayManager:
    """Управление кабельными лотками и обнаружение систем. ПОДДЕРЖКА СВЯЗАННЫХ МОДЕЛЕЙ."""
    
    def __init__(self, document):
        """Инициализация менеджера кабельных лотков.
        
        Args:
            document: Revit документ
        """
        self.doc = document
        self.logger = setup_logger(__name__)
        self.linked_docs = []
    
    def get_available_cable_systems(self, link_doc_info=None):
        """Получить список доступных кабельных систем в модели.
        
        Args:
            link_doc_info: Информация о связанной модели (опционально)
            
        Returns:
            List[str]: Список найденных названий систем
        """
        systems = set()
        
        # Поиск в основной модели
        try:
            collector = FilteredElementCollector(self.doc).OfCategory(
                BuiltInCategory.OST_CableTray
            ).WhereElementIsNotElementType()
            
            for tray in collector:
                try:
                    system = get_element_parameter(tray, PARAM_SYSTEM_NAME)
                    if system:
                        systems.add(system)
                except:
                    pass
        except:
            pass
        
        # Поиск в связанной модели
        if link_doc_info:
            try:
                collector = FilteredElementCollector(link_doc_info['doc']).OfCategory(
                    BuiltInCategory.OST_CableTray
                ).WhereElementIsNotElementType()
                
                for tray in collector:
                    try:
                        system = get_element_parameter(tray, PARAM_SYSTEM_NAME)
                        if system:
                            systems.add(system)
                    except:
                        pass
            except:
                pass
        
        return sorted(list(systems))
    
    def select_linked_model(self):
        """Позволить пользователю выбрать связанный документ для поиска.
        
        Returns:
            Dict: Выбранный связанный документ или None
        """
        linked_docs = get_all_linked_documents(self.doc)
        
        if not linked_docs:
            self.logger.info("Связанные модели не найдены. Будет использована основная модель.")
            return None
        
        try:
            link_names = [f"{link['name']}" for link in linked_docs]
            link_names.insert(0, "Только основная модель")
            
            selected = forms.ask_for_one_item(
                link_names,
                default=link_names[0],
                prompt="Выберите модель для поиска кабельных лотков:",
                title="Выбор модели"
            )
            
            if selected == "Только основная модель":
                return None
            
            for link_doc in linked_docs:
                if link_doc['name'] == selected:
                    return link_doc
        except:
            pass
        
        return None
    
    def select_cable_system(self, link_doc_info=None):
        """Позволить пользователю выбрать кабельную систему из доступных.
        
        Args:
            link_doc_info: Информация о связанной модели (опционально)
            
        Returns:
            str: Название выбранной системы или None
        """
        available_systems = self.get_available_cable_systems(link_doc_info)
        
        if not available_systems:
            self.logger.error("В моделях не найдены кабельные лотки с параметром 'mS_Имя системы'")
            return None
        
        self.logger.info(f"Доступные кабельные системы: {available_systems}")
        
        try:
            selected = forms.ask_for_one_item(
                available_systems,
                default=available_systems[0] if available_systems else None,
                prompt="Выберите кабельную систему:",
                title="Выбор кабельной системы"
            )
            return selected
        except:
            return None
    
    def get_tray_name_from_user(self, link_doc_info=None):
        """Получить название кабельной системы от пользователя.
        
        Args:
            link_doc_info: Информация о связанной модели (опционально)
        
        Returns:
            str: Название системы или None
        """
        # Сначала попробуем показать доступные системы
        available_systems = self.get_available_cable_systems(link_doc_info)
        
        if available_systems:
            self.logger.info(f"\nНайденные системы: {', '.join(available_systems)}")
            selected = self.select_cable_system(link_doc_info)
            if selected:
                return selected
        
        # Если не выбрал из списка, попросить вручную ввести
        try:
            result = forms.ask_for_string(
                default='КНС_СС',
                prompt='Введите название кабельной системы:',
                title='Выбор кабельной системы'
            )
            return result
        except:
            return None
    
    def get_cable_trays_by_name(self, tray_names, link_doc_info=None):
        """Получить кабельные лотки по названию системы.
        ПОИСК В ОСНОВНОЙ МОДЕЛИ И ВЫБРАННОЙ СВЯЗАННОЙ МОДЕЛИ.
        
        Args:
            tray_names: Список названий систем для поиска
            link_doc_info: Информация о связанной модели (опционально)
            
        Returns:
            List[Dict]: Список словарей с информацией о лотках
        """
        all_trays = []
        
        # Поиск в основной модели
        self.logger.info("Поиск лотков в основной модели...")
        main_trays = self._search_trays_in_doc(self.doc, tray_names, None, None)
        all_trays.extend(main_trays)
        self.logger.info(f"  → Найдено в основной модели: {len(main_trays)}")
        
        # Поиск в связанной модели (если выбрана)
        if link_doc_info:
            try:
                self.logger.info(f"Поиск лотков в связанной модели: {link_doc_info['name']}...")
                linked_trays = self._search_trays_in_doc(
                    link_doc_info['doc'],
                    tray_names,
                    link_doc_info['transform'],
                    link_doc_info['instance']
                )
                all_trays.extend(linked_trays)
                self.logger.info(f"  → Найдено в связанной модели: {len(linked_trays)}")
            except Exception as e:
                self.logger.error(f"Ошибка при поиске в связанной модели: {e}")
        
        return all_trays
    
    def _search_trays_in_doc(self, search_doc, tray_names, transform=None, link_instance=None):
        """Внутренняя функция поиска лотков в документе.
        
        Args:
            search_doc: Документ для поиска
            tray_names: Список названий систем
            transform: Трансформация (для связанных моделей)
            link_instance: Объект связи
            
        Returns:
            List[Dict]: Найденные лотки
        """
        trays = []
        
        try:
            # Получить ВСЕ лотки для диагностики
            collector = FilteredElementCollector(search_doc).OfCategory(
                BuiltInCategory.OST_CableTray
            ).WhereElementIsNotElementType()
            
            all_trays_count = collector.GetElementCount()
            self.logger.info(f"    Всего лотков в документе: {all_trays_count}")
            
            # Собрать все системы для отладки
            all_systems_in_doc = set()
            
            for tray in collector:
                try:
                    system_param = get_element_parameter(tray, PARAM_SYSTEM_NAME)
                    
                    # Добавить в список всех систем для диагностики
                    if system_param:
                        all_systems_in_doc.add(system_param)
                        self.logger.info(f"    Найден лоток: {tray.Name}, система: '{system_param}'")
                    else:
                        self.logger.info(f"    Лоток '{tray.Name}' без параметра 'mS_Имя системы'")
                    
                    # Проверить, входит ли в искомые
                    if system_param and system_param in tray_names:
                        location = tray.Location.Point if tray.Location else None
                        
                        # Применить трансформацию если это связанная модель
                        if transform and location:
                            location = apply_transform_to_point(location, transform)
                        
                        trays.append({
                            'element': tray,
                            'id': tray.Id,
                            'name': tray.Name,
                            'system': system_param,
                            'location': location,
                            'from_linked': link_instance is not None,
                            'linked_instance': link_instance,
                            'transform': transform
                        })
                except Exception as e:
                    self.logger.error(f"    Ошибка при обработке лотка: {e}")
            
            if all_systems_in_doc:
                self.logger.info(f"    Доступные системы: {sorted(list(all_systems_in_doc))}")
            
        except Exception as e:
            self.logger.error(f"Ошибка при сборе лотков: {e}")
        
        return trays
    
    def get_cable_tray_fittings(self, link_doc_info=None):
        """Получить фитинги кабельных лотков.
        ПОИСК В ОСНОВНОЙ И СВЯЗАННОЙ МОДЕЛЯХ.
        
        Args:
            link_doc_info: Информация о связанной модели (опционально)
            
        Returns:
            List: Список элементов-фитингов
        """
        all_fittings = []
        
        # Фитинги из основной модели
        self.logger.info("Поиск фитингов в основной модели...")
        main_fittings = self._search_fittings_in_doc(self.doc, None, None)
        all_fittings.extend(main_fittings)
        self.logger.info(f"  → Найдено в основной модели: {len(main_fittings)}")
        
        # Фитинги из связанной модели (если выбрана)
        if link_doc_info:
            try:
                self.logger.info(f"Поиск фитингов в связанной модели: {link_doc_info['name']}...")
                linked_fittings = self._search_fittings_in_doc(
                    link_doc_info['doc'],
                    link_doc_info['transform'],
                    link_doc_info['instance']
                )
                all_fittings.extend(linked_fittings)
                self.logger.info(f"  → Найдено в связанной модели: {len(linked_fittings)}")
            except Exception as e:
                self.logger.error(f"Ошибка при поиске фитингов в связанной модели: {e}")
        
        return all_fittings
    
    def _search_fittings_in_doc(self, search_doc, transform=None, link_instance=None):
        """Внутренняя функция поиска фитингов в документе."""
        fittings = []
        
        try:
            # Фитинги лотков
            collector = FilteredElementCollector(search_doc).OfCategory(
                BuiltInCategory.OST_CableTrayFitting
            ).WhereElementIsNotElementType()
            
            tray_fitting_count = collector.GetElementCount()
            self.logger.info(f"    Фитингов лотков: {tray_fitting_count}")
            
            for fitting in collector:
                try:
                    location = fitting.Location.Point if fitting.Location else None
                    if transform and location:
                        location = apply_transform_to_point(location, transform)
                    
                    fittings.append({
                        'element': fitting,
                        'id': fitting.Id,
                        'location': location,
                        'from_linked': link_instance is not None,
                        'transform': transform
                    })
                except:
                    pass
            
            # Фитинги кабелепроводов
            collector = FilteredElementCollector(search_doc).OfCategory(
                BuiltInCategory.OST_ConduitFitting
            ).WhereElementIsNotElementType()
            
            conduit_fitting_count = collector.GetElementCount()
            self.logger.info(f"    Фитингов кабелепроводов: {conduit_fitting_count}")
            
            for fitting in collector:
                try:
                    location = fitting.Location.Point if fitting.Location else None
                    if transform and location:
                        location = apply_transform_to_point(location, transform)
                    
                    fittings.append({
                        'element': fitting,
                        'id': fitting.Id,
                        'location': location,
                        'from_linked': link_instance is not None,
                        'transform': transform
                    })
                except:
                    pass
        except Exception as e:
            self.logger.error(f"Ошибка при сборе фитингов: {e}")
        
        return fittings
    
    def get_conduits_by_name(self, system_names, link_doc_info=None):
        """Получить кабелепроводы по названию системы."""
        all_conduits = []
        
        # Поиск в основной модели
        self.logger.info("Поиск кабелепроводов в основной модели...")
        main_conduits = self._search_conduits_in_doc(self.doc, system_names, None, None)
        all_conduits.extend(main_conduits)
        self.logger.info(f"  → Найдено в основной модели: {len(main_conduits)}")
        
        # Поиск в связанной модели (если выбрана)
        if link_doc_info:
            try:
                self.logger.info(f"Поиск кабелепроводов в связанной модели: {link_doc_info['name']}...")
                linked_conduits = self._search_conduits_in_doc(
                    link_doc_info['doc'],
                    system_names,
                    link_doc_info['transform'],
                    link_doc_info['instance']
                )
                all_conduits.extend(linked_conduits)
                self.logger.info(f"  → Найдено в связанной модели: {len(linked_conduits)}")
            except Exception as e:
                self.logger.error(f"Ошибка при поиске кабелепроводов в связанной модели: {e}")
        
        return all_conduits
    
    def _search_conduits_in_doc(self, search_doc, system_names, transform=None, link_instance=None):
        """Внутренняя функция поиска кабелепроводов в документе."""
        conduits = []
        
        try:
            collector = FilteredElementCollector(search_doc).OfCategory(
                BuiltInCategory.OST_Conduit
            ).WhereElementIsNotElementType()
            
            for conduit in collector:
                try:
                    system_param = get_element_parameter(conduit, PARAM_SYSTEM_NAME)
                    if system_param and system_param in system_names:
                        location = conduit.Location.Point if conduit.Location else None
                        if transform and location:
                            location = apply_transform_to_point(location, transform)
                        
                        conduits.append({
                            'element': conduit,
                            'id': conduit.Id,
                            'name': conduit.Name,
                            'system': system_param,
                            'location': location,
                            'from_linked': link_instance is not None,
                            'transform': transform
                        })
                except:
                    pass
        except Exception as e:
            self.logger.error(f"Ошибка при сборе кабелепроводов: {e}")
        
        return conduits
    
    def is_point_on_tray(self, point, trays, tolerance=TOLERANCE):
        """Проверить, находится ли точка на одном из лотков."""
        min_distance = float('inf')
        closest_tray = None
        
        for tray_dict in trays:
            try:
                tray_point = tray_dict.get('location')
                if tray_point:
                    dist = distance_3d(point, tray_point)
                    if dist < min_distance:
                        min_distance = dist
                        closest_tray = tray_dict
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
        """Инициализация менеджера цепей."""
        self.doc = document
        self.logger = setup_logger(__name__)
    
    def get_all_circuits(self):
        """Получить все электрические цепи в документе."""
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
        """Позволить пользователю выбрать цепи из списка."""
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
    logger.info("С ПОДДЕРЖКОЙ ОСНОВНОЙ МОДЕЛИ И СВЯЗАННЫХ ФАЙЛОВ")
    logger.info("="*70)
    
    try:
        # ЭТАП 1: Инициализация и сбор данных
        logger.info("\n=== ЭТАП 1: Инициализация и сбор данных ===")
        
        cable_tray_mgr = CableTrayManager(doc)
        
        # Позволить выбрать связанную модель (опционально)
        link_doc_info = cable_tray_mgr.select_linked_model()
        if link_doc_info:
            logger.info(f"✓ Выбрана связанная модель: {link_doc_info['name']}")
        else:
            logger.info("✓ Будет использована основная модель")
        
        # Получить названию системы (с отладкой доступных систем)
        logger.info("\nПоиск доступных кабельных систем...")
        tray_name = cable_tray_mgr.get_tray_name_from_user(link_doc_info)
        
        if not tray_name:
            logger.warning("Название кабельной системы не указано. Выход.")
            return
        
        logger.info(f"✓ Выбрана кабельная система: '{tray_name}'")
        
        # Собрать кабельные лотки из основной и связанной моделей
        logger.info("\nПоиск кабельных лотков...")
        trays = cable_tray_mgr.get_cable_trays_by_name([tray_name], link_doc_info)
        if not trays:
            logger.error(f"✗ Лотки системы '{tray_name}' не найдены")
            logger.error("Проверьте:")
            logger.error("  1. Правильность названия системы (учитывается регистр)")
            logger.error("  2. Наличие параметра 'mS_Имя системы' у лотков")
            logger.error("  3. Выбрана ли правильная модель")
            return
        
        # Собрать фитинги
        logger.info("Поиск фитингов...")
        fittings = cable_tray_mgr.get_cable_tray_fittings(link_doc_info)
        
        # Собрать кабелепроводы
        logger.info("Поиск кабелепроводов...")
        conduits = cable_tray_mgr.get_conduits_by_name([tray_name], link_doc_info)
        
        logger.info(f"\n✓ ИТОГО НАЙДЕНО:")
        logger.info(f"  • Лотков: {len(trays)}")
        logger.info(f"  • Фитингов: {len(fittings)}")
        logger.info(f"  • Кабелепроводов: {len(conduits)}")
        
        # ЭТАП 3: Выбор цепей
        logger.info("\n=== ЭТАП 2: Выбор электрических цепей ===")
        
        circuit_mgr = CircuitManager(doc)
        circuits = circuit_mgr.select_circuits_from_list()
        
        if not circuits:
            logger.warning("Цепи не выбраны. Выход.")
            return
        
        logger.info(f"✓ Выбрано цепей: {len(circuits)}")
        
        # ИТОГИ
        logger.info("\n" + "="*70)
        logger.success(f"✓ Модель готова к маршрутизации")
        logger.success(f"  • Лотков: {len(trays)}")
        logger.success(f"  • Цепей для прокладки: {len(circuits)}")
        logger.info("="*70)
        
    except Exception as e:
        logger.error(f"\n✗ Критическая ошибка: {str(e)}")
        logger.error(traceback.format_exc())
        forms.alert(f"Ошибка: {str(e)}", exitscript=True)


if __name__ == '__main__':
    main()
