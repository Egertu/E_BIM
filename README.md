# E_BIM - Cable Routing Automation System

Automated cable circuit routing in Revit cable trays, conduits, and pipes for pyRevit.

## Technical Specifications

See inline documentation in `script.py`

## Features

- Automatic cable tray discovery in main and linked models
- Orthogonal graph construction for optimal routing
- A* pathfinding algorithm for shortest paths
- Route classification (tray, conduit, pipe)
- Equipment parameter updates
- Route persistence in pyRevit configuration

## Installation

1. Copy `script.py` to your pyRevit extension folder
2. Reload pyRevit
3. The script will appear in the E_BIM extension

## Constants

- `FEET_TO_METERS`: 0.3048
- `TOLERANCE`: 0.800 ft (244 mm)
- `STEP`: 0.1 m
- `DIAGONAL_PENALTY`: 100
- `PROXIMITY_THRESHOLD`: 1.0 ft
- `POLYGON_THRESHOLD`: 0.7
