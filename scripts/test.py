#!/usr/bin/env python3
"""Discover the portable Python suite and fail rather than silently running zero tests."""
from pathlib import Path
import sys
import unittest

root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(root / 'python'))
suite = unittest.defaultTestLoader.discover(str(root / 'python_tests'))
if suite.countTestCases() == 0:
    raise SystemExit('No Python tests discovered: check the python_tests directory')
result = unittest.TextTestRunner(verbosity=2).run(suite)
raise SystemExit(0 if result.wasSuccessful() else 1)
