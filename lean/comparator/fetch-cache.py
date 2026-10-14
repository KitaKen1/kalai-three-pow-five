#!/usr/bin/env python3
"""Fetch Mathlib cache only for the proof and trusted challenge import closures."""
from pathlib import Path
import json
import subprocess
import sys

root = Path(__file__).resolve().parents[2]
subprocess.run([sys.executable, str(root / 'lean/comparator/check-inputs.py')], check=True)
pins = json.loads((root / 'lean/comparator/pins.json').read_text())
imports = list(dict.fromkeys(pins['mathlib_imports'] + pins['challenge_imports']))
subprocess.run(['lake', 'exe', 'cache', 'get', *imports], cwd=root / 'lean', check=True)
