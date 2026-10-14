#!/usr/bin/env python3
"""Refresh package hashes after intentional edits, without upgrading proof status."""
from pathlib import Path
import hashlib
import importlib.util
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    spec = importlib.util.spec_from_file_location('kalai_inputs', ROOT / 'lean/comparator/check-inputs.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    pinfile = ROOT / 'lean/comparator/pins.json'
    pins = json.loads(pinfile.read_text())
    names = set(pins['files_sha256'])
    names.update(path.relative_to(ROOT).as_posix()
                 for path in (ROOT / 'lean/comparator').iterdir()
                 if path.is_file() and path.name != 'pins.json')
    for folder in ['lean', 'leanWithoutComparator', 'lean4web', 'FClikelean']:
        names.update(folder + '/' + name for name in
                     ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json'])
    names.update(['lean4web/source-map.json', 'lean/Kalai5/FormalConjectures.lean'])
    pins['proof_source_map_sha256'] = digest(ROOT / 'lean/comparator/proof-source-map.json')
    pins['files_sha256'] = {name: digest(ROOT / name) for name in sorted(names)}
    pinfile.write_text(json.dumps(pins, indent=2) + '\n')
    manifest_path = ROOT / 'PUBLICATION-MANIFEST.json'
    manifest = json.loads(manifest_path.read_text())
    manifest['files_sha256'] = {name: digest(ROOT / name) for name in sorted(module.tracked_inputs())}
    manifest_path.write_text(json.dumps(manifest, indent=2) + '\n')
    subprocess.run([sys.executable, str(ROOT / 'lean/comparator/check-inputs.py')], check=True)
    print('Hashes refreshed; proof and CI status were not upgraded.')


if __name__ == '__main__':
    main()
