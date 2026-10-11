"""Locations shared by the verifier and manuscript generator."""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CERTIFICATES = ROOT / 'certificates'
EVIDENCE = ROOT / 'evidence'
