"""Unlock the pinned local JP library using an independently supplied ROM."""
import argparse
from pathlib import Path
import wafel

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('rom', type=Path)
args = p.parse_args()
runtime = Path(__file__).resolve().parents[2]/'build/wafel-pilot'
wafel.unlock_libsm64(str(runtime/'sm64_jp.dll.locked'), str(runtime/'sm64_jp.dll'), str(args.rom))
print('JP library unlocked locally; do not publish the library or ROM.')
