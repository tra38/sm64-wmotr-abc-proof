"""Unpack the pinned official Windows runtime into ignored build output.

No global Python installation, ROM download, or game-state setup is performed.
Pass archives downloaded from the URLs in README.md. Only the JP locked library
and Python 3.9 wheel are selected from Wafel's distribution.
"""
import hashlib
import io
from pathlib import Path
import zipfile

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'build/wafel-pilot'
ARCHIVES = {
    'wafel_0_8_5_win_x64.zip': 'c3552468f90819ee6c1c000014b2859898e2d6bed260324bf12ce45d0d42c219',
    'python-3.9.13-embed-amd64.zip': '938a1f3b80d580320836260612084d74ce094a261e36f9ff3ac7b9463df5f5e4',
}

def unpack(archive, destination):
    destination.mkdir(parents=True, exist_ok=True)
    for info in archive.infolist():
        target = (destination / info.filename).resolve()
        if not target.is_relative_to(destination.resolve()):
            raise ValueError('Archive member leaves runtime directory')
    archive.extractall(destination)

for filename, expected in ARCHIVES.items():
    assert hashlib.sha256((OUT / filename).read_bytes()).hexdigest() == expected, filename
with zipfile.ZipFile(OUT / 'python-3.9.13-embed-amd64.zip') as archive:
    unpack(archive, OUT / 'python')
with zipfile.ZipFile(OUT / 'wafel_0_8_5_win_x64.zip') as archive:
    wheel = archive.read('bindings/python/wafel-0.8.5-cp39-cp39-win_amd64.whl')
    with zipfile.ZipFile(io.BytesIO(wheel)) as package:
        unpack(package, OUT / 'python')
    locked = archive.read('libsm64/sm64_jp.dll.locked')
    (OUT / 'sm64_jp.dll.locked').write_bytes(locked)
print('Pinned Python 3.9.13 and Wafel 0.8.5 unpacked locally.')
