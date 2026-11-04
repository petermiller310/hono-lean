#!/usr/bin/env python3
"""Fail if any relative link in a tracked Markdown file points at a missing file."""
import re
import subprocess
import sys
from pathlib import Path
from urllib.parse import unquote

ROOT = Path(__file__).resolve().parents[1]
LINK = re.compile(r'\]\(([^)\s]+)(?:\s+"[^"]*")?\)|<img[^>]*\bsrc="([^"]+)"')


def links(text):
    for match in LINK.finditer(text):
        yield match.group(1) or match.group(2)


def is_local(target):
    return not re.match(r'^[a-z][a-z0-9+.-]*:', target, re.I) and not target.startswith('#')


def main():
    names = subprocess.check_output(['git', 'ls-files', '*.md'], cwd=ROOT, text=True).split()
    broken = []
    for name in names:
        source = ROOT / name
        if not source.exists():
            continue
        for target in links(source.read_text()):
            if not is_local(target):
                continue
            path = unquote(target.split('#', 1)[0])
            if path and not (source.parent / path).exists():
                broken.append(f'{name}: {target}')
    for line in broken:
        print(line)
    print(f'{len(names)} Markdown files checked, {len(broken)} broken links.')
    return 1 if broken else 0


if __name__ == '__main__':
    sys.exit(main())
