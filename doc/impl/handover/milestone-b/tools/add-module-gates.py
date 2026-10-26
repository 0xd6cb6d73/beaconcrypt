#!/usr/bin/env python3
"""Append per-module inventory gates (root import, theorem/guard counts, each guard and theorem) for new Computational modules,
bump the handwritten-lean count, and register the files in reviewed-inventory.txt. Usage: add-module-gates.py Module1 [Module2 ...]"""
import hashlib, re, sys
from pathlib import Path
core = Path('/tmp/beaconcrypt-authenticated-root-completion/beaconcrypt-core')
script = core / 'proofs/check-inventory.sh'
manifest = core / 'proofs/reviewed-inventory.txt'
text = script.read_text()
lines = manifest.read_text().rstrip('\n').split('\n')
blocks = []
rx = lambda n: re.sub(r'([?+*()\[\]{}|^$\\.])', r'\\\1', n)
for module in sys.argv[1:]:
    rel = f'proofs/lean/BeaconcryptCore/Computational/{module}.lean'
    src = (core / rel).read_text()
    theorems = re.findall(r'^theorem (\S+)', src, flags=re.M)
    guards = len(re.findall(r'^#guard_msgs in$', src, flags=re.M))
    printed = re.findall(r'^#print axioms BeaconcryptCore\.Computational\.' + re.escape(module) + r'\.(\S+)$', src, flags=re.M)
    assert guards == len(printed) and set(theorems) <= set(printed), (module, guards, len(theorems), len(printed))
    out = [f'selected_source_module={rel}',
           f"require_line_count 1 '^import BeaconcryptCore.Computational.{module}$' proofs/lean/BeaconcryptCore.lean \"{module} root import\"",
           f"require_line_count {len(theorems)} '^theorem ' \"$selected_source_module\" \"{module} theorem inventory\"",
           f"require_line_count {guards} '^#guard_msgs in$' \"$selected_source_module\" \"{module} guarded dependencies\""]
    for name in printed:
        out.append(f"require_line_count 1 '^#print axioms BeaconcryptCore.Computational.{module}.{rx(name)}$' \"$selected_source_module\" \"{module} dependency {name}\"")
        if name in theorems:
            out.append(f"require_line_count 1 '^theorem {rx(name)}([[:space:]]|$)' \"$selected_source_module\" \"{module} theorem {name}\"")
    blocks.append('\n'.join(out))
    if not any(l.endswith('\t' + rel) for l in lines):
        lines.append('\t'.join(('handwritten-lean', hashlib.sha256((core / rel).read_bytes()).hexdigest(), rel)))
count = int(re.search(r'\[handwritten-lean\]=(\d+)', text).group(1))
added = sum(1 for m in sys.argv[1:] if f'proofs/lean/BeaconcryptCore/Computational/{m}.lean' not in manifest.read_text())
text = text.replace(f'[handwritten-lean]={count}', f'[handwritten-lean]={count + added}')
final = "\nprintf 'Formal-verification inventory matches the reviewed boundary.\\n'\n"
assert text.endswith(final)
text = text[:-len(final)] + '\n' + '\n'.join(blocks) + '\n' + final
script.write_text(text)
manifest.write_text('\n'.join(lines) + '\n')
print('handwritten-lean', count, '->', count + added, 'modules', sys.argv[1:])
