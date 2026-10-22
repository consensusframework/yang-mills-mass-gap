#!/usr/bin/env python3
"""Documentary CI-log checks for Stone 59; does not execute Lean.

Created by the coordination on 2026-10-21. Accepts the original 59-P
log (JSON or text), the frozen module source and the QA1 warning baseline
as explicit paths. It does not modify its inputs or the original package.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re

SOURCE_SHA = '61dde0c961ef126dd813c04a869da5fd4f60ec08395f84a2fb3ad18016704cee'
BASELINE_SHA = '42817399cb566dffab0f584e26e94eb9bbad6aa16455f37b97b6b36ad21dd219'
STANDARD = ('propext', 'Classical.choice', 'Quot.sound')

def require(condition, message):
    if not condition:
        raise SystemExit('FAIL: ' + message)

def normalized(text):
    return re.sub(r'^\ufeff?\d{4}-\d\d-\d\dT[\d:.]+Z ?', '', text, flags=re.M)

def read_log(path):
    text = path.read_text(encoding='utf-8-sig')
    try:
        obj = json.loads(text)
    except json.JSONDecodeError:
        return text
    require(isinstance(obj, dict), 'JSON log must be an object')
    value = obj.get('logs_content', obj.get('content'))
    require(isinstance(value, str), 'JSON log lacks logs_content/content')
    return value

def project_warning_blocks(text):
    # Same block boundaries and ./ normalization as the audited baseline
    # comparison; warning continuation text is retained without rewriting.
    event = re.compile(r'^(✔|⚠|✖|ℹ|info:|warning:|error:|Build |trace:|\S? ?\[\d+/\d+\])')
    blocks, current = [], None
    for line in normalized(text).split('\n'):
        if line.startswith('warning:'):
            if current:
                blocks.append(current)
            current = [line]
        elif event.match(line) or (not line.strip() and current is None):
            if current:
                blocks.append(current)
            current = None
        elif current is not None:
            current.append(line)
    if current:
        blocks.append(current)
    result = []
    for block in blocks:
        block[0] = re.sub(r'^warning: (\./)+', 'warning: ', block[0])
        if block[0].startswith('warning: LatticeGauge/'):
            result.append('\n'.join(block).rstrip())
    return Counter(result)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--log', required=True, type=Path)
    parser.add_argument('--module-source', required=True, type=Path)
    parser.add_argument('--baseline', required=True, type=Path)
    parser.add_argument('--expect-sha', required=True)
    args = parser.parse_args()
    source = args.module_source.read_bytes()
    baseline = args.baseline.read_bytes()
    require(hashlib.sha256(source).hexdigest() == SOURCE_SHA, 'module source hash')
    require(hashlib.sha256(baseline).hexdigest() == BASELINE_SHA, 'QA1 baseline hash')
    require(re.fullmatch(r'[a-f0-9]{40}', args.expect_sha) is not None, 'expected SHA syntax')
    module_names = {'LatticeGauge.' + n for n in re.findall(r'^#print axioms (\S+)', source.decode(), re.M)}
    require(len(module_names) == 44, '44 distinct module commands')
    log = normalized(read_log(args.log))
    lines = log.splitlines()
    # Requires the SHA emitted by git log --format=%H, rather than only a
    # SHA mentioned in a fetched ref or in a script body.
    require(args.expect_sha in lines, 'effective checkout SHA output')
    builds = re.findall(r'^.*\bBuilt (LatticeGauge\.[^\s]+)', log, re.M)
    require(len(builds) == len(set(builds)) == 120, '120 unique project builds')
    require(not re.search(r'\bReplayed LatticeGauge\.', log), 'no project replay')
    require('Build completed successfully.' in log, 'successful build completion')
    diagnostic_text = re.sub(r'\x1b\[[0-9;]*m', '', log)
    require(not re.search(r'^\s*(?:error:|::error::|##\[error\])', diagnostic_text, re.M), 'no build error')
    rows = re.findall(r"'(LatticeGauge\.[^\n]+)' depends on axioms:\s*\[([^\]]*)\]", log)
    names = Counter(n for n, _ in rows)
    require(len(rows) == 364 and len(names) == 362, '364 outputs / 362 names')
    require(all(tuple(x.strip() for x in axioms.split(',')) == STANDARD for _, axioms in rows), 'all axiom lists standard')
    require(all(names[n] == 1 for n in module_names), '44 module outputs exactly once')
    require('no sorryAx.' in log, 'workflow sorryAx check completed')
    require(not any('sorryAx' in l and not any(s in l for s in ('grep', 'echo', 'no sorryAx')) for l in lines), 'no sorryAx outside workflow script/check')
    require(log.count('lake-manifest.json: OK') == 2, 'two manifest confirmations')
    require(len(re.findall(r' @ [0-9a-f]{40}$', log, re.M)) == 9, 'nine dependency revisions listed')
    warnings = project_warning_blocks(log)
    require(sum(warnings.values()) == 114, '114 project warnings')
    require(warnings == project_warning_blocks(baseline.decode()), 'complete warning multiset equals QA1')
    require(not any('ActivityProfileDampingOptimalCover' in b.split('\n')[0] for b in warnings), 'no new-module warning')
    print(json.dumps({
        'result': 'PASS documentary log checks', 'effective_sha': args.expect_sha,
        'project_built': 120, 'project_replayed': 0, 'project_warnings': 114,
        'axiom_outputs': len(rows), 'distinct_names': len(names),
        'module_outputs': 44, 'multiline_lists': sum('\n' in ax for _, ax in rows),
        'lean_executed_by_this_script': False,
    }, ensure_ascii=False, indent=2))

if __name__ == '__main__':
    main()
