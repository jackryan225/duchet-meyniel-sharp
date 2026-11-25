#!/bin/sh
# Second kernel. Usage (in a Lake project folder): sh l4l.sh <tag> <Module> <name>...
# Exports the named theorems with lean4export (v4.34 build) and checks the export with lean4lean (d51e8ad). lean4lean exits 0 also on
# an empty export, so the script also checks that every name is a theorem in the export and that the only axioms are the three.
ulimit -n 8192
tag=$1; mod=$2; shift 2
O=$HOME/build/results; W=$HOME/build/work; X=$HOME/build/checkers; mkdir -p "$O" "$W"
echo "--- lean4export $mod -- $*"
/usr/bin/time -l lake env $X/lean4export-4.34/.lake/build/bin/lean4export "$mod" -- "$@" > "$W/$tag.ndjson" 2> "$O/$tag-export-stderr.txt"; e=$?
grep -E 'real|maximum resident' "$O/$tag-export-stderr.txt"; ls -l "$W/$tag.ndjson" | awk '{print "export bytes", $5}'; echo "--- lean4export: exit $e"
python3 -I - "$W/$tag.ndjson" "$@" <<'PY' | tee "$O/$tag-export-names.txt"
import json, sys
names = {0: ''}; th = set(); ax = []; n = 0
for line in open(sys.argv[1]):
    o = json.loads(line)
    if 'in' in o:
        k = o['in']
        if 'str' in o: names[k] = (names[o['str']['pre']] + '.' + o['str']['str']).lstrip('.')
        elif 'num' in o: names[k] = names[o['num']['pre']] + '.' + str(o['num']['i'])
    elif 'thm' in o: th.add(names[o['thm']['name']]); n += 1
    elif 'axiom' in o: ax.append(names[o['axiom']['name']])
missing = [x for x in sys.argv[2:] if x not in th]
print('theorems in export:', n, 'axioms in export:', sorted(ax), 'missing named theorems:', missing)
print('EXPORT-OK' if not missing and sorted(ax) == ['Classical.choice', 'Quot.sound', 'propext'] else 'EXPORT-BAD')
PY
echo "--- lean4lean --import $tag.ndjson"
/usr/bin/time -l $X/lean4lean/.lake/build/bin/lean4lean --import "$W/$tag.ndjson" > "$O/$tag-lean4lean.txt" 2>&1; e=$?
grep -E 'checked|real|maximum resident|error|rror' "$O/$tag-lean4lean.txt" | head -10; echo "--- lean4lean: exit $e"
