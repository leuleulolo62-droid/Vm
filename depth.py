import re, sys
lines = open(sys.argv[1], "r", encoding="utf-8").read().split("\n")
depth = 0
for i, ln in enumerate(lines, 1):
    t = re.sub(r'--.*', '', ln)
    t = re.sub(r'"(\\.|[^"\\])*"', '""', t)
    t = re.sub(r"'(\\.|[^'\\])*'", "''", t)
    d = t.count('(') - t.count(')')
    if d != 0:
        depth += d
        print("L%d d%+d -> %d : %s" % (i, d, depth, ln.strip()[:72]))
print("FINAL paren depth:", depth)
