import re, sys
src = open(sys.argv[1], "r", encoding="utf-8").read()
# strip long strings/comments first, then quoted strings, THEN line comments
s = re.sub(r'\[(=*)\[.*?\]\1\]', '""', src, flags=re.S)   # long brackets
s = re.sub(r'"(\\.|[^"\\])*"', '""', s)
s = re.sub(r"'(\\.|[^'\\])*'", "''", s)
s = re.sub(r'--\[\[.*?\]\]', '', s, flags=re.S)
s = re.sub(r'--[^\n]*', '', s)
for o, c in [('(', ')'), ('{', '}'), ('[', ']')]:
    print(o, c, "balance:", s.count(o) - s.count(c))
opens = len(re.findall(r'\bfunction\b', s)) + len(re.findall(r'\bdo\b', s)) + \
        len(re.findall(r'\bthen\b', s)) + len(re.findall(r'\brepeat\b', s))
closes = len(re.findall(r'\bend\b', s)) + len(re.findall(r'\buntil\b', s))
elseif = len(re.findall(r'\belseif\b', s))
print("block opens(-elseif):", opens - elseif, " closes:", closes,
      " diff:", (opens - elseif) - closes, "(0 = balanced)")
