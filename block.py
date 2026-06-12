import sys
# proper-ish Lua tokenizer: skip strings & comments, then balance block keywords
src = open(sys.argv[1], "r", encoding="utf-8").read()
i, n = 0, len(src)
toks = []
def long_bracket(i):
    # at '[' ; returns (level, contentEnd_after_close) or None
    j = i + 1; eq = 0
    while j < n and src[j] == '=':
        eq += 1; j += 1
    if j < n and src[j] == '[':
        close = "]" + "=" * eq + "]"
        k = src.find(close, j + 1)
        return (n if k == -1 else k + len(close))
    return None
while i < n:
    c = src[i]
    if c == '-' and src[i:i+2] == '--':
        if src[i+2:i+3] == '[':
            lb = long_bracket(i+2)
            if lb: i = lb; continue
        j = src.find('\n', i); i = n if j == -1 else j; continue
    if c == '[':
        lb = long_bracket(i)
        if lb: i = lb; continue
        toks.append('['); i += 1; continue
    if c == '"' or c == "'":
        q = c; j = i + 1
        while j < n:
            if src[j] == '\\': j += 2; continue
            if src[j] == q: j += 1; break
            j += 1
        i = j; continue
    if c.isalpha() or c == '_':
        j = i
        while j < n and (src[j].isalnum() or src[j] == '_'): j += 1
        toks.append(src[i:j]); i = j; continue
    if c in '(){}':
        toks.append(c)
    i += 1
OPEN = {"function", "do", "then", "if", "for", "while", "repeat"}  # using if/for/while+do/then carefully
# Lua block model: function/do/while..do/for..do/if..then -> end ; repeat -> until
# count: each 'function' -> needs end; 'do' -> end; 'then' from if -> end (but elseif/else share); 'repeat'->until
depth = 0
stack = []
skip_then = False
for t in toks:
    if t == "function": stack.append("function")
    elif t == "do": stack.append("do")          # for/while ... do
    elif t == "then":
        if skip_then:
            skip_then = False                    # the 'then' belongs to an elseif
        else:
            stack.append("then")                 # opens an if-block (closed by end)
    elif t == "repeat": stack.append("repeat")
    elif t == "elseif":
        skip_then = True                          # its 'then' does NOT open a new block
    elif t == "else":
        pass  # else stays within the 'then' block
    elif t == "end":
        # closes nearest function/do/then
        while stack and stack[-1] not in ("function", "do", "then"):
            stack.pop()
        if stack: stack.pop()
        else: print("UNMATCHED end")
    elif t == "until":
        if stack and stack[-1] == "repeat": stack.pop()
        else: print("UNMATCHED until")
par = sum(1 for t in toks if t == '(') - sum(1 for t in toks if t == ')')
brace = sum(1 for t in toks if t == '{') - sum(1 for t in toks if t == '}')
print("unclosed blocks:", len(stack), stack[-5:] if stack else [])
print("paren diff:", par, " brace diff:", brace)
print("RESULT:", "OK" if (len(stack) == 0 and par == 0 and brace == 0) else "IMBALANCE")
