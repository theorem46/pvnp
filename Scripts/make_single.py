"""
make_single.py -- produce a single-file Overleaf source, main_single.tex, by
inlining every \input{...} of main.tex (the generated tables and the generated
appendices). Run make_tables.py and make_appendices.py first.
"""
import os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = HERE if os.path.exists(os.path.join(HERE, "main.tex")) else os.path.dirname(HERE)

def inline(text, depth=0):
    def repl(m):
        path = os.path.join(ROOT, m.group(1))
        if not path.endswith(".tex"):
            path += ".tex"
        with open(path, encoding="utf-8") as f:
            body = f.read()
        body = "\n".join(l for l in body.splitlines() if not l.startswith("% generated"))
        return f"% ---- inlined from {m.group(1)} ----\n" + inline(body, depth + 1)
    return re.sub(r"\\input\{([^}]*)\}", repl, text)

src = open(os.path.join(ROOT, "main.tex"), encoding="utf-8").read()
out = inline(src)
with open(os.path.join(ROOT, "main_single.tex"), "w", encoding="utf-8") as f:
    f.write(out)
print("main_single.tex written;", out.count("\\input{"), "inputs remain")
