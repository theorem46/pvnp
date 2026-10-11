"""
quote_check.py  --  every passage quoted from [1] in the paper is verified
verbatim against the source text.

Quotations in main.tex and the section drafts are written between `` and ''
(LaTeX) or between straight double quotes (Markdown). Each is normalised
(whitespace collapsed, dashes and quotes unified, LaTeX math stripped) and
searched for in the normalised source text of [1]. A quotation that is not
found verbatim fails the run. Usage: python3 -I quote_check.py [files...]
"""

import os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = HERE if os.path.exists(os.path.join(HERE, "main.tex")) else os.path.dirname(HERE)
SOURCE = os.path.join(HERE, "new_pa.txt")
SOURCE2 = os.path.join(HERE, "yang_mills.txt")     # passages marked \\qq{...} are from [2]
DEFAULT_FILES = ["main.tex", "section_encoding_stratification.md", "section_theorems.md"]


def normalise(s):
    s = re.sub(r"(?m)^\s*\d{1,3}\s*$", " ", s)          # page numbers standing alone on a line
    s = s.replace("\u2014", "-").replace("\u2013", "-").replace("---", "-").replace("--", "-")
    s = s.replace("\u2265", ">=").replace("\u2264", "<=").replace("\u22a1", "(+)").replace("\u00b7", "*")
    s = s.replace("\u2212", "-").replace("\u2019", "'").replace("\u2018", "'").replace("``", '"').replace("''", '"')
    s = s.replace("\u201c", '"').replace("\u201d", '"')
    s = re.sub(r"\\[a-zA-Z]+\{([^}]*)\}", r"\1", s)        # \emph{x} -> x
    s = s.replace("$", "").replace("\\ge", ">=").replace("\\otimes", "(x)").replace("\\neg", "not")
    s = s.replace("\\,", " ").replace("\\", "")
    s = re.sub(r"\s+", " ", s)
    return s.strip().lower()


def quotes_in(text, fn):
    """In LaTeX, only passages marked \\q{...} are citations of [1]; in the
       Markdown drafts every double-quoted passage of citation length is."""
    out = []
    if fn.endswith(".tex"):
        for macro, which in (("\\q{", 1), ("\\qq{", 2)):
            i = 0
            while True:
                j = text.find(macro, i)
                if j < 0:
                    break
                k = j + len(macro); depth = 1
                while k < len(text) and depth:
                    depth += (text[k] == "{") - (text[k] == "}"); k += 1
                out.append((which, text[j + len(macro):k - 1])); i = k
        # \q{ also matches inside \qq{ : drop the duplicates it produces
        qq = {q for w, q in out if w == 2}
        out = [(w, q) for w, q in out if not (w == 1 and q in qq)]
        return out
    for m in re.finditer(r"\"(.+?)\"", text, re.S):
        out.append((1, m.group(1)))
    return out


def main(files):
    srcs = {1: normalise(open(SOURCE, encoding="utf-8", errors="replace").read())}
    if os.path.exists(SOURCE2):
        srcs[2] = normalise(open(SOURCE2, encoding="utf-8", errors="replace").read())
    mins = {w: v.replace("- ", "").replace(" -", "") for w, v in srcs.items()}
    total = ok = 0
    for fn in files:
        path = os.path.join(ROOT, fn)
        if not os.path.exists(path):
            continue
        text = open(path, encoding="utf-8").read()
        for which, q in quotes_in(text, fn):
            src = srcs.get(which, ""); src_min = mins.get(which, "")
            nq = normalise(q)
            if len(nq) < 25:                   # short phrases are not citations
                continue
            # an elision '...' splits the quotation into fragments, each verified
            frags = [f.strip().rstrip(".,;:") for f in re.split(r"\.\.\.|\u2026|\\dots|\\ldots", nq) if f.strip()]
            total += 1
            found = all(f in src or f.replace("- ", "").replace(" -", "") in src_min for f in frags)
            ok += 1 if found else 0
            print(f"[{'OK  ' if found else 'MISS'}] {fn} [{which}]: \"{q[:90]}{'...' if len(q) > 90 else ''}\"")
    print()
    print(f"{ok} of {total} quotations found verbatim in the source texts of [1] and [2].")
    if total == 0:
        # A verifier that passes because it had nothing to verify is a false
        # green: it means no source file was found, not that the paper is clean.
        print("FAIL: no quotations were found to check -- expected main.tex beside "
              "this script or in its parent directory, and new_pa.txt next to it.")
        return False
    return ok == total


if __name__ == "__main__":
    files = sys.argv[1:] or DEFAULT_FILES
    sys.exit(0 if main(files) else 1)
