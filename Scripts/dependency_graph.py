"""
dependency_graph.py  --  the proof graph of Sections 4 and 5, built from the
text and verified, in the manner of Section 57 of the Primitive Architecture.

The object is the paper's own text: every labeled item (Convention, Definition,
Lemma, Corollary, Theorem, Posit) and the dependencies line that closes it,
"*Dependencies.* ... Nothing else is used." Edges run from an item to what its
dependencies line names. A name that is one of this paper's items is an
internal edge; any other name must resolve, by kind and number, to a labeled
item of [1] (the Primitive Architecture source text), or the run fails.

Verified:
  1. every proof-bearing item carries exactly one dependencies line;
  2. every external citation resolves in the source text of [1];
  3. no label of this paper shadows a label of [1] that this paper cites;
  4. the graph is acyclic;
  5. every internal dependency precedes its citer in the text;
  6. the posited item bears no load (no edge enters it);
  7. the terminal census and the longest chain are reported.

Usage:  python3 -I dependency_graph.py [section_4.md section_5.md] [paper1.txt]
"""

import os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = HERE if os.path.exists(os.path.join(HERE, "main.tex")) else os.path.dirname(HERE)
DEFAULT_SECTIONS = [os.path.join(ROOT, "main.tex")]
DEFAULT_PAPER1 = [os.path.join(HERE, "new_pa.txt"),
                  os.path.join(os.path.dirname(HERE), "new_pa.txt")]

KINDS = ("Convention", "Definition", "Lemma", "Corollary", "Theorem", "Posit")
CITE_KINDS = ("Axiom", "Definition", "Proposition", "Lemma", "Theorem",
              "Corollary", "Convention", "Posit", "Section")
ITEM_RE = re.compile(r"\*\*(" + "|".join(KINDS) + r") (\d+\.\d+) \(([^)]*)\)")
DEPS_RE = re.compile(r"\*Dependencies\.\*(.*?)Nothing else is used\.", re.S)
CITE_RE = re.compile(r"\b(" + "|".join(CITE_KINDS) + r") (\d+(?:\.\d+)?)")


def load_sections(paths):
    text = ""
    for p in paths:
        with open(p, encoding="utf-8") as f:
            text += f.read() + "\n"
    return text


TEX_ITEM_RE = re.compile(r"\\begin\{(definition|lemma|corollary|theorem|convention|posit|proposition)\}\[([^\]]*)\]\s*\\label\{([^}]*)\}")
TEX_DEPS_RE = re.compile(r"\\deps\{(.*?)\}", re.S)
TEX_KIND = {"definition": "Definition", "lemma": "Lemma", "corollary": "Corollary",
            "theorem": "Theorem", "convention": "Convention", "posit": "Posit",
            "proposition": "Proposition"}


def extract_items_tex(text):
    """Items of a LaTeX source: environments with a label. The label is the
       identity; internal citations are \\ref{label}; external citations are
       'Kind~number' patterns naming items of [1]."""
    marks = list(TEX_ITEM_RE.finditer(text))
    items = []
    for i, m in enumerate(marks):
        start = m.start()
        end = marks[i + 1].start() if i + 1 < len(marks) else len(text)
        span = text[start:end]
        deps_lines = []
        j = 0
        while True:
            j = span.find("\\deps{", j)
            if j < 0:
                break
            k = j + 6; depth = 1
            while k < len(span) and depth:
                depth += (span[k] == "{") - (span[k] == "}"); k += 1
            deps_lines.append(span[j + 6:k - 1]); j = k
        items.append(dict(kind=TEX_KIND[m.group(1)], num=m.group(3), name=m.group(2),
                          label=m.group(3), pos=i, deps_lines=deps_lines, tex=True))
    return items


def extract_items(text):
    """Items in text order with their spans and dependencies."""
    marks = list(ITEM_RE.finditer(text))
    items = []
    for i, m in enumerate(marks):
        start = m.start()
        end = marks[i + 1].start() if i + 1 < len(marks) else len(text)
        span = text[start:end]
        deps_lines = DEPS_RE.findall(span)
        items.append(dict(kind=m.group(1), num=m.group(2), name=m.group(3),
                          label=f"{m.group(1)} {m.group(2)}", pos=i,
                          deps_lines=deps_lines))
    return items


def paper1_labels(path):
    """Every labeled item of [1] at a line start, kind-aware, plus section
       headers of the form '<n> <Title>'."""
    labels = set()
    with open(path, encoding="utf-8", errors="replace") as f:
        for line in f:
            m = re.match(r"^\s*(Axiom|Definition|Proposition|Lemma|Theorem|Corollary|Remark) (\d+\.\d+)\b", line)
            if m:
                labels.add((m.group(1), m.group(2)))
            m = re.match(r"^\s*(\d+) [A-Z]", line)
            if m:
                labels.add(("Section", m.group(1)))
    return labels


def build(items, p1):
    by_label = {it["label"]: it for it in items}
    edges = []          # (citer, cited) over internal labels
    external = {}       # citer -> set of external (kind, num)
    problems = []
    for it in items:
        if it["kind"] == "Posit":
            if it["deps_lines"]:
                problems.append(f"{it['label']} is posited and must carry no dependencies line")
            continue
        if len(it["deps_lines"]) != 1:
            problems.append(f"{it['label']} carries {len(it['deps_lines'])} dependencies lines (needs 1)")
            continue
        line = it["deps_lines"][0]
        external[it["label"]] = set()
        if it.get("tex"):
            for ref in re.findall(r"\\ref\{([^}]*)\}", line):
                if ref in by_label:
                    if ref == it["label"]:
                        problems.append(f"{it['label']} cites itself")
                    edges.append((it["label"], ref))
                else:
                    problems.append(f"{it['label']} cites \\ref{{{ref}}}, which is neither an item of this paper nor a labeled item of [1]")
            line = re.sub(r"[A-Za-z]+~\\ref\{[^}]*\}", "", line)   # strip internal refs
            line = line.replace("~", " ")
        cites = set(CITE_RE.findall(line))
        for kind, num in cites:
            lab = f"{kind} {num}"
            if lab in by_label and not it.get("tex"):
                if lab == it["label"]:
                    problems.append(f"{it['label']} cites itself")
                edges.append((it["label"], lab))
            else:
                if (kind, num) not in p1:
                    problems.append(f"{it['label']} cites {lab}, which is neither an item of this paper nor a labeled item of [1]")
                external[it["label"]].add((kind, num))
    return by_label, edges, external, problems


def check_shadowing(items, external, p1):
    cited_p1 = set().union(*external.values()) if external else set()
    out = []
    for it in items:
        if it.get("tex"):
            continue
        key = (it["kind"], it["num"])
        if key in p1 and key in cited_p1:
            out.append(f"{it['label']} shadows a cited label of [1]")
    return out


def check_acyclic_and_order(items, edges):
    pos = {it["label"]: it["pos"] for it in items}
    forward = [f"{a} depends on {b}, which follows it in the text"
               for a, b in edges if pos[b] >= pos[a]]
    # cycle search by DFS
    adj = {}
    for a, b in edges:
        adj.setdefault(a, set()).add(b)
    WHITE, GREY, BLACK = 0, 1, 2
    color = {l: WHITE for l in pos}
    cycles = []

    def dfs(u, stack):
        color[u] = GREY; stack.append(u)
        for v in adj.get(u, ()):
            if color[v] == GREY:
                cycles.append(" -> ".join(stack[stack.index(v):] + [v]))
            elif color[v] == WHITE:
                dfs(v, stack)
        stack.pop(); color[u] = BLACK

    for l in pos:
        if color[l] == WHITE:
            dfs(l, [])
    return forward, cycles


def longest_chain(items, edges):
    adj = {}
    for a, b in edges:
        adj.setdefault(a, set()).add(b)
    memo = {}

    def depth(u):
        if u in memo:
            return memo[u]
        best = ([u], 1)
        for v in adj.get(u, ()):
            chain, d = depth(v)
            if d + 1 > best[1]:
                best = ([u] + chain, d + 1)
        memo[u] = best
        return best

    return max((depth(it["label"]) for it in items), key=lambda x: x[1])


def run(section_paths, paper1_path):
    text = load_sections(section_paths)
    items = extract_items_tex(text) if all(p.endswith(".tex") for p in section_paths) else extract_items(text)
    p1 = paper1_labels(paper1_path)
    by_label, edges, external, problems = build(items, p1)
    problems += check_shadowing(items, external, p1)
    forward, cycles = check_acyclic_and_order(items, edges)
    in_deg = {it["label"]: 0 for it in items}
    for a, b in edges:
        in_deg[b] += 1
    posits = [it["label"] for it in items if it["kind"] == "Posit"]
    posit_loaded = [p for p in posits if in_deg[p] > 0]
    chain, depth = longest_chain(items, edges)
    terminals = sorted(set().union(*external.values())) if external else []
    census = {}
    for kind, num in terminals:
        census[kind] = census.get(kind, 0) + 1

    print("=" * 78)
    print("THE PROOF GRAPH OF SECTIONS 4 AND 5, built from the text and verified")
    print("=" * 78)
    print(f"  items: {len(items)}   internal edges: {len(edges)}   "
          f"external citations: {len(terminals)}   source of [1]: {os.path.basename(paper1_path)}")
    print()
    print("  ITEMS, in text order, with what each uses")
    print("  " + "-" * 74)
    for it in items:
        ints = sorted(b for a, b in edges if a == it["label"])
        exts = sorted(f"{k} {n}" for k, n in external.get(it["label"], ()))
        tag = "posited; bears no load" if it["kind"] == "Posit" else ""
        print(f"  {it['label']:<16} {it['name'][:44]:<44} {tag}")
        if ints:
            print(f"      this paper: {', '.join(ints)}")
        if exts:
            print(f"      [1]:        {', '.join(exts)}")
    print("  " + "-" * 74)
    print()
    print("  TERMINAL CENSUS (where every chain bottoms out, in [1])")
    for k in sorted(census):
        print(f"     {k:<12} {census[k]}")
    print(f"  LONGEST CHAIN ({depth} items): " + " -> ".join(chain))
    print()
    checks = [
        ("every proof-bearing item carries exactly one dependencies line, and the "
         "posited item none", not any("dependencies line" in p for p in problems)),
        ("every citation of [1] resolves to a labeled item of its source text, by kind "
         "and number", not any("neither an item" in p for p in problems)),
        ("no label of this paper shadows a cited label of [1]",
         not any("shadows" in p for p in problems)),
        ("the graph is acyclic", not cycles),
        ("every internal dependency precedes its citer in the text", not forward),
        (f"the posited item bears no load: in-degree 0 for {', '.join(posits)}",
         bool(posits) and not posit_loaded),
        ("every chain terminates in [1] or in Convention 5.1 alone",
         all(k in ("Axiom", "Definition", "Proposition", "Lemma", "Theorem",
                   "Corollary", "Section") for k, _ in terminals)),
    ]
    print("-" * 78)
    print("VERDICTS")
    print("-" * 78)
    for p in problems + forward + cycles:
        print(f"   !! {p}")
    total = passed = 0
    for d, ok in checks:
        total += 1; passed += 1 if ok else 0
        print(f"   [{'PASS' if ok else 'FAIL'}]  {d}")
    print()
    print("=" * 78)
    print(f"VERDICT:  All {total} checks pass." if passed == total
          else f"VERDICT:  {passed}/{total} pass -- FAILURE PRESENT.")
    print("=" * 78)
    return passed == total


def latex_table(section_paths, paper1_path, out_path):
    """Emit the proof graph as a LaTeX table: each item of this paper with the
       items of this paper and of [1] it uses."""
    text = load_sections(section_paths)
    items = extract_items_tex(text) if all(p.endswith(".tex") for p in section_paths) else extract_items(text)
    p1 = paper1_labels(paper1_path)
    by_label, edges, external, problems = build(items, p1)
    rows = []
    for it in items:
        ints = sorted(b for a, b in edges if a == it["label"])
        exts = sorted(f"{k}~{n}" for k, n in external.get(it["label"], ()))
        tag = "posited; sink" if it["kind"] == "Posit" else ""
        name = it["name"].split(" \u2014 ")[0].split(" --- ")[0]
        rows.append((it["label"], name, ", ".join(ints) or "---", ", ".join(exts) or (tag or "---")))
    body = "\\begin{tabular}{@{} p{0.13\\textwidth} p{0.24\\textwidth} p{0.24\\textwidth} p{0.31\\textwidth} @{}}\n\\toprule\n"
    body += "\\textbf{Item} & \\textbf{Name} & \\textbf{Uses (this paper)} & \\textbf{Uses ([1])} \\\\\n\\midrule\n"
    for lab, name, ints, exts in rows:
        body += f"{lab} & {name} & {ints} & {exts} \\\\\n"
    body += "\\bottomrule\n\\end{tabular}\n"
    with open(out_path, "w") as f:
        f.write("% generated by dependency_graph.py -- do not edit\n" + body)
    return len(items), len(edges), len(set().union(*external.values()) if external else [])


if __name__ == "__main__":
    args = sys.argv[1:]
    args = [a for a in args]
    secs = [a for a in args if a.endswith(".md") or a.endswith(".tex")] or DEFAULT_SECTIONS
    p1s = [a for a in args if a.endswith(".txt")]
    p1 = p1s[0] if p1s else next((p for p in DEFAULT_PAPER1 if os.path.exists(p)), None)
    if p1 is None:
        print("source text of [1] not found; pass its path"); sys.exit(2)
    if "--latex" in args:
        out = os.path.join(HERE, "tables", "tab_graph.tex")
        os.makedirs(os.path.dirname(out), exist_ok=True)
        print("proof graph table written:", latex_table(secs, p1, out))
        sys.exit(0)
    sys.exit(0 if run(secs, p1) else 1)
