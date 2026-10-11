"""
make_appendices.py  --  generate appendices.tex from the experiments.

For each appendix: a scope paragraph, Table X1 (protocol mapping: protocol,
sections, targeted results, structural mechanism -- held here, beside the
scripts they describe) and Table X2 (structural outputs and verdicts, read
from the script's run so that every row is the outcome of that run), and an
analysis paragraph. Appendix F prints the verification programs' verdicts.
Usage: python3 -I make_appendices.py   (runs every script; writes appendices.tex)
"""

import os, re, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = HERE if os.path.exists(os.path.join(HERE, "main.tex")) else os.path.dirname(HERE)


def fit(text, width=72):
    """Wrap a run transcript so it cannot overrun a narrow text block.
       Rules are shortened; long lines are folded with a hanging indent."""
    out = []
    for line in text.split("\n"):
        if len(line) > width and set(line.strip()) <= {"=", "-"}:
            out.append(line.strip()[0] * width); continue
        while len(line) > width:
            cut = line.rfind(" ", 0, width)
            if cut <= 0:
                cut = width
            out.append(line[:cut])
            line = "  " + line[cut:].lstrip()
        out.append(line)
    return "\n".join(out)


def run_script(name):
    out = subprocess.run([sys.executable, "-I", os.path.join(HERE, name)],
                         capture_output=True, text=True, cwd="/")
    return out.stdout


def verdict_rows(transcript):
    """Parse the 'STRUCTURAL OUTPUTS AND VERDICTS' block into
       (protocol, check, result) rows."""
    rows = []
    block = transcript.split("STRUCTURAL OUTPUTS AND VERDICTS")[-1] if "STRUCTURAL OUTPUTS AND VERDICTS" in transcript else transcript.split("VERDICTS")[-1]
    proto = ""
    for line in block.splitlines():
        m = re.match(r"\s{2}([A-E]\.\d+)\s+(.*)", line)
        if m and "[" not in line:
            proto = m.group(1); continue
        m = re.match(r"\s+\[(PASS|FAIL)\]\s+(.*)", line)
        if m:
            rows.append((proto, m.group(2).strip(), m.group(1)))
    return rows


def tex_escape(s):
    s = s.replace("\\", "\\textbackslash{}").replace("&", "\\&").replace("%", "\\%")
    s = s.replace("_", "\\_").replace("#", "\\#").replace("<=", "$\\le$").replace(">=", "$\\ge$")
    s = s.replace("^", "\\^{}").replace("~", "\\~{}")
    s = re.sub(r"(\d)x\b", r"\1$\\times$", s)
    s = s.replace("2^n", "$2^n$").replace("2^(n-1)", "$2^{n-1}$").replace("(.)", "$\\odot$")
    return s


APPENDICES = [
    dict(key="A", script="A_precedence.py", title="Structure Precedes Enumeration: The Withdrawal Table",
         scope="Section~\\ref{sec:precedence}", prog="A\\_precedence.py",
         discipline="Both resolutions are run on the same asserted contents, constituted as oriented allocation units (Definition~18.2). The numerical objects of Section~10 of \\PA{} live in a \\texttt{Count} class and are withdrawn by refusing the corresponding operation; a resolution that reaches for a withdrawn object fails at that reach. No native boolean primitive decides any verdict.",
         mapping=[("A.1 Withdrawal", "\\ref{sec:precedence}", "Implication~I of \\PA{}; Definitions~10.1, 10.2", "The arithmetic operations, order, successor and the capacity count are withdrawn cumulatively from the counts; enumeration (combinations bounded by the count) and the structural resolution (head and tail, pairing to exhaustion) are run at every row and their answers compared.")],
         analysis="The decisive row is the last: with the capacity count of the contents itself withdrawn, the structural resolution still completes and returns $\\{-3,-2,5\\}$, while enumeration cannot be stated. The dependence of number on structure is exhibited as one-directional, which is the content of Implication~I of \\PA{} and the first claim of this paper."),
    dict(key="B", script="B_address.py", title="Data as an Address",
         scope="Sections~\\ref{sec:change} and~\\ref{sec:theorems}", prog="B\\_address.py",
         discipline="Magnitude is constituted: a value of $m$ is $m$ allocation units (Definition~18.2, Theorem~18.1); comparison is conjugate pairing to exhaustion (Theorem~18.5); all work is at the term projection (Theorem~18.6). No native integer arithmetic is used within any derivation and no native boolean primitive decides any verdict; native integers size the genesis pool and render a count for reading.",
         mapping=[("B.1 Constituted magnitude", "\\ref{sec:encoding}", "Def.~\\ref{def:encoding}; Thm.~18.5", "Units constituted with orientation; equality decided by pairing, not comparison."),
                  ("B.2 Conjugate negation", "\\ref{sec:change}", "Lemma~26.5; Thm.~11.1(a)", "$\\neg X$ by componentwise opposition; double reversal returns $X$; $X$ and $\\neg X$ jointly exhaust."),
                  ("B.3 Envelope fixation", "\\ref{sec:theorems}", "Thm.~\\ref{thm:envelope}", "$t(X)=t(P)+t(N)$; the signed range spans $t(X)+1$ magnitudes; the address lies within $\\mathrm{cap}(X)$."),
                  ("B.4 Partition by orientation", "\\ref{sec:encoding}", "Def.~18.2; Def.~\\ref{def:address}", "Sectors disjoint and exhaustive."),
                  ("B.5--B.6 Address and reconstitution", "\\ref{sec:theorems}", "Thm.~\\ref{thm:address}; Thm.~15.3", "The address as the depth where both reaches meet; the residing content exhausts and reconstitutes exactly."),
                  ("B.7 Adversarial agreement", "\\ref{sec:theorems}", "Thm.~\\ref{thm:address}", "38 sampled assertions, with none and with several addresses, against the exhaustive reference; every address within $\\mathrm{cap}(X)$."),
                  ("B.8 Alignment with the source chain", "\\ref{sec:encoding}", "Def.~13.1; Thm.~18.6; Thm.~18.3", "Residue order-invariance; $t$ measured only; no sub-collection formed to test, by inspection of the abstract syntax tree."),
                  ("B.9 The solved state", "\\ref{sec:solved}", "Def.~\\ref{def:solved}; Lemma~\\ref{lem:shadow}; Prop.~\\ref{prop:closure}", "$(\\Sigma,D,S)$ built from Thm.~18.5; $S$ vanishes exactly at exhaustion; closures at the second stratum name the exhausting sub-collections; hierarchical lysis terminates at zero exactly when the sub-collection exhausts, in any order."),
                  ("B.10 The address as a path-word", "\\ref{sec:pathword}", "Def.~\\ref{def:pathword}; Thm.~\\ref{thm:pathword}", "1380 addresses on 38 assertions are balanced words of length $2w$; lysis terminates after $w$ pairings; the coincident reading returns the word the counts write and pays one operation per step of it; magnification multiplies the length in units and nothing else.")],
         analysis="The appendix establishes the address as an object: the depth at which both orientations are resident, read by intersecting the two reaches and never by surveying sub-collections (B.8, by inspection of the abstract syntax tree), and, in B.10, the path-word of the residence with its two lengths, in units and in steps between contents, of which the reading pays the second. Every address agrees with the exhaustive reference and every residing content pairs to exhaustion."),
    dict(key="C", script="C_reading.py", title="Reading the Envelope by Depth; the Selected Partition; the Worked Comparison",
         scope="Sections~\\ref{sec:address}--\\ref{sec:change} and~\\ref{sec:theorems}", prog="C\\_reading.py",
         discipline="The boundary (orientation, extremal floor, cardinality cells) is asserted from the counts and charged; residence is read only inside opened cells; every address is certified by pairing; every anchor is written from its own literature and charged under the one convention (Convention~\\ref{conv:cost}). Assertions are sampled from fixed seeds; nothing in the framework is random.",
         mapping=[("C.1--C.2 Traces; completeness", "\\ref{sec:change}", "Thm.~\\ref{thm:address}", "Zero read by depth on the two assertions; decision agrees with the exhaustive reference on all 300 sampled assertions with $n\\le16$."),
                  ("C.3--C.4 Search space; determinism", "\\ref{sec:theorems}", "Thm.~\\ref{thm:reading}(iii)", "Configurations read against the tower on two families; identical traces across runs; no random source and no configuration outside an opened cell, by inspection of source."),
                  ("C.5--C.8 The selected partition", "\\ref{sec:change}", "Thm.~\\ref{thm:address}(iii); Thm.~\\ref{thm:reading}(ii)", "Coincident cells ranked first from the prefix and suffix sums; computability by inspection of source; first-cell arrivals and reads against coarsest-first on the families."),
                  ("C.9, C.12 The worked comparison", "\\ref{sec:address}", "Thm.~\\ref{thm:reading}", "Survey, table, meet-in-the-middle and the structural reading on $X=\\{-7,-3,-2,5,8\\}$; the reading's ledger certified to sum."),
                  ("C.10 Magnitude invariance", "\\ref{sec:change}", "Thm.~\\ref{thm:reading}(v)", "$n=12$, every content multiplied by $1,2,4,8,16$: the table grows, the reading does not move."),
                  ("C.11 Acts per opened cell", "\\ref{sec:change}", "Thm.~\\ref{thm:reading}(ii)", "Acts per cell counted and cross-checked against the traces: three where the least residences coincide (two reads, one match), six where the greatest do."),
                  ("C.13 The anchors on the families", "\\ref{sec:today}", "Thm.~\\ref{thm:reading}(iv)", "Survey, table, meet-in-the-middle and the reading, means per row, $n=8$ to $20$."),
                  ("C.14 The yield of each method", "\\ref{sec:surplus}", "Table~\\ref{tab:surplus}", "What each resolution returns from one run: decision, content, spectrum, multiplicity, distance."),
                  ("C.15 The boundary's cost law", "\\ref{sec:growth}", "Thm.~\\ref{thm:reading}(i)--(ii)", "On all 400 assertions the boundary costs exactly $B(X)$; a coincident first cell costs exactly $c_P+c_N-1<n$ more (least) or $2(c_P+c_N-1)$ (greatest)."),
                  ("C.16 The ceiling", "\\ref{sec:theorems}", "Def.~\\ref{def:ceiling}; Thm.~\\ref{thm:reading}(iii)--(iv); Thm.~\\ref{thm:encoding}", "On 400 suite and 40 adversarial assertions: the decision agrees with the reference; every cell's interior within its formation bound; the reach reading within $\\rho(X)$ and complete; the table at least the reach reading plus the saved reads; the whole resolution at most the table on all 440 and within $6\\ell^2+11\\ell+8$; the certificate family at no more than the table's cost.")],
         analysis="The decisive confirmations are C.9, C.10 and C.16. On the worked assertion the structural reading forms \\workedStructFormed{} configurations at \\workedStructOps{} operations, each operation named, against \\workedSurveyOps{}, \\workedTableOps{} and \\workedMitmOps{} for the anchors; at fixed $n$ the reading's cost is identical to the operation across a sixteen-fold change of the magnitudes while the table's grows with them; and on every assertion, the adversarial certificate family included, the whole resolution stays within the ceiling's bound, so that the reading is never of worse than the table's order. C.7 reports, row by row, the assertions on which no cell coincides; those are the frontier of boundary assertion."),
    dict(key="D", script="D_boundary.py", title="Boundary Species and Relational Refinement; the Two Modes of Assertion",
         scope="Sections~\\ref{sec:change} and~\\ref{sec:encoding}", prog="D\\_boundary.py",
         discipline="A boundary must be computable from the assertion before the resolution it is meant to accelerate; a proposal that requires the resolution in order to state the boundary is circular and is rejected (D.1, D.5). An eliminating boundary must never exclude a true address (D.3). The stratification boundary is derived, not imported: no library divisor function and no native division (D.1, by inspection of the abstract syntax tree).",
         mapping=[("D.1 Computability", "\\ref{sec:encoding}", "Cor.~\\ref{cor:divisibility}", "No admitted boundary builds a reach or consults an address; no library gcd or native division, by inspection of the abstract syntax tree."),
                  ("D.2 The refinement stack", "\\ref{sec:change}", "Thm.~\\ref{thm:envelope}(iii)", "Envelope, stratification, extremal, cardinality strata on the worked assertion; every true address retained."),
                  ("D.3 Soundness at scale", "\\ref{sec:change}", "Thm.~\\ref{thm:address}(iv)", "473 sampled assertions; no true address excluded; median elimination before any reading."),
                  ("D.4--D.5 Ordering; a rejected boundary", "\\ref{sec:change}", "D.1 criterion", "An ordering boundary reported as the weaker species; a circular proposal scored and rejected."),
                  ("D.6 The stratification boundary, derived", "\\ref{sec:encoding}", "Lemma~\\ref{lem:strat}; Cor.~\\ref{cor:divisibility}", "The relation bearing and not bearing: no common stratifier on the worked assertion; elimination where one exists."),
                  ("D.7 The two modes of assertion", "\\ref{sec:encoding}", "Cor.~\\ref{cor:modes}", "The stratifier recovered from counts by Theorem~20.2 with every subtraction charged, against the stratifier read from the asserted tree."),
                  ("D.8 The remainder class on the frontier", "\\ref{sec:encoding}", "Lemma~\\ref{lem:remainder}; Cor.~\\ref{cor:remainder}", "Sound on every cell carrying an address across 122 cases; the certificate family of C.16 decided at the boundary with no reading on all 40; on the sampled frontier the relation bears on 2 of 156 assertions.")],
         analysis="The boundaries are relations on the assertion, each computed before any reading and each sound at scale. D.7 is the first instance of Posit~\\ref{pos:relational}: the same contents asserted as relations carry their stratifier, and what the counts mode pays is the cost of having forgotten the tree. D.8 is the relation at depth beyond coincidence: the family built to defeat the counts is decided by the remainder class in a few hundred operations, where the reading under the ceiling pays the order of the table."),
    dict(key="E", script="E_surplus.py", title="The Structural Surplus",
         scope="Section~\\ref{sec:surplus}", prog="E\\_surplus.py",
         discipline="One resolution under the envelope boundary yields the occupancy of the envelope; every reading is taken from that occupancy and is certified, by inspection of source, neither to re-resolve nor to construct a combination.",
         mapping=[("E.1 One resolution", "\\ref{sec:surplus}", "Thm.~\\ref{thm:reading}", "No reading calls the resolution; no reading constructs a combination."),
                  ("E.2--E.3 Spectrum; multiplicity", "\\ref{sec:surplus}", "Thm.~\\ref{thm:address}", "Twenty targets answered from one resolution; multiplicity carried, agreeing with the exhaustive reference."),
                  ("E.4 Certificate", "\\ref{sec:surplus}", "Thm.~\\ref{thm:envelope}(iv)", "Where no zero resides, a certificate with the distance to the nearest occupied address."),
                  ("E.5--E.6 Symmetry; composition", "\\ref{sec:surplus}", "Lemma~26.5; Def.~19.1", "$\\mathrm{occ}(t)=\\mathrm{occ}(-t)$ on the closed envelope; sub-envelopes compose by convolution, disjointness checked."),
                  ("E.7--E.8 Cost independence; comparison", "\\ref{sec:surplus}", "Thm.~\\ref{thm:reading}", "Work varies by $1.47\\times$ across answer classes; enumeration would need twenty passes for the spectrum alone.")],
         analysis="The surplus is what the same assertion, read once under the envelope boundary, answers beyond the question asked. Each reading is a read of the occupancy, not a second resolution, and each agrees with the exhaustive reference."),
]


def main():
    out = ["% generated by make_appendices.py -- do not edit", "\\begin{appendices}"]
    for ap in APPENDICES:
        tr = run_script(ap["script"])
        rows = verdict_rows(tr)
        npass = sum(1 for r in rows if r[2] == "PASS"); nfail = len(rows) - npass
        out.append(f"\\section{{{ap['title']}}}\\label{{app:{ap['key']}}}")
        out.append(f"\\emph{{Scope: {ap['scope']}.}} The suite for this appendix is the program \\texttt{{{ap['prog']}}}. {ap['discipline']}")
        out.append("")
        out.append("\\begingroup\\small\\renewcommand{\\arraystretch}{1.3}\n\\begin{longtable}{@{} p{0.17\\textwidth} p{0.07\\textwidth} p{0.22\\textwidth} p{0.38\\textwidth} @{}}\n\\caption{Protocol mapping for Appendix~\\ref{app:%s}.}\\label{tab:app%s_mapping}\\\\\n\\toprule\n\\textbf{Protocol} & \\textbf{Section} & \\textbf{Targeted results} & \\textbf{Structural mechanism} \\\\\n\\midrule\n\\endfirsthead\n\\toprule\n\\textbf{Protocol} & \\textbf{Section} & \\textbf{Targeted results} & \\textbf{Structural mechanism} \\\\\n\\midrule\n\\endhead\n\\bottomrule\n\\endfoot" % (ap["key"], ap["key"]))
        for proto, sec, targ, mech in ap["mapping"]:
            out.append(f"{proto} & {sec} & {targ} & {mech} \\\\")
        out.append("\\end{longtable}\\endgroup\n")
        out.append("\\begingroup\\small\\renewcommand{\\arraystretch}{1.25}\n\\begin{longtable}{@{} p{0.06\\textwidth} p{0.66\\textwidth} p{0.13\\textwidth} @{}}\n\\caption{Structural outputs and verdicts for Appendix~\\ref{app:%s}. %s.}\\label{tab:app%s_results}\\\\\n\\toprule\n\\textbf{Proto.} & \\textbf{Structural check} & \\textbf{Result} \\\\\n\\midrule\n\\endfirsthead\n\\toprule\n\\textbf{Proto.} & \\textbf{Structural check} & \\textbf{Result} \\\\\n\\midrule\n\\endhead\n\\bottomrule\n\\endfoot"
                   % (ap["key"], f"All {len(rows)} checks pass" if nfail == 0 else f"{npass} of {len(rows)} checks pass", ap["key"]))
        for proto, check, res in rows:
            out.append(f"{proto} & {tex_escape(check)} & {'Confirmed' if res == 'PASS' else 'FAILED'} \\\\")
        out.append("\\end{longtable}\\endgroup\n")
        out.append(f"\\paragraph{{Analysis.}} {ap['analysis']}\n")
    # Appendix F: verification programs
    g = run_script("dependency_graph.py"); q = run_script("quote_check.py")
    out.append("\\section{The Verification Programs}\\label{app:F}")
    out.append("\\emph{Scope: Sections~\\ref{sec:encoding}--\\ref{sec:falsifiability}.} Two programs take this document's source as their object. \\texttt{dependency\\_graph.py} extracts every labeled item and its Dependencies line, resolves every citation of \\PA{} by kind and number against the source text of \\PA{}, and verifies the graph (Theorem~\\ref{thm:graph}). \\texttt{quote\\_check.py} verifies every passage quoted from \\PA{} verbatim against that source text.")
    out.append("")
    census = g.split("TERMINAL CENSUS")[-1].split("VERDICTS")[0] if "TERMINAL CENSUS" in g else ""
    out.append("{\\footnotesize\\begin{verbatim}")
    out.append(fit("TERMINAL CENSUS" + census.rstrip()))
    out.append("\\end{verbatim}}")
    grows = [(m.group(1), m.group(2)) for m in re.finditer(r"\[(PASS|FAIL)\]\s+(.*)", g)]
    qline = re.search(r"(\d+) of (\d+) quotations found verbatim", q)
    out.append("\\begin{table}[htbp]\n\\centering\n\\caption{Verdicts of the verification programs.}\\label{tab:appF_results}\n\\renewcommand{\\arraystretch}{1.25}\n\\small\n\\begin{tabular}{@{} p{0.11\\textwidth} p{0.62\\textwidth} p{0.13\\textwidth} @{}}\n\\toprule\n\\textbf{Program} & \\textbf{Check} & \\textbf{Result} \\\\\n\\midrule")
    for res, desc in grows:
        out.append(f"graph & {tex_escape(desc)} & {'Confirmed' if res == 'PASS' else 'FAILED'} \\\\")
    if qline:
        out.append(f"quotations & {qline.group(1)} of {qline.group(2)} passages quoted from \\PA{{}} found verbatim in its source text & {'Confirmed' if qline.group(1) == qline.group(2) else 'FAILED'} \\\\")
    out.append("\\bottomrule\n\\end{tabular}\n\\end{table}\n")
    out.append("\\end{appendices}")
    with open(os.path.join(ROOT, "appendices.tex"), "w") as f:
        f.write("\n".join(out) + "\n")
    print("appendices.tex written")


if __name__ == "__main__":
    main()
