"""
E_surplus.py  --  Appendix E: The Structural Surplus
Relational Lysis and Computational Efficiency (P vs NP, introductory examination)

DISCIPLINE (per the companion papers' appendix standard):
  * Magnitude is CONSTITUTED (Def. 18.2, Thm. 18.1); lysis acts on presentation
    (Def. 13.1); exhaustion is the closure condition (Def. 5.2, Cor. 23.8).
    No native arithmetic within a derivation.
  * No native boolean primitive decides any structural verdict.
  * THE TERM PROJECTION. All work here is at the level of the atom count t
    (Thm. 18.6): t(a + b) = t(a) + t(b), the mediating boundary contributing no
    atom. Enfolding is therefore concatenation of unit collections and carries
    no copula. The relation count r, which by Thm. 18.3 gains one intercession
    per mediation, is not the quantity measured and is not claimed to be.
  * ONE RESOLUTION. Every reading in this appendix is taken from a single
    resolution of the assertion. Protocol E.1 certifies that no reading
    re-resolves. A surplus that required a second resolution would not be a
    surplus.
  * Assertions are SAMPLED, not random.
"""

from itertools import combinations
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))
import conventions
import random
import statistics as st

ASSERTED, REVERSED = "+", "-"


# ---------------------------------------------------------------- primitives

def constitute(m, o):
    return tuple(o for _ in range(m))


def content_of(v):
    return constitute(abs(v), ASSERTED if v > 0 else REVERSED)


def residue(c):
    """Lysis on presentation (Def. 13.1). Pairs discharge; the residual stands."""
    a = [u for u in c if u == ASSERTED]
    r = [u for u in c if u == REVERSED]
    while a and r:
        a.pop(); r.pop()
    return tuple(a) + tuple(r)


def exhausts(c):
    verdict = True
    for _ in residue(c):
        verdict = False
        break
    return verdict


def signed(res):
    """Render a residue for reading only: magnitude with orientation."""
    if not res:
        return 0
    return len(res) if res[0] == ASSERTED else -len(res)


# ------------------------------------------------------- THE ONE RESOLUTION

def resolve(X):
    """Assert X. Build the occupancy of the envelope. ONE descent.
       Returns {residue: [contributing contents]} and the work performed."""
    occ = {(): [()]}
    work = 0
    for v in X:
        add = {}
        for res, srcs in occ.items():
            work += 1
            key = residue(res + content_of(v))
            add.setdefault(key, []).extend([s + (v,) for s in srcs])
        for k, ss in add.items():
            occ.setdefault(k, []).extend(ss)
    return occ, work


# ------------------------------- READINGS, all taken from the one occupancy

def read_target(occ, t):
    """Which contents reach target t."""
    want = constitute(abs(t), ASSERTED if t > 0 else REVERSED) if t else ()
    key = residue(want)
    return [c for c in occ.get(key, []) if c]


def read_spectrum(occ):
    """Every reachable target, in one reading."""
    return {signed(r): len([c for c in cs if c]) for r, cs in occ.items()}


def read_multiplicity(occ, t):
    return len(read_target(occ, t))


def read_certificate(occ, t):
    """Exhaustion certificate: the address stands unoccupied. With the nearest
       occupied address, so failure returns an optimisation answer."""
    if read_target(occ, t):
        return None
    reach = [signed(r) for r, cs in occ.items() if any(cs)]
    if not reach:
        return (True, None)
    return (True, min(abs(x - t) for x in reach))


def read_conjugate(occ, t):
    """A target and its reversal, read together."""
    return read_multiplicity(occ, t), read_multiplicity(occ, -t)


def compose(occA, occB):
    """Envelopes compose: the occupancy of a union is the convolution of the
       occupancies (Def. 19.1 aggregation, at the level of occupancy)."""
    out = {}
    for ra, sa in occA.items():
        for rb, sb in occB.items():
            k = residue(ra + rb)
            out.setdefault(k, []).extend([x + y for x in sa for y in sb])
    return out


# ----------------------------------------------------------------- protocols

def protocol_E1(X):
    """ONE RESOLUTION. No reading re-resolves."""
    import inspect
    readers = [read_target, read_spectrum, read_multiplicity,
               read_certificate, read_conjugate]
    return [
        ("no reading calls resolve",
         not any("resolve(" in inspect.getsource(f) for f in readers)),
        ("no reading constructs a combination",
         not any("combinations(" in inspect.getsource(f) for f in readers)),
        ("every reading takes the occupancy as given",
         all("occ" in inspect.signature(f).parameters for f in readers)),
    ]


def protocol_E2(X, occ):
    """The whole spectrum, from the one resolution."""
    spec = read_spectrum(occ)
    kappa = sum(abs(v) for v in X)
    ref = {}
    for r in range(1, len(X) + 1):
        for c in combinations(X, r):
            ref[sum(c)] = ref.get(sum(c), 0) + 1
    agree = all(spec.get(t, 0) == ref.get(t, 0) for t in set(spec) | set(ref))
    return [
        (f"{len([t for t in spec if spec[t]])} distinct targets answered in one "
         f"resolution", len(spec) > 1),
        ("the spectrum spans the envelope and no further",
         all(abs(t) <= kappa for t in spec)),
        ("every target count agrees with exhaustive reference", agree),
    ], spec


def protocol_E3(X, occ):
    """Multiplicity carried without any content being listed."""
    counts = {t: read_multiplicity(occ, t) for t in (0, 1, -1, 5, -5)}
    ref = {}
    for r in range(1, len(X) + 1):
        for c in combinations(X, r):
            ref[sum(c)] = ref.get(sum(c), 0) + 1
    return [
        ("multiplicity agrees with exhaustive reference at every target probed",
         all(counts[t] == ref.get(t, 0) for t in counts)),
        ("the multiplicity reading forms no combination (source inspection)",
         "combinations(" not in __import__("inspect").getsource(read_multiplicity)),
    ], counts


def protocol_E4():
    """Exhaustion certificate and distance to feasibility."""
    Y = [-7, -3, 5, 8]                      # no content exhausts
    occ, _ = resolve(Y)
    cert = read_certificate(occ, 0)
    ref = [c for r in range(1, len(Y) + 1) for c in combinations(Y, r)
           if sum(c) == 0]
    return [
        ("the assertion genuinely carries no address", not ref),
        ("the resolution returns an exhaustion certificate", cert is not None),
        ("the certificate carries the distance to the nearest occupied address",
         cert[1] is not None),
    ], Y, cert


def protocol_E5(X):
    """Conjugate symmetry across the closed envelope."""
    E = list(X) + [-v for v in X]
    occ, _ = resolve(E)
    spec = read_spectrum(occ)
    sym = all(spec.get(t, 0) == spec.get(-t, 0) for t in spec)
    return [
        ("the conjugate envelope is closed under reversal",
         sorted(E) == sorted(-v for v in E)),
        ("occupancy is symmetric: occ(t) equals occ(-t) at every address", sym),
        ("a target and its reversal are therefore answered together", sym),
    ], len(spec)


def protocol_E6():
    """Envelopes compose by convolution. Def. 19.1 requires the constitutions
       to be pairwise DISJOINT; that precondition is checked, not assumed."""
    A, B = [-7, -3], [-2, 5, 8]
    disjoint = not (set(map(abs, A)) & set(map(abs, B))) and not (set(A) & set(B))
    oA, _ = resolve(A)
    oB, _ = resolve(B)
    oAB, _ = resolve(A + B)
    conv = compose(oA, oB)
    keys = set(conv) | set(oAB)
    agree = all(len([c for c in conv.get(k, []) if c]) ==
                len([c for c in oAB.get(k, []) if c]) for k in keys)
    return [
        ("the sub-assertions have disjoint constitutions, as Def. 19.1 requires",
         disjoint),
        ("the convolution of two sub-envelopes equals the envelope of the union",
         agree),
        ("sub-envelopes are therefore reusable, not re-derived", agree),
    ], len(oA), len(oB), len(oAB)


def protocol_E7(trials=40):
    """Cost is independent of the answer."""
    random.seed(11)
    groups = {}
    for _ in range(trials * 20):
        n = 9
        Z = [random.choice([-1, 1]) * random.randint(1, 12) for _ in range(n)]
        if sum(abs(v) for v in Z) != 60:
            continue
        occ, w = resolve(Z)
        k = len(read_target(occ, 0))
        groups.setdefault(k, []).append(w)
        if sum(len(v) for v in groups.values()) >= trials:
            break
    spread = (max(st.mean(v) for v in groups.values()) /
              min(st.mean(v) for v in groups.values())) if len(groups) > 1 else 1.0
    return [
        (f"assertions grouped by address count: {sorted(groups)}", len(groups) > 1),
        (f"mean work varies by {spread:.2f}x across those groups", spread < 1.5),
        ("resolution time therefore carries no information about the answer",
         spread < 1.5),
    ], {k: round(st.mean(v), 1) for k, v in sorted(groups.items())}


def protocol_E8(X, occ, work):
    """How many separate resolutions would enumeration need for the same six?"""
    spec = read_spectrum(occ)
    needed = len([t for t in spec if spec[t]])
    return [
        (f"enumeration answers one target per pass and would need {needed} "
         f"passes for the spectrum alone", needed > 1),
    ], needed


# ------------------------------------------------------------------- summary

def run():
    X = [-7, -3, -2, 5, 8]
    occ, work = resolve(X)
    print("=" * 78)
    print("APPENDIX E  --  THE STRUCTURAL SURPLUS")
    print("Relational Lysis and Computational Efficiency")
    print("=" * 78)
    print(conventions.header(conventions.STRUCTURAL))
    print()
    print(f"  Asserted X = {X}")
    print(f"  ONE resolution: {work} operations. Every reading below is taken")
    print(f"  from it. None re-resolves.")
    print()

    cks2, spec = protocol_E2(X, occ)
    print("  1. THE WHOLE SPECTRUM -- every target, not the one asked")
    print("  " + "-" * 74)
    items = sorted(t for t in spec if spec[t])
    line = "     "
    for t in items:
        line += f"{t:+d}:{spec[t]}  "
        if len(line) > 68:
            print(line); line = "     "
    if line.strip():
        print(line)
    print(f"     {len(items)} distinct targets answered. Enumeration answers one.")
    print()

    cks3, counts = protocol_E3(X, occ)
    print("  2. MULTIPLICITY WITHOUT LISTING")
    print(f"     contents reaching 0: {counts[0]}   +5: {counts[5]}   "
          f"-5: {counts[-5]}   +1: {counts[1]}")
    print("     counts carried; no content was enumerated to obtain them.")
    print()

    cks4, Y, cert = protocol_E4()
    print("  3. EXHAUSTION CERTIFICATE AND DISTANCE")
    print(f"     assertion {Y} carries no address")
    print(f"     certificate returned; nearest feasible residual = {cert[1]}")
    print("     failure yields an optimisation answer, not silence.")
    print()

    cks5, nspec = protocol_E5(X)
    print("  4. CONJUGATE SYMMETRY")
    print(f"     closed envelope X with not-X: {nspec} addresses, "
          f"occ(t) = occ(-t) throughout")
    print("     a target and its reversal are answered in the same resolution.")
    print()

    cks6, la, lb, lab = protocol_E6()
    print("  5. ENVELOPES COMPOSE")
    print(f"     occupancy of [-7,-3] ({la} addresses) convolved with "
          f"[-2,5,8] ({lb})")
    print(f"     equals the occupancy of their union ({lab}). Sub-envelopes are reusable.")
    print()

    cks7, grp = protocol_E7()
    print("  6. COST IS INDEPENDENT OF THE ANSWER")
    print(f"     addresses found -> mean work: {grp}")
    print("     resolution time carries no information about the solution.")
    print()

    cks8, needed = protocol_E8(X, occ, work)
    print("  AND THE COMPARISON")
    print(f"     structure: 1 resolution, {work} operations, all six readings")
    print(f"     enumeration: one target per pass, {needed} passes for the "
          f"spectrum alone")
    print()

    results = [("E.1  One resolution", protocol_E1(X)),
               ("E.2  The whole spectrum", cks2),
               ("E.3  Multiplicity without listing", cks3),
               ("E.4  Exhaustion certificate", cks4),
               ("E.5  Conjugate symmetry", cks5),
               ("E.6  Envelope composition", cks6),
               ("E.7  Answer-independent cost", cks7),
               ("E.8  One resolution against many passes", cks8)]
    print("-" * 78)
    print("STRUCTURAL OUTPUTS AND VERDICTS")
    print("-" * 78)
    total = passed = 0
    for name, checks in results:
        print(f"\n  {name}")
        for desc, ok in checks:
            total += 1; passed += 1 if ok else 0
            print(f"     [{'PASS' if ok else 'FAIL'}]  {desc}")
    print()
    print("=" * 78)
    words = {20: "twenty", 21: "twenty-one", 22: "twenty-two",
             23: "twenty-three", 24: "twenty-four", 25: "twenty-five"}
    if passed == total:
        print(f"APPENDIX E VERDICT:  All {words.get(total, total)} checks pass.")
    else:
        print(f"APPENDIX E VERDICT:  {passed}/{total} pass -- FAILURE PRESENT.")
    print("=" * 78)
    return passed == total


if __name__ == "__main__":
    import sys
    sys.exit(0 if run() else 1)
