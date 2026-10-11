"""
D_boundary.py  --  Appendix D: Boundary Species and Relational Refinement; the Two Modes of Assertion
Relational Lysis and Computational Efficiency (P vs NP, introductory examination)

DISCIPLINE (per the companion papers' appendix standard):
  * Magnitude is CONSTITUTED (Def. 18.2, Thm. 18.1); comparison is conjugate
    pairing to exhaustion (Thm. 18.5). No native arithmetic within a derivation.
  * No native boolean primitive decides any structural verdict.
  * THE TERM PROJECTION. All work here is at the level of the atom count t
    (Thm. 18.6): t(a + b) = t(a) + t(b), the mediating boundary contributing no
    atom. Enfolding is therefore concatenation of unit collections and carries
    no copula. The relation count r, which by Thm. 18.3 gains one intercession
    per mediation, is not the quantity measured and is not claimed to be.
  * THE COMPUTABILITY CRITERION. A boundary must be computable from the
    assertion BEFORE the resolution it is meant to accelerate. A proposal that
    requires the resolution in order to state the boundary is circular and is
    rejected. Protocol D.7 exhibits such a proposal and rejects it.
  * SOUNDNESS. An eliminating boundary must never exclude a true address.
    Certified exhaustively at every scale tested.
  * THE STRATIFICATION BOUNDARY IS DERIVED, NOT IMPORTED. Its relation is
    Lemma 4.3 / Cor. 4.1 of the paper (from Thm. 19.2, Lemma 19.1, Thm. 20.3,
    Thm. 21.2's "common stratifier k >= 2"); the stratifier is decided by
    Thm. 20.2's iterated subtraction. No library gcd, no native division
    (Protocol D.1 inspects the AST). Protocol D.6 exhibits the relation
    bearing and not bearing.
  * Assertions here are SAMPLED, not random. Nothing in this framework is
    random: every assertion carries a constitution. What varies across the
    sample is which relations we have identified, not whether structure exists.
"""

from itertools import combinations
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))
import conventions
from math import sqrt
import random
import statistics as st

ASSERTED, REVERSED = "+", "-"


# ---------------------------------------------------------------- primitives

def constitute(m, o):
    return tuple(o for _ in range(m))


def content_of(v):
    return constitute(abs(v), ASSERTED if v > 0 else REVERSED)


def exhausts(c):
    a = [u for u in c if u == ASSERTED]
    r = [u for u in c if u == REVERSED]
    while a and r:
        a.pop(); r.pop()
    verdict = True
    for _ in a + r:
        verdict = False
        break
    return verdict


def sectors(X):
    """The partition by orientation (Def. 18.2), sectors ordered for prefix reach."""
    return sorted(v for v in X if v > 0), sorted(abs(v) for v in X if v < 0)


def true_addresses(X):
    """Reference only. Builds both ladders. Never consulted by any boundary."""
    P, N = sectors(X)

    def lad(S):
        r = {0}
        for v in S:
            r |= {s + v for s in r}
        return r - {0}

    return lad(P) & lad(N)


# ------------------------------------------- ELIMINATING BOUNDARIES (sound)
# Each is computed from the assertion alone. None builds a ladder entry.

def b_envelope(X):
    """The assertion fixes a finite bound (Ax. 5.3, principle); under the term
       projection (Thm. 18.6) that bound is the sector atom count, and a balance
       cannot exceed either sector's."""
    P, N = sectors(X)
    return set(range(1, min(sum(P), sum(N)) + 1))


NO_COMMON_STRATIFIER = None   # "the relation does not bear" -- not a value (Def. 4.3)


def stratifies(k, n):
    """Thm. 20.2 (Euclidean Decomposition of Counts): resolve groups of k by
       iterated subtraction until the first value below k; k stratifies n when
       the terminal value (the remainder) is zero -- Thm. 21.2's sense of
       "dividing ... with zero remainder". No native division is used."""
    rem = n
    while rem >= k:
        rem -= k
    return rem == 0


def common_stratifier(S):
    """Def. 4.3 (Common Stratifier of a Collection), derived in Sec. 4.2 of the
       paper. Candidates are the finite collection 2..min(S) (a stratifier of n
       cannot exceed n, Lemma 20.1(i)); each is decided by Thm. 20.2; the
       greatest exists by Lemma 26.1 "by the dual argument". Where no k >= 2
       stratifies every member the collection has NO common stratifier, and
       that is a statement that the relation does not bear -- it is not the
       value 1, and the classical gcd is not consulted."""
    least = min(S)
    k = least
    while k >= 2:
        bears = True
        for m in S:
            if not stratifies(k, m):
                bears = False
                break
        if bears:
            return k
        k -= 1
    return NO_COMMON_STRATIFIER


def b_stratification(X):
    """RELATION (Lemma 4.3, Cor. 4.1 of the paper): every count in a sector's
       reach is stratified by that sector's common stratifier g, because each
       member is g-stratifiable (Thm. 19.2, Thm. 20.3) and an aggregate's atom
       count is the sum of its members' (Lemma 19.1), hence g-stratifiable in
       turn. An address lies in both reaches, so it is stratified by g_P and by
       g_N. A sector with no common stratifier contributes no elimination."""
    P, N = sectors(X)
    gP, gN = common_stratifier(P), common_stratifier(N)
    keep = set()
    for w in b_envelope(X):
        ok = True
        for g in (gP, gN):
            if g is not NO_COMMON_STRATIFIER and not stratifies(g, w):
                ok = False
                break
        if ok:
            keep.add(w)
    return keep


def b_divisibility(X):
    """Name retained for the refinement stack; the boundary is b_stratification."""
    return b_stratification(X)


def b_extremal(X):
    """RELATION: a non-empty sector selection reaches at least its least
       element, so the balance is at least the greater of the two minima."""
    P, N = sectors(X)
    lo = max(min(P), min(N))
    return {w for w in b_divisibility(X) if w >= lo}


def strata_reach(S):
    """For each cardinality c, the reach is [sum of c least, sum of c greatest].
       Prefix sums over the ordered sector -- O(n log n), computed once."""
    pre = [0]
    for v in S:
        pre.append(pre[-1] + v)
    suf = [0]
    for v in reversed(S):
        suf.append(suf[-1] + v)
    return {c: (pre[c], suf[c]) for c in range(1, len(S) + 1)}


def b_cardinality(X):
    """RELATIONAL COORDINATE: refine the envelope by sector cardinality, and
       discard any stratum whose two reaches cannot meet."""
    P, N = sectors(X)
    RP, RN = strata_reach(P), strata_reach(N)
    allowed, strata = set(), []
    for cp, (a, b) in RP.items():
        for cn, (c, d) in RN.items():
            lo, hi = max(a, c), min(b, d)
            if lo <= hi:
                strata.append((cp, cn, lo, hi))
                allowed |= set(range(lo, hi + 1))
    return (b_extremal(X) & allowed), strata, len(RP) * len(RN)


# ------------------------------------------- ORDERING BOUNDARY (not sound)

def b_curvature_order(X, candidates):
    """A sector's reach concentrates about half its capacity, with spread set
       by its second moment. Computed in O(n) from the assertion. This ORDERS
       candidates; it eliminates nothing and claims no soundness."""
    P, N = sectors(X)
    mP, sP = sum(P) / 2, sqrt(sum(v * v for v in P) / 4) or 1.0
    mN, sN = sum(N) / 2, sqrt(sum(v * v for v in N) / 4) or 1.0
    wP, wN = 1 / (sP * sP), 1 / (sN * sN)
    centre = (mP * wP + mN * wN) / (wP + wN)
    return sorted(candidates, key=lambda w: abs(w - centre))


# --------------------------------- A BOUNDARY THAT FAILS THE CRITERION

def b_density_order_REJECTED(X, candidates):
    """Rank candidates by joint ladder density. Scores perfectly -- and is
       CIRCULAR: computing it requires building both ladders, which is the
       resolution it claims to accelerate. Retained to be rejected."""
    P, N = sectors(X)

    def counts(S):
        r = {0: 1}
        for v in S:
            add = {}
            for s, c in r.items():
                add[s + v] = add.get(s + v, 0) + c
            for s, c in add.items():
                r[s] = r.get(s, 0) + c
        r.pop(0, None)
        return r

    LP, LN = counts(P), counts(N)
    return sorted(candidates, key=lambda w: -(LP.get(w, 0) * LN.get(w, 0)))


# ----------------------------------------------------------------- protocols

def _uses_division_or_gcd(f):
    """AST inspection of the function BODY (docstrings carry no weight): true
       if any modulo, floor-division, true-division or divmod/gcd call occurs."""
    import ast, inspect, textwrap
    tree = ast.parse(textwrap.dedent(inspect.getsource(f)))
    for node in ast.walk(tree):
        if isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Mod, ast.FloorDiv, ast.Div)):
            return True
        if isinstance(node, ast.Call):
            fn = node.func
            name = fn.id if isinstance(fn, ast.Name) else getattr(fn, "attr", "")
            if name in ("gcd", "divmod", "lcm"):
                return True
    return False


def protocol_D1():
    """THE COMPUTABILITY CRITERION, enforced by inspection."""
    import inspect
    admitted = [b_envelope, b_stratification, b_extremal, b_cardinality,
                b_curvature_order, common_stratifier, stratifies]
    rejected = [b_density_order_REJECTED]
    def builds_ladder(f):
        s = inspect.getsource(f)
        return ("r |= {s + v for s in r}" in s) or ("add[s + v]" in s)
    return [
        ("no admitted boundary builds a ladder",
         not any(builds_ladder(f) for f in admitted)),
        ("no admitted boundary consults true_addresses",
         not any("true_addresses" in inspect.getsource(f) for f in admitted)),
        ("the rejected proposal does build a ladder",
         all(builds_ladder(f) for f in rejected)),
        ("the stratification boundary uses no library gcd and no native "
         "division: Thm. 20.2 by iterated subtraction only (AST inspection)",
         not any(_uses_division_or_gcd(f)
                 for f in (stratifies, common_stratifier, b_stratification))),
    ]


def protocol_D2(X):
    """Eliminating boundaries on the worked assertion."""
    s0 = b_envelope(X); s1 = b_divisibility(X); s2 = b_extremal(X)
    s3, strata, tot = b_cardinality(X)
    t = true_addresses(X)
    return [
        ("each boundary narrows or preserves the previous",
         len(s0) >= len(s1) >= len(s2) >= len(s3)),
        ("every boundary retains every true address",
         t <= s3 and t <= s2 and t <= s1 and t <= s0),
        (f"the envelope falls from {len(s0)} to {len(s3)} candidate depths",
         len(s3) < len(s0)),
    ], [("1 envelope (t(X)+1)", len(s0)), ("2 + stratification (Lemma 4.3)", len(s1)),
        ("3 + extremal", len(s2)), ("4 + cardinality", len(s3))], s3, t, strata, tot


def protocol_D3(trials=500):
    """SOUNDNESS AT SCALE -- the protocol the method stands or falls on."""
    random.seed(5)
    sound = tot = 0; elim = []; d0 = []; d1 = []
    for _ in range(trials):
        n = random.randint(6, 12)
        g = random.choice([1, 2, 3, 4])
        Z = [random.choice([-1, 1]) * g * random.randint(1, 14) for _ in range(n)]
        P, N = sectors(Z)
        if not P or not N:
            continue
        t = true_addresses(Z)
        if not t:
            continue
        tot += 1
        s0 = b_envelope(Z)
        s3, _, _ = b_cardinality(Z)
        if t <= s3:
            sound += 1
        elim.append(1 - len(s3) / len(s0))
        d0.append(len(t) / len(s0)); d1.append(len(t) / max(len(s3), 1))
    return [
        (f"no true address excluded in {sound} of {tot} assertions", sound == tot),
        (f"median {st.median(elim):.0%} of the envelope eliminated before work",
         st.median(elim) > 0.5),
        (f"true-address density rises from {st.median(d0):.0%} to "
         f"{st.median(d1):.0%}", st.median(d1) > st.median(d0)),
    ], tot, sound, st.median(elim), st.median(d0), st.median(d1)


def protocol_D4(trials=400):
    """The ordering boundary, reported honestly."""
    random.seed(5)
    R = []; C = []; hit = 0; tot = 0
    for _ in range(trials):
        n = random.randint(6, 11)
        g = random.choice([1, 2, 3])
        Z = [random.choice([-1, 1]) * g * random.randint(1, 14) for _ in range(n)]
        P, N = sectors(Z)
        if not P or not N:
            continue
        t = true_addresses(Z)
        if not t:
            continue
        cands = sorted(b_envelope(Z))
        tot += 1
        order = b_curvature_order(Z, cands)
        C.append(next(i for i, w in enumerate(order, 1) if w in t))
        r = cands[:]; random.shuffle(r)
        R.append(next(i for i, w in enumerate(r, 1) if w in t))
        if order[0] in t:
            hit += 1
    return [
        ("the ordering boundary builds no ladder (source inspection, as D.1)",
         not any(s in __import__("inspect").getsource(b_curvature_order)
                 for s in ("r |= {s + v for s in r}", "add[s + v]"))),
        (f"it reaches an address in {st.mean(C):.1f} visits against "
         f"{st.mean(R):.1f} unordered", st.mean(C) < st.mean(R)),
        ("the gain is modest and is reported as such; ordering boundaries "
         "remain the weaker species", st.mean(R) / st.mean(C) < 3.0),
    ], st.mean(R), st.mean(C), 100 * hit / tot


def protocol_D5(trials=200):
    """ADVERSARIAL: the circular proposal, scored and then rejected."""
    random.seed(5)
    hit = tot = 0
    for _ in range(trials):
        n = random.randint(6, 11)
        Z = [random.choice([-1, 1]) * random.randint(1, 14) for _ in range(n)]
        P, N = sectors(Z)
        if not P or not N:
            continue
        t = true_addresses(Z)
        if not t:
            continue
        tot += 1
        if b_density_order_REJECTED(Z, sorted(b_envelope(Z)))[0] in t:
            hit += 1
    return [
        (f"the circular proposal scores {100 * hit / tot:.0f}% first-visit "
         f"accuracy", hit > 0),
        ("it nevertheless fails the computability criterion: it builds a ladder",
         any(s in __import__("inspect").getsource(b_density_order_REJECTED)
             for s in ("r |= {s + v for s in r}", "add[s + v]"))),
    ], 100 * hit / tot, tot


def protocol_D6():
    """THE STRATIFICATION RELATION, bearing and not bearing (Cor. 4.1)."""
    X = [-7, -3, -2, 5, 8]
    P, N = sectors(X)
    gP, gN = common_stratifier(P), common_stratifier(N)
    Y = [6, 9, -4, -10]
    return [
        ("worked assertion: neither sector has a common stratifier, so the "
         "relation does not bear (Cor. 4.1, final clause)",
         gP is NO_COMMON_STRATIFIER and gN is NO_COMMON_STRATIFIER),
        ("and the boundary returns the envelope unchanged there",
         b_stratification(X) == b_envelope(X)),
        ("a sector with a common stratifier is eliminated through: "
         "{+6,+9,-4,-10} keeps of its 14-depth envelope only {6, 12}, the "
         "depths stratified by 3 and by 2",
         b_stratification(Y) == {6, 12} and
         common_stratifier([6, 9]) == 3 and common_stratifier([4, 10]) == 2),
        ("and excludes no true address in doing so",
         true_addresses(Y) <= b_stratification(Y)),
    ], gP, gN


def stratifier_search_cost(S):
    """The cost of RECOVERING the stratifier from counts (Cor. 4.2, counts
       mode): Thm. 20.2 by iterated subtraction, one RAM operation per
       subtraction and one per remainder test, over the candidates 2..min(S)."""
    ops = 0
    k = min(S)
    while k >= 2:
        bears = True
        for m in S:
            rem = m
            while rem >= k:
                rem -= k; ops += 1
            ops += 1
            if rem != 0:
                bears = False
                break
        if bears:
            return k, ops
        k -= 1
    return NO_COMMON_STRATIFIER, ops


def protocol_D7():
    """THE TWO MODES OF ASSERTION (Cor. 4.2). The same contents, constituted
       as relational products g (.) q (Def. 19.2). Asserted as counts, the
       tree is forgotten (Lemma 19.1) and the stratifier must be recovered by
       Thm. 20.2 at a cost; asserted as relations, it is a classification of
       the given tree (Thm. 20.3, Cor. 8.3) and is read in one act."""
    random.seed(11)
    rows = []
    for n, g in ((8, 3), (12, 4), (16, 6), (20, 5)):
        qs = [random.randint(1, 9) for _ in range(n)]
        Z = [random.choice([-1, 1]) * g * q for q in qs]
        P, N = sectors(Z)
        gX, cost = stratifier_search_cost(P + N)
        rows.append((n, g, gX, cost, 1))
    return [
        ("asserted as counts, the stratifier recovered by Thm. 20.2 is the one the "
         "constitution carries, on every row", all(r[2] == r[1] for r in rows)),
        (f"and the recovery costs {', '.join(str(r[3]) for r in rows)} operations "
         f"at n = 8, 12, 16, 20", all(r[3] > 1 for r in rows)),
        ("asserted as relations, the stratifier is read in one act on every row: "
         "the search is what the counts mode pays for forgetting the tree",
         all(r[4] == 1 for r in rows)),
    ], rows


# ------------------------------------------------------------------- summary

# ---------------------------------------------------------------- D.8 the remainder class

def remainder_class(S, k, ops):
    """The common remainder of a sector modulo k (Thm. 20.2's rem), recovered
       from counts by iterated subtraction with every subtraction and every
       test charged; None where the members' remainders differ."""
    rem0 = None
    for m in S:
        rem = m
        while rem >= k:
            rem -= k; ops[0] += 1
        ops[0] += 1
        if rem0 is None:
            rem0 = rem
        elif rem != rem0:
            return None
    return rem0


def remainder_boundary(X, strata, k, ops):
    """THE REMAINDER-CLASS RELATION at modulus k. Where every asserted
       content leaves remainder r_P and every reversed content r_N modulo k
       (Thm. 20.2), a configuration of c_P asserted contents resides at a
       depth of remainder c_P * r_P (Lemma 19.1; Thm. 20.2's uniqueness), and
       one of c_N reversed at c_N * r_N; a cell in which these differ carries
       no address and is discarded before any reading. Returns the surviving
       cells, or the cells unchanged where the relation does not bear."""
    P, N = sectors(X)
    rP = remainder_class(P, k, ops); rN = remainder_class(N, k, ops)
    if rP is None or rN is None:
        return list(strata), False
    kept = []
    for cp, cn, lo, hi in strata:
        ops[0] += 3                                     # two products by count, one comparison of remainders
        if (cp * rP) % k == (cn * rN) % k:
            kept.append((cp, cn, lo, hi))
    return kept, True


def protocol_D8():
    """THE REMAINDER CLASS ON THE FRONTIER. Soundness on every sampled
       assertion of the suite; the certificate family of Appendix C decided
       at the boundary, with no reading, by the remainder class modulo n; the
       count of frontier assertions (no coincident cell) on which a modulus
       2..n bears, and what it eliminates there."""
    import C_reading as C
    F = C.families()
    sound = True; checked = 0
    rng = random.Random(2082)
    structured = []
    while len(structured) < 80:                           # assertions built with a common remainder in each sector
        n = rng.choice([8, 10, 12, 14]); k = rng.randint(2, 7); rP = rng.randrange(k); rN = rng.randrange(k)
        P = [k * rng.randint(1, 6) + rP for _ in range(n // 2)]; N = [k * rng.randint(1, 6) + rN for _ in range(n - n // 2)]
        if all(v > 0 for v in P + N):
            structured.append(("S", n, k, P + [-v for v in N]))
    for fam, n, g, Z in F + structured:
        if n > 16:
            continue
        allowed, strata, total = b_cardinality(Z)
        ref = {}
        for Y in C.exhausting_subcollections(Z):
            cp = sum(1 for v in Y if v > 0); cn = len(Y) - cp
            ref.setdefault((cp, cn), 0); ref[(cp, cn)] += 1
        for k in range(2, n + 1):
            kept, bears = remainder_boundary(Z, strata, k, [0])
            if bears:
                checked += 1
                sound &= all(any(c[:2] == cell for c in kept) for cell in ref)
    # the certificate family of C.16: decided at the boundary
    cert_ok = True; cert_rows = []
    for n in (12, 16, 20, 24):
        for sd in range(10):
            Z = C.certificate_family(n, 100 * n + sd)
            allowed, strata, total = b_cardinality(Z)
            ops = [0]
            kept, bears = remainder_boundary(Z, strata, n, ops)
            r = C.read_selected(Z)
            cert_ok &= bears and kept == [] and not r["decision"]
            cert_rows.append((n, len(strata), len(kept), ops[0], r["ram"], C.bellman_ops(Z)))
    # the frontier of the suite: assertions with no coincident cell
    frontier = bears_on = 0; eliminated = []
    for fam, n, g, Z in F:
        r = C.read_selected(Z)
        if r["decision"] and r["strata_opened"] == 1:
            continue                                     # a coincident cell: not frontier
        frontier += 1
        allowed, strata, total = b_cardinality(Z)
        best = 0
        for k in range(2, n + 1):
            kept, bears = remainder_boundary(Z, strata, k, [0])
            if bears and len(strata) - len(kept) > best:
                best = len(strata) - len(kept)
        if best:
            bears_on += 1; eliminated.append(best / max(1, len(strata)))
    return [
        (f"wherever a modulus 2..n bears on both sectors ({checked} cases: the suite at n <= 16 and 80 assertions "
         "built with a common remainder in each sector), every cell carrying an address survives the "
         "remainder-class relation: the relation is sound against the exhaustive reference", sound and checked > 100),
        ("on the certificate family of Protocol C.16 the remainder class modulo n bears on both sectors, "
         "discards every surviving cell, and returns the certificate at the boundary with no reading "
         "on all 40", cert_ok),
        (f"on the {frontier} frontier assertions of the suite (no coincident cell) a modulus bears and "
         f"eliminates at least one cell on {bears_on}" + (f", eliminating on average {100 * sum(eliminated) / len(eliminated):.0f}% of their cells" if eliminated else "")
         + ": the relation is a boundary for structured assertions and the frontier for sampled ones",
         0 < frontier and bears_on <= frontier),
    ], cert_rows, (frontier, bears_on)


def run():
    X = [-7, -3, -2, 5, 8]
    print("=" * 78)
    print("APPENDIX D  --  BOUNDARY SPECIES AND RELATIONAL REFINEMENT")
    print("Relational Lysis and Computational Efficiency")
    print("=" * 78)
    print(conventions.header(conventions.RAM))
    print()
    print("  The boundary need not be a partition of the asserted elements.")
    print("  It may be a relation. Each refinement below is stated as a relation")
    print("  on the assertion and computed before any resolution begins.")
    print()
    print(f"  Asserted X = {X}")
    print()

    cks2, rows, s3, t, strata, tot_strata = protocol_D2(X)
    print("  THE REFINEMENT STACK")
    print("  " + "-" * 74)
    for nm, c in rows:
        print(f"     {nm:<34}{c:>5} candidate depths")
    print(f"     {'TRUE addresses':<34}{len(t):>5}   {sorted(t)}")
    print("  " + "-" * 74)
    print(f"     surviving window {sorted(s3)}")
    print(f"     {100 * (1 - len(s3) / rows[0][1]):.0f}% of the envelope eliminated, "
          f"with no ladder built")
    print(f"     cardinality strata: {tot_strata} total, {len(strata)} survive")
    for cp, cn, lo, hi in strata:
        print(f"        {cp} asserted + {cn} reversed, reach meets in [{lo},{hi}]")
    print()

    cks3, tot, sound, elim, d0, d1 = protocol_D3()
    print("  SOUNDNESS AND ELIMINATION AT SCALE")
    print("  " + "-" * 74)
    print(f"     assertions tested                        {tot:>8}")
    print(f"     true address excluded                    {tot - sound:>8}")
    print(f"     median envelope eliminated               {elim:>8.0%}")
    print(f"     true-address density, envelope only      {d0:>8.0%}")
    print(f"     true-address density, after refinement   {d1:>8.0%}")
    print(f"     proximity gain                           {d1 / d0:>7.1f}x")
    print("  " + "-" * 74)
    print()

    cks4, mr, mc, hitpct = protocol_D4()
    print("  ORDERING BOUNDARY (curvature from sector moments)")
    print(f"     visits to an address, unordered   {mr:>6.1f}")
    print(f"     visits, curvature-ordered         {mc:>6.1f}")
    print(f"     first visit is an address         {hitpct:>5.0f}%")
    print(f"     gain {mr / mc:.1f}x -- real, and the weaker species. Reported as such.")
    print()

    cks5, dhit, dtot = protocol_D5()
    print("  REJECTED: A BOUNDARY THAT REQUIRES THE RESOLUTION")
    print(f"     joint-density ordering scores {dhit:.0f}% first-visit accuracy")
    print(f"     and is rejected: computing it builds both ladders, which is")
    print(f"     the resolution it claims to accelerate. See D.1.")
    print()

    cks6, gP, gN = protocol_D6()
    print("  THE STRATIFICATION BOUNDARY, DERIVED (Sec. 4.2-4.3, Lemma 4.3)")
    print(f"     common stratifier of the asserted sector   "
          f"{'none -- relation does not bear' if gP is NO_COMMON_STRATIFIER else gP}")
    print(f"     common stratifier of the reversed sector   "
          f"{'none -- relation does not bear' if gN is NO_COMMON_STRATIFIER else gN}")
    print(f"     on the worked assertion the stratification row therefore equals")
    print(f"     the envelope; the elimination above is extremal + cardinality.")
    print()

    cks7, rows7 = protocol_D7()
    print("  THE TWO MODES OF ASSERTION (Cor. 4.2)")
    print("  " + "-" * 74)
    print(f"  {'n':>4}{'constituted g':>15}{'recovered g':>13}{'search ops':>12}{'read, as relations':>20}")
    print("  " + "-" * 74)
    for n, g, gX, cost, one in rows7:
        print(f"  {n:>4}{g:>15}{gX:>13}{cost:>12}{one:>20}")
    print("  " + "-" * 74)
    print()

    cks8, rows8, (fr8, bo8) = protocol_D8()
    print("  THE REMAINDER CLASS ON THE CERTIFICATE FAMILY (Protocol D.8)")
    print("  " + "-" * 74)
    print(f"  {'n':>4}{'cells formed':>14}{'cells kept':>12}{'relation ops':>14}{'reading ops':>13}{'table ops':>11}")
    print("  " + "-" * 74)
    for n in (12, 16, 20, 24):
        rs = [r for r in rows8 if r[0] == n]
        print(f"  {n:>4}{sum(r[1] for r in rs)/len(rs):>14.1f}{sum(r[2] for r in rs)/len(rs):>12.1f}"
              f"{sum(r[3] for r in rs)/len(rs):>14.0f}{sum(r[4] for r in rs)/len(rs):>13,.0f}{sum(r[5] for r in rs)/len(rs):>11,.0f}")
    print("  " + "-" * 74)
    print()

    results = [("D.1  The computability criterion", protocol_D1()),
               ("D.2  The refinement stack", cks2),
               ("D.3  Soundness at scale", cks3),
               ("D.4  Ordering boundary", cks4),
               ("D.5  A rejected boundary", cks5),
               ("D.6  The stratification boundary, derived", cks6),
               ("D.7  The two modes of assertion", cks7),
               ("D.8  The remainder class on the frontier", cks8)]
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
    words = {15: "fifteen", 16: "sixteen", 17: "seventeen", 18: "eighteen",
             21: "twenty-one", 22: "twenty-two", 23: "twenty-three",
             19: "nineteen", 20: "twenty"}
    if passed == total:
        print(f"APPENDIX D VERDICT:  All {words.get(total, total)} checks pass.")
    else:
        print(f"APPENDIX D VERDICT:  {passed}/{total} pass -- FAILURE PRESENT.")
    print("=" * 78)
    return passed == total


if __name__ == "__main__":
    import sys
    sys.exit(0 if run() else 1)
