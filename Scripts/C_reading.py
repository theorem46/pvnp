"""
C_reading.py  --  Appendix C: Reading the Envelope by Depth, the Selected Partition,
                  and the Worked Comparison
Relational Lysis and Computational Efficiency (P vs NP, introductory examination)

THE PROBLEM, fixed for the whole suite.
  Given an asserted finite collection X of non-zero integers, which of its
  sub-collections exhaust to zero? Zero is exhaustion (Def. 5.2, Cor. 23.8).

THE RESOLUTION, built from Appendices B and D and nothing else.
  Let X denote the defined and not-X its reversal. The envelope X (x) not-X
  holds every configuration the contents can form, each resident at its own
  depth -- its count of units -- "independently of any act of selection,
  retrieval, or observation" (Thm. 15.1). Zero resides wherever both
  orientations are resident at one depth: an asserted configuration and a
  reversed configuration of equal count are a conjugate pair (Thm. 18.1),
  and a conjugate pair exhausts (Def. 5.2). The address of zero is that
  depth, and the sub-collection is what stands beneath the pair (Appendix B).
  The resolution never walks the tower from the top. It asserts the relations
  the boundary carries (Appendix D) -- the partition by orientation
  (Def. 18.2), the extremal floor, and the cardinality cells, the partition
  of the envelope by how many contents of each orientation a configuration
  holds -- and these name the depths at which zero is possible and the cells
  in which it can stand. In each cell four configurations reside whose depths
  the prefix and suffix sums already name (Thm. 15.1, Def. 19.1, Lemma 19.1):
  the least and the greatest on each side. Where two of them coincide, zero
  is read there with nothing else formed. THE SELECTING RELATION ranks
  coincident cells first, then fewest contents first; it is computed from
  the counts alone, before any reading. Then residence is read in the opened
  cells, and nowhere else. Where no admitted cell carries both orientations,
  no sub-collection exhausts: the certificate.

WHAT IS COUNTED.
  STRUCTURAL ACTS: one act per relation asserted at the boundary, one per
  cell opened, one per residence read (one configuration of a sector at one
  depth), one per match. Levels of magnitude are never counted.
  RAM ELEMENTARY OPERATIONS beside the acts, as the external anchor: every
  addition and comparison of the boundary, the selection and the reading,
  charged exactly as the classical anchors are charged.

THE ANCHORS, each written from its own literature and charged the same way.
  The exhaustive survey; the Bellman table over the signed range; the
  Horowitz-Sahni meet-in-the-middle. The near-linear tables of Koiliaris-Xu
  and Bringmann are cited for their bounds, which grow with t(X), and are not
  run.

WHAT IS CLAIMED.
  The boundary, asserted before any reading, reduces the configurations ever
  read from the full tower (2^n - 1) to the residences of the opened cells
  within their windows; where a coincident cell exists, zero is read in the
  first cell opened with two residence reads and one match. The suite reports
  on every assertion how many configurations were read against how many
  reside in the tower, certifies every address by pairing, certifies
  completeness against the exhaustive reference, and reports exactly the
  assertions on which no cell coincides. The structural reading's cost does
  not depend on the magnitudes of the contents; the table's does.

REPEATABILITY.
  Every seed is fixed; every run from any directory under python3 -I
  reproduces every figure; every address is certified by pairing.
"""

from itertools import combinations
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))
import conventions
import D_boundary as D
import random

ASSERTED, REVERSED = "+", "-"


# ============================================================ the boundary

def sort_cost(values, ram):
    """The order of a sector by count, charged: merge sort with every
       comparison counted (the n log n the order is quoted at). The order
       relation on counts is the chain of Theorem 10.2; asserting it on the
       sector is one act, and its comparisons are elementary operations."""
    if len(values) <= 1:
        return list(values)
    mid = len(values) // 2
    L1 = sort_cost(values[:mid], ram); R1 = sort_cost(values[mid:], ram)
    out = []; i = j = 0
    while i < len(L1) and j < len(R1):
        ram[0] += 1
        if L1[i] <= R1[j]:
            out.append(L1[i]); i += 1
        else:
            out.append(R1[j]); j += 1
    return out + L1[i:] + R1[j:]


def boundary(X, ram, order=None):
    """The relations asserted at the envelope, from Appendix D, with their
       cost charged. Returns the admitted windows (reporting only), the
       surviving cells, each as (cp, cn, lo, hi), coarsest first (fewest
       contents) unless an ordering relation is supplied (Appendix C asserts
       one), the number of cells formed, and the acts."""
    acts = 1                                              # orientation (Def. 18.2)
    # the order of each sector by count: one relation asserted, comparisons charged
    P = sort_cost([v for v in X if v > 0], ram); N = sort_cost([-v for v in X if v < 0], ram)
    acts += 1
    # extremal reach: the balance is at least the greater of the two minima
    floor = max(P[0], N[0]); acts += 1; ram[0] += 1
    # cardinality cells: prefix and suffix sums, one pass each sector (Def. 19.1, Lemma 19.1)
    RP, RN = D.strata_reach(P), D.strata_reach(N)
    ram[0] += 2 * (len(P) + len(N))
    strata = []; total = 0
    for cp, (a, b) in RP.items():
        for cn, (c, d) in RN.items():
            lo, hi = max(a, c), min(b, d); total += 1
            ram[0] += 1                                   # one comparison per cell: do the reaches meet
            if lo <= hi and hi >= max(lo, floor):
                strata.append((cp, cn, max(lo, floor), hi))
    acts += 1
    windows = [(lo, hi) for _, _, lo, hi in strata]
    strata = Cells(strata); strata.RP, strata.RN = RP, RN   # the prefix and suffix sums, computed once above
    if order is None:
        ranked = Cells(rank_by_contents(strata, len(X), ram)); ranked.RP, ranked.RN = RP, RN
        strata = ranked
    else:
        strata = order(X, strata, ram); acts += 1          # one relation asserted
    return windows, strata, total, acts


class Cells(list):
    """The surviving cells, carrying the prefix and suffix sums of the two
       sectors that named their windows (charged once, in boundary)."""
    pass


def rank_by_contents(strata, n, ram):
    """Fewest contents first: the cells placed in buckets by c_P + c_N
       (at most n - 1 buckets) and read out in order. Charged one placement
       per cell and one visit per bucket: k + n - 1. Within a bucket the
       cells keep their order of formation, c_P then c_N."""
    buckets = {}
    for cell in strata:
        buckets.setdefault(cell[0] + cell[1], []).append(cell)
    ram[0] += len(strata) + max(0, n - 1)
    return [cell for key in sorted(buckets) for cell in buckets[key]]


# ============================================================ residence

def residences(S, k, lo, hi, ram, acts, formed):
    """The configurations of exactly k contents of sector S resident at a
       depth in [lo, hi]. Each configuration formed is one residence read
       (one act). Every extension of a partial configuration is one addition
       and one comparison with hi; every completed configuration one
       comparison with lo. Configurations whose partial count already
       exceeds hi are not completed: the depth is closed above by the
       boundary. Cost <= 2 * sum_{j<=k} C(a, j) + C(a, k): each extension
       attempt is a distinct sub-collection of at most k contents (the break
       attempt included), each completion a sub-collection of k."""
    out = {}
    S = sorted(S)                                         # already in order of count (boundary)

    def extend(start, chosen, count):
        if len(chosen) == k:
            acts[0] += 1; ram[0] += 1; formed[0] += 1     # one comparison with the floor (count <= hi held at creation)
            if lo <= count:
                out.setdefault(count, chosen)
            return
        for i in range(start, len(S)):
            c = count + S[i]; ram[0] += 2                 # one addition, one comparison with hi
            if c > hi:
                break                                     # ordered: nothing further fits
            extend(i + 1, chosen + (S[i],), c)

    extend(0, (), 0)
    return out


def formation_table(a, ram):
    """F[c] = 2 * sum_{j<=c} C(a, j) + C(a, c): the bound on the operations of
       residences(S, c, lo, hi) for a sector of a contents. Built once per
       sector from the counts by the multiplicative formula
       C(a, j+1) = C(a, j)(a - j)/(j + 1): six operations per entry (the
       subtraction, the product, the quotient, the running sum, the doubling,
       the entry's sum)."""
    F = [0] * (a + 1); C_ = 1; acc = 0
    for j in range(1, a + 1):
        C_ = C_ * (a - j + 1) // j; acc += C_
        F[j] = 2 * acc + C_
        ram[0] += 6
    return F


def reach_reading(P, N, m, ram, acts, trace=None):
    """THE CEILING'S READING: the reach of each sector read to the floor m,
       as the table reads it and charged as the table is charged. One array
       of m + 1 cells per sector; each content of the sector, in the order of
       Sigma, is swept against every cell once (one read per cell), and where
       a cell is occupied its residence is mediated with the content (Def.
       18.1; Lemma 19.1 places the mediation at the sum of the depths): one
       addition, one comparison with the floor, and one write where the sum
       is within it. Residences at one depth stand at one stratum and one is
       kept (the content beneath the first). At most |S|(m + 1) reads and
       3|S|m further operations per sector, so n(4m + 1) for both, plus m + 1
       reads for the match by depth: rho(X) = n(4m + 1) + m + 1.
       Against the table run in the same order over the full range: every
       cell this reading occupies when a content is swept, the table has
       occupied too (its sums include the sector's own), and the table's
       target is always within its range; so each operation here is matched
       by one there, and the table has n(t - m) further reads besides."""
    R = {}; nread = 0
    for name, S in (("asserted", P), ("reversed", N)):
        reach = [None] * (m + 1)
        for x in sorted(S, reverse=True):
            for i in range(m, -1, -1):                    # swept downward: x used once
                ram[0] += 1                               # the read
                if reach[i] is not None:
                    e = i + x; ram[0] += 2                # the addition, the comparison with the floor
                    if e <= m and reach[e] is None:
                        reach[e] = reach[i] + (x,); ram[0] += 1; nread += 1; acts[0] += 1
            if x <= m and reach[x] is None:
                reach[x] = (x,); ram[0] += 1; nread += 1; acts[0] += 1
        R[name] = reach
    found = {}
    for d in range(1, m + 1):                             # one read per depth for the match
        ram[0] += 1; acts[0] += 1
        if R["asserted"][d] is not None and R["reversed"][d] is not None:
            found[d] = tuple(R["asserted"][d]) + tuple(-v for v in R["reversed"][d])
    if trace is not None:
        trace.append(f"  reach of the asserted sector: {sum(1 for c in R['asserted'] if c)} depths; of the reversed: "
                     f"{sum(1 for c in R['reversed'] if c)}; zero resides at {sorted(found)}")
    return found, nread


def resolve(X, trace=None, all_addresses=False, order=None):
    """Read the envelope by depth under the asserted boundary.
       Returns dict: decision, addresses (depth -> content), acts, ram,
       reads (configurations formed), cell_acts (acts within opened cells,
       the opening excluded), strata_opened, strata_total, tower, ceiling."""
    ram = [0]; acts = [0]
    windows, strata, total, bacts = boundary(X, ram, order)
    P, N = D.sectors(X)                                   # the ordered sectors (ordered and charged in boundary)
    acts[0] += bacts
    formed = [0]; cell_acts = [0]
    found = {}
    opened = 0
    if trace is not None:
        trace.append(f"boundary: sectors P={P} N={N}; admitted windows "
                     f"{sorted(set(windows))}; strata surviving "
                     f"{len(strata)} of {total}")
    tested = isinstance(strata, Ranked)          # the selection has tested every cell's ends
    if tested and all_addresses and strata.first_coincides and len(strata) > 1:
        strata = Ranked([strata[0]] + rank_by_contents(list(strata[1:]), len(X), ram), True)
    m = Breach = None; cumulative = 0; FP = FN = None

    def result(decision, ceiling):
        return dict(decision=decision, addresses=found, acts=acts[0], ram=ram[0],
                    reads=formed[0], cell_acts=cell_acts[0], strata_opened=opened,
                    strata_total=total, tower=2 ** len(X) - 1, ceiling=ceiling)

    def match_interior(RP, RN, cp, cn, lo, hi, label):
        if trace is not None:
            trace.append(f"  {label} {cp} asserted + {cn} reversed, depths [{lo},{hi}]: "
                         f"asserted resident at {sorted(RP)}, reversed resident at {sorted(RN)}")
        for w in RP:
            ram[0] += 1; acts[0] += 1                     # one match test per asserted residence, in any order
            if w in RN:
                content = tuple(RP[w]) + tuple(-v for v in RN[w])
                new = w not in found
                found.setdefault(w, content)
                if trace is not None and new:
                    trace.append(f"     depth {w}: both orientations resident -- zero as "
                                 f"exhaustion; beneath: {list(content)}")
                if not all_addresses:
                    return True
        return False

    for idx, (cp, cn, lo, hi) in enumerate(strata):
        opened += 1; acts[0] += 1
        before = acts[0]
        if tested and not (idx == 0 and strata.first_coincides):
            # THE CEILING. The selection has already compared this cell's
            # extremal residences (they do not coincide). Before its interior
            # is read, the cells' formation bound, cumulative over the cells
            # opened, is compared with the bound of reading the reach of both
            # sectors to the floor; all from counts. Where the cells would
            # cost more than the reach, the reach is read instead, once.
            if m is None:
                # THE ALLOWANCE, from counts: the table's reads the floor saves, n(t - m),
                # less the boundary already paid and the ceiling's own bookkeeping.
                # Interiors are read only while their formation bounds fit within it,
                # so the whole resolution never exceeds the table where the allowance
                # is non-negative (Thm. reading (iv)).
                tP, tN = sum(P), sum(N); m = min(tP, tN); ram[0] += 1   # the sector totals are the last suffix sums
                Bx = ram[0]
                Breach = len(X) * (tP + tN - m) - (m + 1) - Bx - (5 * len(strata) + 6 * len(X) + 9); ram[0] += 8
                FP = formation_table(len(P), ram); FN = formation_table(len(N), ram)
            b = FP[cp] + FN[cn]; ram[0] += 3              # two table reads, one addition
            cumulative += b; ram[0] += 1
            ram[0] += 1                                   # the comparison with the allowance
            if cumulative > Breach:
                if trace is not None:
                    trace.append(f"  cell {cp} asserted + {cn} reversed: formation bound {b} brings the "
                                 f"cells to {cumulative}, above the allowance {Breach}: the reach of "
                                 f"both sectors is read to the floor {m}")
                found_r, nread = reach_reading(P, N, m, ram, acts, trace)
                formed[0] += nread
                for w in sorted(found_r):
                    found.setdefault(w, found_r[w])
                cell_acts[0] += acts[0] - before
                return result(bool(found), True)
            RP = residences(P, cp, lo, hi, ram, acts, formed)
            RN = residences(N, cn, lo, hi, ram, acts, formed)
            hit = match_interior(RP, RN, cp, cn, lo, hi, "cell")
            cell_acts[0] += acts[0] - before
            if hit:
                return result(True, False)
            continue
        # THE EXTREMAL RESIDENCES FIRST. The least cp asserted contents and
        # the least cn reversed contents are configurations that reside
        # (Thm. 15.1, Def. 19.1) at the depths the prefix sums already name
        # (Lemma 19.1); likewise the greatest. Where the two least, or the two
        # greatest, stand at one depth, they are a conjugate pair there
        # (Thm. 18.1): zero is read with two residence reads, one match, and no other
        # configuration formed. The relation names the depth; nothing is walked.
        for which, pick in (("least", lambda S, k: tuple(S[:k])),
                            ("greatest", lambda S, k: tuple(S[-k:]))):
            a, b = pick(P, cp), pick(N, cn)
            acts[0] += 2; formed[0] += 2; ram[0] += (cp - 1) + (cn - 1)   # the two residences: their additions
            da, db = sum(a), sum(b)
            acts[0] += 1; ram[0] += 1                     # the match: one equality test
            # no window test: coincident least ends stand at the cell's lo (>= floor),
            # coincident greatest ends at its hi; both are within the window
            if da == db:
                content = a + tuple(-v for v in b)
                found.setdefault(da, content)
                if trace is not None:
                    trace.append(f"  stratum {cp} asserted + {cn} reversed, depths [{lo},{hi}]: "
                                 f"the {which} residences coincide at depth {da} -- zero as "
                                 f"exhaustion; beneath: {list(content)}")
                if not all_addresses:
                    cell_acts[0] += acts[0] - before
                    return result(True, False)
        RP = residences(P, cp, lo, hi, ram, acts, formed)
        RN = residences(N, cn, lo, hi, ram, acts, formed)
        hit = match_interior(RP, RN, cp, cn, lo, hi, "stratum")
        cell_acts[0] += acts[0] - before
        if hit:
            return result(True, False)
    return result(bool(found), False)


# ============================================================ the selection

def coincides(cp, cn, lo, hi, RP, RN):
    """The extremal residences of a cell coincide: the two least, or the two
       greatest, configurations stand at one depth within the window."""
    (lpP, hpP), (lpN, hpN) = RP[cp], RN[cn]
    # Two equality tests. No window test is needed: if the least ends coincide
    # at w then w = lo of the cell and w >= min P, min N, hence w >= floor; if
    # the greatest ends coincide at w then w = hi >= lo. Both lie in the window.
    return lpP == lpN or hpP == hpN


def select(X, strata, ram):
    """THE SELECTING RELATION: coincident cells first, then coarsest first.
       Computed from the prefix and suffix sums alone. Charged: one
       comparison per cell per end, and the ranking comparisons."""
    RP, RN = strata.RP, strata.RN                   # the sums the boundary formed; nothing recomputed
    keyed = []
    for cp, cn, lo, hi in strata:
        ram[0] += 2                                 # two equality tests: the least ends, the greatest ends
        c = 0 if coincides(cp, cn, lo, hi, RP, RN) else 1
        keyed.append((c, cp + cn, (cp, cn, lo, hi)))
    if not keyed:
        return Ranked([], False)
    # the least-keyed cell in one pass: k - 1 comparisons
    least = keyed[0]
    for item in keyed[1:]:
        ram[0] += 1
        if item[:2] < least[:2]:
            least = item
    rest = [item[2] for item in keyed if item is not least]
    if least[0] == 0:
        # the least cell coincides: zero is read there and the resolution ends;
        # the remaining cells are ranked only where every address is wanted,
        # and that ranking is charged where it is performed (resolve).
        return Ranked([least[2]] + rest, True)
    return Ranked([least[2]] + rank_by_contents(rest, len(X), ram), False)


class Ranked(list):
    """The ordered cells, carrying whether the first coincides."""
    def __init__(self, cells, first_coincides):
        super().__init__(cells); self.first_coincides = first_coincides


def read_selected(X, trace=None):
    """Appendix B's reading, under the asserted selection."""
    return resolve(X, trace=trace, order=select)


def read_coarsest(X, trace=None):
    return resolve(X, trace=trace)


# ============================================================ anchors

def exhausting_subcollections(X):
    out = []
    for r in range(1, len(X) + 1):
        for c in combinations(range(len(X)), r):
            if sum(X[i] for i in c) == 0:
                out.append(tuple(X[i] for i in c))
    return out


def survey_ops(n):
    return n * 2 ** (n - 1) + 2 ** n - 1


def bellman_ops(X):
    """Bellman (1957): one cell per sum of the signed range, each content
       visited against every cell once, in place (cells swept away from the
       content's direction so that a content is used once). Charged under the
       one convention: one read per cell; and for each occupied cell one
       addition (the target index), one comparison (the bound), and one write
       where the target lies in the range. n(t + 1) reads, and at most three
       further operations per occupied cell. The contents are taken in the
       order of the assertion (Sigma, eldest first), the order every
       resolution compared receives."""
    lo = sum(v for v in X if v < 0); hi = sum(v for v in X if v > 0)
    size = hi - lo + 1; ops = 0
    reach = bytearray(size); origin = -lo
    for v in sorted(X, key=lambda u: (-abs(u), u < 0)):   # the order of the assertion: Sigma, eldest first
        order = range(size - 1, -1, -1) if v > 0 else range(size)
        for i in order:
            ops += 1                                      # the read
            if reach[i]:
                j = i + v; ops += 2                       # the addition, the bound comparison
                if 0 <= j < size:
                    reach[j] = 1; ops += 1                # the write
        reach[v + origin] = 1; ops += 1                   # the content alone
    return ops


def bellman_decision(X):
    """The table's decision, exact."""
    lo = sum(v for v in X if v < 0); hi = sum(v for v in X if v > 0)
    size = hi - lo + 1; reach = bytearray(size); origin = -lo
    for v in sorted(X, key=lambda u: (-abs(u), u < 0)):
        order = range(size - 1, -1, -1) if v > 0 else range(size)
        for i in order:
            if reach[i]:
                j = i + v
                if 0 <= j < size:
                    reach[j] = 1
        reach[v + origin] = 1
    return bool(reach[origin])


def exhausts(content):
    a = [ASSERTED] * sum(v for v in content if v > 0)
    r = [REVERSED] * sum(-v for v in content if v < 0)
    while a and r:
        a.pop(); r.pop()
    for _ in a + r:
        return False
    return True




def mitm_ops(X):
    """Horowitz-Sahni (1974) meet-in-the-middle, written from the paper: split
       the contents into halves, form every sub-collection sum of each half
       (2^(n/2) each, r additions for a sub-collection of r members), sort both
       lists (comparisons charged as n log n insertion-count), then sweep the
       two sorted lists once for a pair summing to zero with both parts
       nonempty handled by excluding the empty-empty pair. Returns ops."""
    n = len(X); h = n // 2
    L, R = X[:h], X[h:]
    ops = 0
    def sums(S):
        nonlocal ops
        out = []
        for r in range(0, len(S) + 1):
            for c in combinations(range(len(S)), r):
                s = 0
                for i in c:
                    s += S[i]; ops += 1
                out.append((s, r))
        return out
    A, Bb = sums(L), sums(R)
    def sort_count(lst):
        """Merge sort with every comparison charged: the n log n the method
           is quoted at, not a quadratic sort that would overstate its cost."""
        nonlocal ops
        if len(lst) <= 1:
            return list(lst)
        mid = len(lst) // 2
        L1 = sort_count(lst[:mid]); R1 = sort_count(lst[mid:])
        out = []; i = j = 0
        while i < len(L1) and j < len(R1):
            ops += 1
            if L1[i][0] <= R1[j][0]:
                out.append(L1[i]); i += 1
            else:
                out.append(R1[j]); j += 1
        out.extend(L1[i:]); out.extend(R1[j:])
        return out
    A = sort_count(A); Bb = sort_count(Bb)
    i, j = 0, len(Bb) - 1
    while i < len(A) and j >= 0:
        ops += 1
        s = A[i][0] + Bb[j][0]; ops += 1
        if s == 0 and (A[i][1] + Bb[j][1]) > 0:
            return ops
        if s < 0:
            i += 1
        else:
            j -= 1
    return ops

# ============================================================ families

def assertion(n, g=1, seed=0):
    r = random.Random(seed)
    while True:
        qs = [r.randint(1, 9) for _ in range(n)]
        sg = [r.choice([-1, 1]) for _ in range(n)]
        Z = [o * g * q for o, q in zip(sg, qs)]
        if [v for v in Z if v > 0] and [v for v in Z if v < 0]:
            return Z


def assertion_distinct(n, hi, seed=0):
    r = random.Random(seed)
    while True:
        mags = r.sample(range(1, hi + 1), n)
        Z = [r.choice([-1, 1]) * m for m in mags]
        if [v for v in Z if v > 0] and [v for v in Z if v < 0]:
            return Z


def families():
    F = []
    for n in (6, 8, 10, 12, 14, 16, 18, 20):
        for s in range(25):
            F.append(("A", n, 1, assertion(n, 1, seed=1000 * n + s)))
    for n, hi in ((6, 20), (8, 30), (10, 40), (12, 50), (14, 60), (16, 80),
                  (18, 100), (20, 120)):
        for s in range(25):
            F.append(("B", n, hi, assertion_distinct(n, hi, seed=5000 * n + s)))
    return F


WORKED = [-7, -3, -2, 5, 8]
SECOND = [10, -8, -3, 2, 1]


# ============================================================ protocols

def protocol_C1():
    """THE TWO TRACES."""
    out = []
    for X in (WORKED, SECOND):
        tr = []
        r = resolve(X, trace=tr, all_addresses=True)
        out.append((X, tr, r))
    w, s = out
    checks = [
        ("worked assertion: zero resides at depth 5 and nowhere else",
         sorted(w[2]["addresses"]) == [5]),
        ("beneath it stands {5, -3, -2}, certified to exhaust by pairing",
         set(w[2]["addresses"][5]) == {5, -3, -2} and exhausts(w[2]["addresses"][5])),
        (f"of 31 configurations in the tower, {w[2]['reads']} were read",
         w[2]["reads"] < 31),
        ("the tower was never walked from the top: no configuration outside the "
         "admitted strata and depths was formed", w[2]["strata_opened"] <= w[2]["strata_total"]),
        ("second assertion: zero resides at depths 3 and 11",
         sorted(s[2]["addresses"]) == [3, 11]),
        ("beneath them stand {-3, 2, 1} and {10, 1, -8, -3}, both certified",
         set(s[2]["addresses"][3]) == {-3, 2, 1} and set(s[2]["addresses"][11]) == {10, 1, -8, -3}
         and all(exhausts(c) for c in s[2]["addresses"].values())),
        (f"of 31 configurations in the tower, {s[2]['reads']} were read",
         s[2]["reads"] < 31),
    ]
    return checks, out


def protocol_C2(F):
    """COMPLETENESS AND FIDELITY against the exhaustive reference."""
    agree = tot = cert = 0
    for fam, n, g, Z in F:
        if n > 16:
            continue
        tot += 1
        r = resolve(Z)
        ref = exhausting_subcollections(Z)
        if r["decision"] == bool(ref):
            agree += 1
        if all(exhausts(c) for c in r["addresses"].values()):
            cert += 1
    return [
        (f"the decision agrees with the exhaustive reference on all {tot} assertions "
         f"with n <= 16: where the reading finds no zero, none exists", agree == tot),
        ("every address returned is certified to exhaust by pairing", cert == tot),
    ], tot


def protocol_C3(F):
    """THE SEARCH SPACE THE BOUNDARY LEAVES, on both families."""
    rows = {}
    for fam, n, g, Z in F:
        r = resolve(Z)
        row = rows.setdefault((fam, n, g), dict(total=0, found=0, reads=[], acts=[],
                                                ram=[], frac=[], bell=[], opened=[],
                                                stot=[]))
        row["total"] += 1
        row["found"] += 1 if r["decision"] else 0
        row["reads"].append(r["reads"]); row["acts"].append(r["acts"])
        row["ram"].append(r["ram"]); row["frac"].append(r["reads"] / r["tower"])
        row["bell"].append(bellman_ops(Z)); row["opened"].append(r["strata_opened"])
        row["stot"].append(r["strata_total"])
    worst = max(max(v["frac"]) for v in rows.values())
    worst10 = max(max(v["frac"]) for (fam, n, g), v in rows.items() if n >= 10)
    checks = [
        (f"the worst fraction of the tower read on any assertion is {worst:.1%} "
         f"(at n = 6, where the extremal reads are most of the tower); from n = 10 "
         f"upward the worst is {worst10:.2%}", worst10 < 0.1),
        ("the reads do not grow with the magnitudes: family B's widening range "
         "leaves the mean reads at n = 20 within 10x of family A's",
         (sum(rows[('B', 20, 120)]['reads']) / 25) <
         10 * max(1, sum(rows[('A', 20, 1)]['reads']) / 25)),
        ("the Bellman table grows with the magnitudes: family B's mean table at "
         "n = 20 is more than 5x family A's",
         (sum(rows[('B', 20, 120)]['bell']) / 25) > 5 * (sum(rows[('A', 20, 1)]['bell']) / 25)),
    ]
    return checks, rows


def protocol_C4(F):
    """DETERMINISM AND DISCIPLINE."""
    same = True
    for fam, n, g, Z in F[::9]:
        t1, t2 = [], []
        r1 = resolve(Z, trace=t1); r2 = resolve(Z, trace=t2)
        same &= (t1 == t2 and r1 == r2)
    import inspect
    src = (inspect.getsource(resolve) + inspect.getsource(residences) + inspect.getsource(boundary)
           + inspect.getsource(reach_reading) + inspect.getsource(select) + inspect.getsource(formation_table))
    import ast
    tree = ast.parse(inspect.getsource(resolve))
    fors = [nd for nd in ast.walk(tree) if isinstance(nd, ast.For)]
    def calls(node, name):
        return sum(1 for nd in ast.walk(node) if isinstance(nd, ast.Call)
                   and isinstance(nd.func, ast.Name) and nd.func.id == name)
    in_loop = sum(calls(f, "residences") for f in fors), sum(calls(f, "reach_reading") for f in fors)
    in_all = calls(tree, "residences"), calls(tree, "reach_reading")
    outside = sum(calls(ast.parse(inspect.getsource(fn)), "residences") + calls(ast.parse(inspect.getsource(fn)), "reach_reading")
                  for fn in (boundary, select, formation_table, reach_reading, residences))
    return [
        ("repeated runs produce identical traces and results", same),
        ("the resolution consults no random source and no reference answer "
         "(source inspection)", "random" not in src and "exhausting_subcollections" not in src
         and "true_addresses" not in src),
        ("no configuration is formed outside an admitted stratum: residence is read only "
         "inside the strata loop, by the interior reading of an opened cell or by the reach "
         "reading the ceiling selects there (source inspection)",
         in_loop == in_all == (4, 1) and outside == 0),
    ]


# ============================================================ protocols

def protocol_C5():
    """THE SELECTION ON THE TWO ASSERTIONS, with the ranking shown."""
    out = []
    for X in (WORKED, SECOND):
        P, N = D.sectors(X)
        _, strata, total, _ = boundary(X, [0])
        RP, RN = D.strata_reach(P), D.strata_reach(N)
        ranked = select(X, strata, [0])
        rows = [(cp, cn, lo, hi, coincides(cp, cn, lo, hi, RP, RN), RP[cp], RN[cn])
                for cp, cn, lo, hi in ranked]
        tr = []
        r = read_selected(X, trace=tr)
        out.append((X, rows, tr, r))
    w, s = out
    checks = [
        ("worked assertion: the counts select 'one asserted against two reversed' "
         "because its least residences coincide: 5 and 3 + 2 both stand at depth 5",
         w[1][0][:2] == (1, 2) and w[1][0][4] and w[1][0][5][0] == 5 == w[1][0][6][0]),
        ("zero is read there at depth 5 in the first cell opened: two residence reads "
         "and one match, no other configuration formed",
         w[3]["decision"] and sorted(w[3]["addresses"]) == [5]
         and w[3]["strata_opened"] == 1 and w[3]["cell_acts"] == 3 and w[3]["reads"] == 2),
        ("second assertion: the counts select 'two asserted against one reversed' "
         "because its least residences coincide: 1 + 2 and 3 both stand at depth 3",
         s[1][0][:2] == (2, 1) and s[1][0][4] and s[1][0][5][0] == 3 == s[1][0][6][0]),
        ("zero is read there at depth 3 in the first cell opened, with two residence "
         "reads and one match",
         s[3]["decision"] and sorted(s[3]["addresses"]) == [3]
         and s[3]["strata_opened"] == 1 and s[3]["cell_acts"] == 3 and s[3]["reads"] == 2),
    ]
    return checks, out


def protocol_C6():
    """COMPUTABILITY: the selection consults counts only, never a residence."""
    import inspect
    src = inspect.getsource(select) + inspect.getsource(coincides)
    return [
        ("the selecting relation forms no configuration and reads no residence "
         "(no call to residences, resolve, combinations or the reference)",
         not any(t in src for t in ("residences(", "resolve(", "combinations(",
                                     "exhausting_subcollections", "true_addresses"))),
        ("it consults the prefix and suffix sums of the sectors and the cell "
         "windows only", "strata.RP, strata.RN" in src and "RP[cp]" in src and "lo, hi" in src),
    ]


def protocol_C7(F):
    """THE SELECTED PARTITION ON THE FAMILIES: where zero is read, and what
       the selection costs against coarsest-first and the tower."""
    rows = {}
    first = second = later = none = 0
    worse = 0; total = 0
    for fam, n, g, Z in F:
        rs = read_selected(Z); rc = read_coarsest(Z)
        key = (fam, n, g)
        row = rows.setdefault(key, dict(total=0, zero=0, first=0, reads_s=[],
                                        reads_c=[], tower=2 ** n - 1, opened=[]))
        row["total"] += 1; total += 1
        row["reads_s"].append(rs["reads"]); row["reads_c"].append(rc["reads"])
        if rs["decision"]:
            row["zero"] += 1; row["opened"].append(rs["strata_opened"])
            if rs["strata_opened"] == 1:
                first += 1; row["first"] += 1
            elif rs["strata_opened"] == 2:
                second += 1
            else:
                later += 1
        else:
            none += 1
        if rs["reads"] > rc["reads"]:
            worse += 1
    carry = first + second + later
    coinc = sum(1 for fam, n, g, Z in F
                if any("coincide" in t for t in (lambda tr: (read_selected(Z, trace=tr), tr)[1])([])))
    checks = [
        (f"of {carry} assertions carrying a zero, it is read in the first cell the "
         f"counts select on {first}, in the second on {second}, later on {later}",
         first + second + later == carry),
        (f"zero is read directly from coincident extremal residences, with nothing "
         f"else formed, on {coinc} of {carry}", coinc > 0),
        (f"the selection reads more than coarsest-first on {worse} of {total} "
         f"assertions and no more on the rest; in total it reads fewer",
         sum(sum(v['reads_s']) for v in rows.values()) <
         sum(sum(v['reads_c']) for v in rows.values())),
        (f"the {carry - coinc} assertions whose zero is not at a coincident end are "
         "the frontier of boundary assertion, reported as a count", carry - coinc >= 0),
    ]
    return checks, rows, (first, second, later, none, worse, total)


def protocol_C8(F):
    """WHAT SELECTION BUYS, measured: mean reads under selection against
       coarsest-first and against the tower, per row."""
    rows = {}
    for fam, n, g, Z in F:
        rs = read_selected(Z); rc = read_coarsest(Z)
        row = rows.setdefault((fam, n, g), dict(s=[], c=[], t=2 ** n - 1))
        row["s"].append(rs["reads"]); row["c"].append(rc["reads"])
    means = [(k, sum(v["s"]) / len(v["s"]), sum(v["c"]) / len(v["c"]), v["t"])
             for k, v in sorted(rows.items())]
    return [
        ("under selection the mean reads are below coarsest-first on every row of "
         "family A", all(s < c for (fam, n, g), s, c, _ in means if fam == "A")),
        ("and below one percent of the tower from n = 12 upward on both families",
         all(s / t < 0.01 for (fam, n, g), s, c, t in means if n >= 12)),
    ], means


def protocol_C9():
    """THE WORKED COMPARISON, hand-checkable: the three resolutions of the one
       question on the worked assertion, under one RAM convention, with the
       structural reading's operations itemised so that every figure can be
       recomputed on paper."""
    X = WORKED
    P, N = D.sectors(X)
    survey = survey_ops(len(X))                      # 5*16 + 31
    table = bellman_ops(X)
    rs = read_selected(X)
    # the ledger of the structural reading
    ledger = [
        ("orientation partition (Def. 18.2): P = {5, 8}, N = {2, 3, 7}", 0),
        ("order of each sector by count: merge-sort comparisons, 1 for {5, 8} and 3 for {7, 3, 2}", 1 + 3),
        ("extremal floor: max(min P, min N) = 5 -- one comparison", 1),
        ("prefix and suffix sums of both sectors: 2 * (2 + 3) additions", 2 * (len(P) + len(N))),
        ("cardinality cells: 2 * 3 = 6 windows, one comparison each", len(P) * len(N)),
        ("selection: two surviving cells, one comparison per end, plus ranking", 2 * 2 + 1),
        ("reading the selected cell: least residences 5 and 3 + 2 -- one addition; "
         "coincide at depth 5 -- one match", 2),
    ]
    total = sum(v for _, v in ledger)
    return [
        (f"the ledger of the structural reading sums to its measured RAM count: "
         f"{total} = {rs['ram']}", total == rs["ram"]),
        (f"exhaustive survey: {survey} operations over 31 configurations; table: "
         f"{table} operations over 26 cells x 5 contents; structural reading: "
         f"{rs['ram']} operations over 2 configurations",
         rs["ram"] < table and rs["ram"] < survey and rs["reads"] == 2),
        ("the structural reading returns the residing content {5, -3, -2}; the table "
         "returns a bit", set(rs["addresses"][5]) == {5, -3, -2}),
    ], ledger, total, survey, table, rs





def protocol_C10():
    """MAGNITUDE INVARIANCE. The same twenty-five assertions at n = 12 with
       every content multiplied by g: the table grows with the magnitudes,
       the structural reading does not move."""
    rows = []
    for g in (1, 2, 4, 8, 16):
        tb = []; rl = []; rd = []; mm = []
        for s in range(25):
            Z = assertion(12, g, seed=1000 * 12 + s)
            r = read_selected(Z)
            tb.append(bellman_ops(Z)); rl.append(r["ram"]); rd.append(r["reads"])
        rows.append((g, sum(tb) / 25, sum(rl) / 25, sum(rd) / 25))
    return [
        ("the structural reading's mean operations are identical at every "
         "magnitude scale (to the operation)", len({round(r[2], 6) for r in rows}) == 1),
        ("and so are the configurations formed", len({round(r[3], 6) for r in rows}) == 1),
        (f"the table's mean operations grow with the magnitudes: "
         f"{rows[0][1]:.0f} to {rows[-1][1]:.0f} from scale 1 to scale 16",
         all(rows[i + 1][1] > rows[i][1] for i in range(len(rows) - 1))),
    ], rows


def protocol_C11(F):
    """THE READING ACTS PER CELL. An observation to be measured, not asserted.
       When the least residences of the first cell coincide, the reading is
       two residence reads and one match: three. When the greatest coincide,
       the least pair was read and matched first without coinciding: six.
       Otherwise the interior is read. This protocol counts reads per opened
       cell and cross-checks the counts at exactly three and exactly six
       against the traces."""
    per_cell = []; least_first = greatest_first = 0; none_opened = 0
    ok_l = ok_g = True
    for fam, n, g, Z in F:
        tr = []
        r = read_selected(Z, trace=tr)
        if r["strata_opened"] == 0:
            none_opened += 1
            continue
        per_cell.append(r["cell_acts"] / r["strata_opened"])
        if r["decision"] and r["strata_opened"] == 1:
            if any("least residences coincide" in t for t in tr):
                least_first += 1; ok_l &= (r["cell_acts"] == 3 and r["reads"] == 2)
            elif any("greatest residences coincide" in t for t in tr):
                greatest_first += 1; ok_g &= (r["cell_acts"] == 6 and r["reads"] == 4)
    at3 = sum(1 for v in per_cell if abs(v - 3) < 1e-9)
    at6 = sum(1 for v in per_cell if abs(v - 6) < 1e-9)
    return [
        (f"acts per opened cell: {at3} assertions at exactly 3, {at6} at exactly 6, "
         f"{len(per_cell) - at3 - at6} elsewhere; "
         f"{none_opened} opened no cell (no admitted cell: certificate)",
         len(per_cell) + none_opened == len(F)),
        (f"every assertion whose least residences coincide in the first cell ({least_first}) performs "
         f"exactly 3 acts in it, two reads and a match, and every one whose greatest do ({greatest_first}) exactly 6",
         ok_l and ok_g and least_first > 0 and greatest_first > 0),
    ], per_cell, at3, at6


def protocol_C12():
    """THE ANCHORS ON THE WORKED ASSERTION, each written from its own
       literature and charged under the one convention."""
    X = WORKED
    rs = read_selected(X)
    rows = [("exhaustive survey", 2 ** len(X) - 1, survey_ops(len(X))),
            ("Bellman table", 26 * 5, bellman_ops(X)),
            ("Horowitz-Sahni meet-in-the-middle", 2 ** (len(X) // 2) + 2 ** (len(X) - len(X) // 2), mitm_ops(X)),
            ("structural reading", rs["reads"], rs["ram"])]
    return [
        ("every anchor costs more than the structural reading on the worked "
         "assertion", all(r[2] > rs["ram"] for r in rows[:-1])),
    ], rows



def protocol_C13(F):
    """THE ANCHORS ON THE FAMILIES: survey, table, meet-in-the-middle and the
       structural reading, means per row, family B (distinct magnitudes)."""
    rows = []
    for n in (8, 12, 16, 20):
        Zs = [Z for fam, m, g, Z in F if fam == "B" and m == n]
        rl = [read_selected(Z)["ram"] for Z in Zs]
        tb = [bellman_ops(Z) for Z in Zs]
        mm = [mitm_ops(Z) for Z in Zs]
        rows.append((n, survey_ops(n), sum(tb) / len(Zs), sum(mm) / len(Zs), sum(rl) / len(Zs)))
    return [
        ("on every row the structural reading's mean operations are below the survey, "
         "the table and meet-in-the-middle",
         all(r[4] < r[1] and r[4] < r[2] and r[4] < r[3] for r in rows)),
        ("meet-in-the-middle grows as 2^(n/2): each step of four in n more than "
         "triples it", all(rows[i + 1][3] > 3 * rows[i][3] for i in range(len(rows) - 1))),
    ], rows


# ============================================================ the yield of each method

CANNOT = "cannot"      # the method's own output cannot produce the reading


def survey_readings(X, target=0):
    """What the exhaustive survey carries: every sub-collection with its sum."""
    sums = {}
    for r in range(1, len(X) + 1):
        for c in combinations(range(len(X)), r):
            s = sum(X[i] for i in c)
            sums.setdefault(s, []).append(tuple(X[i] for i in c))
    hits = sums.get(target, [])
    return dict(decision=bool(hits), content=hits[0] if hits else None,
                multiplicity=len(hits), spectrum=len(sums),
                certificate=(not hits),
                distance=(min(abs(k - target) for k in sums if k != target) if not hits else None))


def table_readings(X, target=0):
    """What the Bellman table carries: one bit per attainable sum."""
    lo = sum(v for v in X if v < 0); hi = sum(v for v in X if v > 0)
    size = hi - lo + 1
    reach = bytearray(size)
    for v in X:
        new = bytearray(reach); new[v - lo] = 1
        for i in range(size):
            if reach[i]:
                j = i + v
                if 0 <= j < size:
                    new[j] = 1
        reach = new
    hit = bool(reach[target - lo]); spec = [i + lo for i in range(size) if reach[i]]
    return dict(decision=hit, content=CANNOT, multiplicity=CANNOT, spectrum=len(spec),
                certificate=(not hit),
                distance=(min(abs(k - target) for k in spec if k != target) if not hit and spec else None))


def mitm_readings(X, target=0):
    """What meet-in-the-middle carries: the two half-lists and the pair found
       for the one target. The sweep answers one target; a spectrum, a
       multiplicity or a distance would each require a further pass."""
    n = len(X); h = n // 2
    def sums(S):
        out = []
        for r in range(0, len(S) + 1):
            for c in combinations(range(len(S)), r):
                out.append((sum(S[i] for i in c), tuple(S[i] for i in c)))
        return sorted(out)
    A, Bb = sums(X[:h]), sums(X[h:])
    i, j = 0, len(Bb) - 1
    while i < len(A) and j >= 0:
        s = A[i][0] + Bb[j][0]
        if s == target and (A[i][1] or Bb[j][1]):
            return dict(decision=True, content=A[i][1] + Bb[j][1], multiplicity=CANNOT,
                        spectrum=CANNOT, certificate=False, distance=CANNOT)
        if s < target:
            i += 1
        else:
            j -= 1
    return dict(decision=False, content=None, multiplicity=CANNOT, spectrum=CANNOT,
                certificate=True, distance=CANNOT)


def structural_readings(X, target=0):
    """What one structural resolution under the envelope boundary carries
       (Appendix E), together with the address read under the selected
       boundary (this appendix)."""
    import E_surplus as E
    occ, _ = E.resolve(X)
    spec = E.read_spectrum(occ)
    rs = read_selected(X)
    content = rs["addresses"][min(rs["addresses"])] if rs["decision"] else None
    mult = E.read_multiplicity(occ, target)
    cert = E.read_certificate(occ, target)
    return dict(decision=rs["decision"], content=content, multiplicity=mult,
                spectrum=len(spec), certificate=(not rs["decision"]),
                distance=(cert[1] if isinstance(cert, tuple) and not rs["decision"] else None))


def protocol_C14():
    """THE YIELD OF EACH METHOD on the worked assertion and on an assertion
       carrying no zero: each reading attempted from each method's own output."""
    rows = {}
    for name, f in (("exhaustive survey", survey_readings), ("Bellman table", table_readings),
                    ("meet-in-the-middle", mitm_readings), ("structural reading", structural_readings)):
        ry = f(WORKED); rn = f([-7, -3, 5, 8])
        rows[name] = dict(decision=ry["decision"] is True, content=ry["content"] not in (None, CANNOT),
                          multiplicity=ry["multiplicity"] is not CANNOT, spectrum=ry["spectrum"] is not CANNOT,
                          certificate=rn["certificate"] is True, distance=rn["distance"] not in (None, CANNOT))
    return [
        ("the exhaustive survey supplies every reading",
         all(rows["exhaustive survey"].values())),
        ("the table supplies no residing content and no multiplicity",
         not rows["Bellman table"]["content"] and not rows["Bellman table"]["multiplicity"]),
        ("meet-in-the-middle supplies the decision and the content for one target "
         "and no spectrum, multiplicity or distance",
         rows["meet-in-the-middle"]["content"] and not rows["meet-in-the-middle"]["spectrum"]
         and not rows["meet-in-the-middle"]["distance"]),
        ("the structural reading supplies every reading from one resolution",
         all(rows["structural reading"].values())),
    ], rows


def protocol_C15(F):
    """THE BOUNDARY'S COST LAW, exact: 1 + 2n + |P||N| + 2k + k(k-1)/2 RAM
       operations, k the surviving cells, on every assertion of the suite; and
       on every assertion whose least residences coincide in the first cell the
       whole resolution is the boundary plus the opening of that cell, two
       residence reads and one match (four structural acts), which in elementary
       operations is the boundary plus c_P + c_N <= n, the cell's cardinalities."""
    ok_b = ok_c = ok_n = ok_g = True; worst = 0.0; m = mg = 0
    for fam, n, g, Z in F:
        P, N = D.sectors(Z)
        ram = [0]
        _, strata, total, bacts = boundary(Z, ram, order=select)
        k = len(strata)
        srt = [0]; sort_cost([v for v in Z if v > 0], srt); sort_cost([-v for v in Z if v < 0], srt)
        bound = srt[0] + 1 + 2 * len(Z) + len(P) * len(N)
        if k:
            bound += 2 * k + (k - 1) + (0 if strata.first_coincides else (k - 1) + (len(Z) - 1))
        ok_b &= ram[0] == bound
        worst = max(worst, ram[0] / bound)
        tr = []
        r = read_selected(Z, trace=tr)
        if r["decision"] and r["strata_opened"] == 1 and any("least residences coincide" in t for t in tr):
            cp, cn = strata[0][0], strata[0][1]; m += 1
            ok_c &= (r["acts"] == bacts + 4) and (r["ram"] == ram[0] + cp + cn - 1)
            ok_n &= cp + cn - 1 < n
        elif r["decision"] and r["strata_opened"] == 1 and any("greatest residences coincide" in t for t in tr):
            cp, cn = strata[0][0], strata[0][1]; mg += 1
            ok_g &= (r["acts"] == bacts + 7) and (r["ram"] == ram[0] + 2 * (cp + cn - 1)) and 2 * (cp + cn - 1) < 2 * n
    return [
        (f"on all {len(F)} assertions the boundary costs exactly s(P) + s(N) + 1 + 2n + |P||N| + 2k + (k - 1) "
         f"operations, plus (k - 1) + (n - 1) where the least cell does not coincide (k the surviving cells, "
         f"s the merge-sort comparisons ordering a sector)", ok_b),
        (f"on every assertion whose least residences coincide in the first cell ({m} of {len(F)}), "
         "the whole resolution costs the boundary plus four structural acts (open, read, read, match) "
         "and, in elementary operations, the boundary plus exactly c_P + c_N - 1: the steps of the passage", ok_c),
        ("on each of those assertions c_P + c_N - 1 < n: the coincident reading costs fewer than n "
         "operations beyond the boundary", ok_n),
        (f"on every assertion whose greatest residences alone coincide in the first cell ({mg} of {len(F)}), "
         "the resolution costs the boundary plus seven acts and exactly 2(c_P + c_N - 1) < 2n operations", ok_g),
    ]


def certificate_family(n, seed):
    """An adversarial assertion with no zero and no coincident cell: asserted
       contents congruent to 1 and reversed contents congruent to 0 modulo n,
       so that no sub-collection with fewer than n asserted contents exhausts;
       |P| = n/2 < n."""
    r = random.Random(seed)
    P = [n * r.randint(1, 12) + 1 for _ in range(n // 2)]
    N = [n * r.randint(1, 12) for _ in range(n - n // 2)]
    return P + [-v for v in N]


def protocol_C16(F):
    """THE CEILING. Upstream cannot cost more than downstream at the same
       resolution: the reach reading is the table's own reading restricted to
       the sectors and the floor, charged as the table is charged, and the
       interiors are read only within the allowance the restriction saves.
       (1) The selected reading's decision agrees with the exhaustive
           reference (n <= 16) or the table's decision (n > 16) on every
           assertion, the ceiling path included; every address exhausts.
       (2) The interior reading of every surviving cell costs at most its
           formation bound.
       (3) The reach reading costs at most rho(X) = n(4m + 1) + m + 1 and marks
           exactly the depths at which a configuration of the sector resides;
           and the table, run in the order of the assertion, costs at least
           the reach reading plus n(t - m) - (m + 1): the reads the floor saves.
       (4) Where the allowance n(t - m) - (m + 1) - B(X) - (5k + 6n + 9) is
           non-negative the whole resolution costs at most the table; where
           it is negative, at most B(X) + rho(X) + 5k + 6n + 9.
       (5) In the length l = t(X): at most 8 l^2 + 16 l + 6 on every assertion.
       (6) The adversarial certificate family (no zero, no coincident cell):
           the certificate is returned on every one, at most at the table's
           cost; the ratio is reported."""
    ok1 = ok2 = ok3 = ok3b = ok4 = ok4b = ok5 = ok6 = True; fired = 0; rows = []; ratios = []; nonneg = 0
    adv = [("CERT", n, 10, certificate_family(n, 100 * n + s)) for n in (12, 16, 20, 24) for s in range(10)]
    for fam, n, g, Z in F + adv:
        P, N = D.sectors(Z)
        r = read_selected(Z)
        ref = bool(exhausting_subcollections(Z)) if n <= 16 else bellman_decision(Z)
        ok1 &= (r["decision"] == ref) and all(exhausts(c) for c in r["addresses"].values())
        ram = [0]; _, strata, _, _ = boundary(Z, ram, order=select)
        k = len(strata); B = ram[0]
        FP = formation_table(len(P), [0]); FN = formation_table(len(N), [0])
        for cp, cn, lo, hi in strata:
            rr = [0]; residences(P, cp, lo, hi, rr, [0], [0]); ok2 &= rr[0] <= FP[cp]
            rr = [0]; residences(N, cn, lo, hi, rr, [0], [0]); ok2 &= rr[0] <= FN[cn]
        t = sum(P) + sum(N); m = min(sum(P), sum(N)); rr = [0]; aa = [0]
        found_r, nread = reach_reading(P, N, m, rr, aa)
        rho = n * (4 * m + 1) + m + 1
        T = bellman_ops(Z)
        ok3 &= rr[0] <= rho
        ok3b &= T >= rr[0] + n * (t - m) - (m + 1)
        if n <= 12:
            for S, name in ((P, "asserted"), (N, "reversed")):
                attainable = {sum(c) for j in range(1, len(S) + 1) for c in combinations(S, j) if sum(c) <= m}
                reach = [None] * (m + 1)
                for x in sorted(S, reverse=True):
                    for i in range(m, -1, -1):
                        if reach[i] is not None and i + x <= m and reach[i + x] is None:
                            reach[i + x] = 1
                    if x <= m and reach[x] is None:
                        reach[x] = 1
                ok3 &= {d for d in range(1, m + 1) if reach[d] is not None} == attainable
        A = n * (t - m) - (m + 1) - B - (5 * k + 6 * n + 9)
        if A >= 0:
            nonneg += 1; ok4 &= r["ram"] <= T
        else:
            ok4 &= r["ram"] <= B + rho + 5 * k + 6 * n + 9
        ok4b &= r["ram"] <= T
        l = t
        ok5 &= r["ram"] <= 6 * l * l + 11 * l + 8
        if fam == "CERT":
            fired += 1 if r["ceiling"] else 0
            ok6 &= (not r["decision"]) and r["ram"] <= T
            ratios.append(T / r["ram"])
            rows.append((n, l, B, r["ram"] - B, r["ram"], T, r["ceiling"], 6 * l * l + 11 * l + 8))
    nF = len(F); nA = len(adv)
    return [
        (f"the selected reading's decision agrees with the exhaustive reference (n <= 16) or the table's "
         f"decision (n > 16) on all {nF} assertions of the suite and {nA} adversarial assertions, and "
         "every address returned is certified to exhaust", ok1),
        ("the interior reading of every surviving cell costs at most its formation bound "
         "2 * sum_{j<=c} C(a, j) + C(a, c), computed from the counts", ok2),
        ("the reach reading costs at most rho(X) = n(4m + 1) + m + 1, m the lesser sector total, and marks exactly "
         "the depths at which a configuration of the sector resides (n <= 12, against the exhaustive set)", ok3),
        ("the table, run in the order of the assertion, costs at least the reach reading plus n(t - m) - (m + 1) "
         "on every assertion: the reads the floor saves", ok3b),
        (f"where the allowance n(t - m) - (m + 1) - B(X) - (5k + 6n + 9) is non-negative ({nonneg} of {nF + nA}) the whole "
         "resolution costs at most the table, and where it is negative at most B(X) + rho(X) + 5k + 6n + 9", ok4),
        (f"and, measured, the whole resolution costs at most the table on every one of the {nF + nA} assertions, "
         "the negative-allowance ones (all at n = 6) included", ok4b),
        ("in the length l = t(X) the whole resolution costs at most 6 l^2 + 11 l + 8 on every assertion", ok5),
        (f"on the adversarial family (no zero, no coincident cell, |P| = |N| = n/2, n = 12..24) the certificate "
         f"is returned on all {nA} at no more than the table's cost; the ceiling fires on {fired} of {nA}; the "
         f"table costs between {min(ratios):.2f}x and {max(ratios):.1f}x the resolution", ok6),
    ], rows


# ============================================================ summary

def run():
    print("=" * 78)
    print("APPENDIX C  --  READING THE ENVELOPE BY DEPTH; THE SELECTED PARTITION;")
    print("                THE WORKED COMPARISON")
    print("Relational Lysis and Computational Efficiency")
    print("=" * 78)
    print(conventions.header(conventions.STRUCTURAL))
    print("  (RAM elementary operations reported beside, as the external anchor)")
    print()
    cks1, traces = protocol_C1()
    print("  C.1  THE TWO TRACES, coarsest-first, all addresses")
    for X, tr, r in traces:
        print(f"  ASSERTED X = {X}")
        for line in tr:
            print("     " + line)
        print(f"     -> addresses of zero: {sorted(r['addresses'])}   configurations read "
              f"{r['reads']} of {r['tower']}   cells opened {r['strata_opened']} of "
              f"{r['strata_total']}   acts {r['acts']}   RAM {r['ram']}")
        print()

    F = families()
    cks2, _ = protocol_C2(F)
    cks3, rows = protocol_C3(F)
    print("  C.3  THE SEARCH SPACE THE BOUNDARY LEAVES (coarsest-first)")
    print("  " + "-" * 74)
    print(f"  {'fam':>4}{'n':>4}{'range':>7}{'zero':>7}{'read':>8}{'tower':>14}{'read/tower':>12}"
          f"{'cells':>9}{'acts':>7}{'RAM':>8}{'table':>9}")
    print("  " + "-" * 74)
    for (fam, n, g), v in sorted(rows.items()):
        gl = "1..9" if fam == "A" else f"1..{g}"
        m = len(v["reads"])
        zero = f"{v['found']}/{v['total']}"
        strata = f"{sum(v['opened']) / m:.1f}/{sum(v['stot']) / m:.0f}"
        print(f"  {fam:>4}{n:>4}{gl:>7}{zero:>7}{sum(v['reads']) / m:>8.1f}{2 ** n - 1:>14,}"
              f"{sum(v['frac']) / m:>12.2%}{strata:>9}{sum(v['acts']) / m:>7.1f}"
              f"{sum(v['ram']) / m:>8.0f}{sum(v['bell']) / m:>9,.0f}")
    print("  " + "-" * 74)
    print()

    cks5, out5 = protocol_C5()
    print("  C.5  THE SELECTION ON THE TWO ASSERTIONS")
    for X, rws, tr, r in out5:
        print(f"  ASSERTED X = {X}")
        print("     cells ranked by the counts (extremal residences, from the prefix and suffix sums):")
        for cp, cn, lo, hi, co, rp, rn in rws:
            print(f"        {cp} asserted + {cn} reversed, depths [{lo},{hi}]: least "
                  f"residences at {rp[0]} | {rn[0]}, greatest at {rp[1]} | {rn[1]}"
                  f"{'   <- coincide' if co else ''}")
        print("     reading under the selection:")
        for line in tr[1:]:
            print("     " + line)
        print(f"     -> zero at {sorted(r['addresses'])}; cells opened {r['strata_opened']}; "
              f"configurations read {r['reads']} of {r['tower']}; acts {r['acts']}; RAM {r['ram']}")
        print()

    cks7, rows7, (first, second, later, none, worse, total) = protocol_C7(F)
    cks8, means = protocol_C8(F)
    print("  C.7  THE SELECTED PARTITION ON THE FAMILIES")
    print("  " + "-" * 74)
    print(f"  {'fam':>4}{'n':>4}{'range':>7}{'zero':>7}{'first cell':>12}{'cells':>7}"
          f"{'reads sel.':>12}{'reads coarse':>14}{'tower':>14}")
    print("  " + "-" * 74)
    for (fam, n, g), v in sorted(rows7.items()):
        gl = "1..9" if fam == "A" else f"1..{g}"
        m = len(v["reads_s"])
        op = f"{sum(v['opened']) / len(v['opened']):.2f}" if v["opened"] else "-"
        zero = f"{v['zero']}/{v['total']}"; fc = f"{v['first']}/{v['zero']}"
        print(f"  {fam:>4}{n:>4}{gl:>7}{zero:>7}{fc:>12}{op:>7}"
              f"{sum(v['reads_s']) / m:>12.1f}{sum(v['reads_c']) / m:>14.1f}{v['tower']:>14,}")
    print("  " + "-" * 74)
    print(f"     Across all {total}: first cell {first}, second {second}, later {later}, "
          f"no zero {none}.")
    print()

    cks9, ledger, total9, survey9, table9, rs9 = protocol_C9()
    cks12, rows12 = protocol_C12()
    print("  C.9 / C.12  THE WORKED COMPARISON -- one question, four resolutions, one convention")
    print("  " + "-" * 74)
    print(f"     {'resolution':<36}{'formed / visited':>18}{'RAM operations':>16}")
    for name, formed, ops in rows12:
        print(f"     {name:<36}{formed:>18,}{ops:>16,}")
    print("  " + "-" * 74)
    print("     the structural reading, itemised:")
    for desc, v in ledger:
        print(f"        {v:>3}  {desc}")
    print(f"        {total9:>3}  total")
    print()

    cks10, rows10 = protocol_C10()
    print("  C.10  MAGNITUDE INVARIANCE -- n = 12, every content multiplied by g")
    print("  " + "-" * 74)
    print(f"  {'g':>4}{'table':>10}{'structural':>12}{'formed':>8}{'table/structural':>18}")
    print("  " + "-" * 74)
    for g, tb, rl, rd in rows10:
        print(f"  {g:>4}{tb:>10,.0f}{rl:>12.1f}{rd:>8.1f}{tb / rl:>17.1f}x")
    print("  " + "-" * 74)
    print()

    cks13, rows13 = protocol_C13(F)
    print("  C.13  THE ANCHORS ON THE FAMILIES (family B, means of 25 per row)")
    print("  " + "-" * 74)
    print(f"  {'n':>4}{'survey':>14}{'table':>10}{'meet-in-middle':>16}{'structural':>12}"
          f"{'survey/str':>12}{'table/str':>11}{'mitm/str':>10}")
    print("  " + "-" * 74)
    for n, sv, tb, mm, rl in rows13:
        print(f"  {n:>4}{sv:>14,}{tb:>10,.0f}{mm:>16,.0f}{rl:>12.0f}{sv / rl:>11,.0f}x"
              f"{tb / rl:>10.1f}x{mm / rl:>9.1f}x")
    print("  " + "-" * 74)
    print()

    cks11, per_cell, at3, at6 = protocol_C11(F)
    print(f"  C.11  READS PER OPENED CELL: {cks11[0][0]}")
    print()

    results = [("C.1  The two traces", cks1),
               ("C.2  Completeness and fidelity", cks2),
               ("C.3  The search space the boundary leaves", cks3),
               ("C.4  Determinism and discipline", protocol_C4(F)),
               ("C.5  The selection on the two assertions", cks5),
               ("C.6  Computability of the selection", protocol_C6()),
               ("C.7  The selected partition on the families", cks7),
               ("C.8  What selection buys", cks8),
               ("C.9  The worked comparison", cks9),
               ("C.10 Magnitude invariance", cks10),
               ("C.11 Reads per opened cell", cks11),
               ("C.12 The anchors", cks12),
               ("C.13 The anchors on the families", cks13),
               ("C.14 The yield of each method", protocol_C14()[0]),
               ("C.15 The boundary's cost law", protocol_C15(F)),
               ("C.16 The ceiling", protocol_C16(F)[0])]
    print("-" * 78)
    print("STRUCTURAL OUTPUTS AND VERDICTS")
    print("-" * 78)
    total_c = passed = 0
    for name, checks in results:
        print(f"\n  {name}")
        for desc, ok in checks:
            total_c += 1; passed += 1 if ok else 0
            print(f"     [{'PASS' if ok else 'FAIL'}]  {desc}")
    print()
    print("=" * 78)
    print(f"APPENDIX C VERDICT:  All {total_c} checks pass." if passed == total_c else
          f"APPENDIX C VERDICT:  {passed}/{total_c} pass -- FAILURE PRESENT.")
    print("=" * 78)
    return passed == total_c


if __name__ == "__main__":
    import sys
    sys.exit(0 if run() else 1)
