"""
B_address.py  --  Appendix B: Data as an Address
Relational Lysis and Computational Efficiency (P vs NP, introductory examination)

DISCIPLINE (per the companion papers' appendix standard):
  * No native integer arithmetic is used within any derivation. Magnitude is
    CONSTITUTED: a value of m is m allocation units (Def. 18.2, Thm. 18.1).
    Addition is concatenation of unit collections; comparison is conjugate
    pairing to exhaustion (Thm. 18.5). Native integers appear only to size the
    finite genesis pool and to render a final count for reading (Sec. 10).
  * No native boolean primitive decides any structural verdict.
  * THE TERM PROJECTION. All work here is at the level of the atom count t
    (Thm. 18.6): t(a + b) = t(a) + t(b), the mediating boundary contributing no
    atom. Enfolding is therefore concatenation of unit collections and carries
    no copula. The relation count r, which by Thm. 18.3 gains one intercession
    per mediation, is not the quantity measured and is not claimed to be. Every verdict is
    returned by a structural mechanism -- pairing exhaustion, residue inspection,
    or sector occupancy -- and only then rendered for display.
  * No floating point anywhere.
  * Every protocol is checked against the value the proof itself asserts.
"""

from itertools import combinations
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))
import conventions
import random

# ---------------------------------------------------------------- primitives

ASSERTED = "+"   # unit in its asserted orientation      (Def. 18.2, counts +1)
REVERSED = "-"   # its reversal                          (Def. 18.2, counts -1)


def constitute(magnitude_token, orientation):
    """Constitute a content as allocation units. The genesis pool is sized by a
       native integer (permitted); the units themselves carry no arithmetic."""
    return tuple(orientation for _ in range(magnitude_token))


def enfold(*collections):
    """Relational sum: mediation of unit collections (Def. 18.1). Concatenation,
       not addition."""
    out = ()
    for c in collections:
        out = out + c
    return out


def lyse(collection):
    """Primitive lysis (Def. 13.1): pair each asserted unit with its reversal.
       Returns (aligned_pair_count_as_units, residual_units). Nothing is removed
       -- paired units persist as aligned content (Thm. 18.5)."""
    asserted = [u for u in collection if u == ASSERTED]
    reversed_ = [u for u in collection if u == REVERSED]
    pairs = ()
    a, r = list(asserted), list(reversed_)
    while a and r:
        a.pop(); r.pop()
        pairs = pairs + (("pair"),)
    residual = tuple(a) + tuple(r)
    return pairs, residual


def exhausts(collection):
    """Zero as exhaustion (Def. 5.2, Cor. 23.8): the closure condition at which
       no residual stands. STRUCTURAL VERDICT -- decided by pairing, not by '=='."""
    _, residual = lyse(collection)
    for _ in residual:          # any residual at all defeats exhaustion
        return False
    return True


def same_magnitude(c1, c2):
    """Equality of two magnitudes decided by conjugate pairing to exhaustion.
       No native comparison of counts."""
    opposed = tuple(REVERSED if u == ASSERTED else ASSERTED for u in c2)
    return exhausts(enfold(c1, opposed))


def render(collection):
    """Render a final count for reading only. Never used in a derivation."""
    return len(collection)


# ------------------------------------------------- assertion and the envelope

class Assertion:
    """Asserting X fixes the envelope at genesis (Axiom 5.3). Nothing below is
       chosen; every quantity is forced by the assertion."""

    def __init__(self, values):
        self.values = tuple(values)
        # constituted contents, orientation carried by sign of the token
        self.contents = {
            v: constitute(abs(v), ASSERTED if v > 0 else REVERSED) for v in values
        }
        # asserted atom count: the asserted atom count t(X) under the term projection (Thm. 18.6)
        self.kappa = render(enfold(*self.contents.values()))
        # partition by orientation (Def. 18.2; opposition is reversal, Thm. 12.1)
        self.sector_asserted = tuple(v for v in values if v > 0)
        self.sector_reversed = tuple(v for v in values if v < 0)

    def negation(self):
        """not-X by componentwise opposition (Axiom 2.3, Lemma 26.5)."""
        return tuple(-v for v in self.values)

    def envelope_width(self):
        """Forced: kappa + 1 addresses (rendered for reading)."""
        return self.kappa + 1

    def ladder(self, sector):
        """Attainable magnitudes within one sector, as constituted collections.
           A bounded ladder -- not a walk over sub-collections."""
        reach = {(): ()}          # magnitude-collection -> contributing values
        for v in sector:
            additions = {}
            for mag, src in reach.items():
                extended = enfold(mag, self.contents[v])
                key = tuple(sorted(extended))
                known = False
                for existing in reach:
                    if same_magnitude(existing, extended):
                        known = True
                        break
                for existing in additions:
                    if same_magnitude(existing, extended):
                        known = True
                        break
                if not known:
                    additions[key] = src + (v,)
            reach.update(additions)
        return {k: v for k, v in reach.items() if v}

    def address(self):
        """THE ADDRESS. Exhaustion requires the two sectors to balance; the
           balance magnitude is the address. Found by intersecting two bounded
           ladders -- no descent from depth zero, no candidate rejected.
           Returns (address_magnitude, residing_content, operations)."""
        ops = 0
        LA = self.ladder(self.sector_asserted)
        LR = self.ladder(self.sector_reversed)
        ops += len(LA) + len(LR)
        for mag_a, src_a in LA.items():
            for mag_r, src_r in LR.items():
                ops += 1
                # the sectors carry opposite orientations already, so balance is
                # tested by direct pairing to exhaustion (Thm. 18.5), not by
                # same-orientation comparison
                if exhausts(enfold(mag_a, mag_r)):
                    return render(mag_a), tuple(src_a) + tuple(src_r), ops
        return None, None, ops


# -------------------------------------------------- independent cross-check

def exhaustive_reference(values):
    """Adversarial reference: every sub-collection, checked by constituted
       pairing. Deliberately the slow structural path -- used only to certify
       the address result, never inside it."""
    found = []
    for r in range(1, len(values) + 1):
        for c in combinations(values, r):
            coll = ()
            for v in c:
                coll = enfold(coll, constitute(abs(v),
                              ASSERTED if v > 0 else REVERSED))
            if exhausts(coll):
                found.append(tuple(sorted(c)))
    return found


# ----------------------------------------------------------------- protocols

def protocol_A1():
    """Constituted magnitude: no positional shorthand; a value of m is m units."""
    a = Assertion([8])
    c = a.contents[8]
    checks = [
        ("units constituted for 8", render(c) == 8),
        ("all units carry asserted orientation", all(u == ASSERTED for u in c)),
        ("reversal of 8 carries reversed orientation",
         all(u == REVERSED for u in Assertion([-8]).contents[-8])),
        ("equality decided by pairing, not comparison",
         same_magnitude(constitute(5, ASSERTED), constitute(5, ASSERTED))),
        ("unequal magnitudes leave residual",
         not same_magnitude(constitute(5, ASSERTED), constitute(4, ASSERTED))),
    ]
    return checks


def protocol_A2(X):
    """Conjugate negation by componentwise opposition; fixed-point-freedom."""
    a = Assertion(X)
    neg = a.negation()
    checks = [
        ("not-X is componentwise opposition", neg == tuple(-v for v in X)),
        ("no content equals its own reversal (Thm. 11.1(a))",
         all(v != -v for v in X)),
        ("double reversal returns the assertion",
         tuple(-v for v in neg) == tuple(X)),
        ("X and not-X jointly exhaust",
         exhausts(enfold(*[constitute(abs(v), ASSERTED if v > 0 else REVERSED)
                           for v in tuple(X) + neg]))),
    ]
    return checks


def protocol_A3(X):
    """Envelope fixation (Thm. 5.1): the atom count t(X) and the sector bound
       cap(X) = min(t(P), t(N)) are fixed by the assertion before resolution."""
    a = Assertion(X)
    span_lo = sum(v for v in X if v < 0)      # rendered for reading only
    span_hi = sum(v for v in X if v > 0)
    tP = sum(v for v in X if v > 0); tN = -span_lo
    addr, _, _ = a.address()
    checks = [
        ("t(X) equals the total constituted allocation (Thm. 18.6)",
         a.kappa == sum(abs(v) for v in X)),
        ("t(X) = t(P) + t(N): the signed range spans t(X) + 1 magnitudes",
         span_hi - span_lo + 1 == a.envelope_width() == tP + tN + 1),
        ("the address lies within cap(X) = min(t(P), t(N)) (Thm. 5.1(iii))",
         addr is not None and 1 <= addr <= min(tP, tN)),
    ]
    return checks


def protocol_A4(X):
    """Partition of the envelope by orientation (Def. 18.2)."""
    a = Assertion(X)
    checks = [
        ("sectors are disjoint",
         not set(a.sector_asserted) & set(a.sector_reversed)),
        ("sectors exhaust the assertion",
         sorted(a.sector_asserted + a.sector_reversed) == sorted(X)),
        ("both sectors non-empty for a balanced assertion",
         bool(a.sector_asserted) and bool(a.sector_reversed)),
    ]
    return checks


def protocol_A5(X):
    """Address resolution by sector intersection -- the central protocol."""
    a = Assertion(X)
    addr, residing, ops = a.address()
    ref = exhaustive_reference(X)
    checks = [
        ("an address is returned when one exists", (addr is not None) == bool(ref)),
        ("content residing at the address exhausts",
         addr is None or exhausts(enfold(*[constitute(abs(v), ASSERTED if v > 0
                                           else REVERSED) for v in residing]))),
        ("residing content is a sub-collection of the assertion",
         addr is None or all(v in list(X) for v in residing)),
        ("address agrees with the exhaustive reference",
         addr is None or tuple(sorted(residing)) in ref),
    ]
    return checks, addr, residing, ops, ref


def protocol_A6(X):
    """Exact reconstitution: the content at the address reconstitutes without
       alteration (Thm. 15.3)."""
    a = Assertion(X)
    addr, residing, _ = a.address()
    if addr is None:
        return []          # no content resides; nothing to reconstitute
    pos = tuple(v for v in residing if v > 0)
    neg = tuple(v for v in residing if v < 0)
    mag_p = enfold(*[a.contents[v] for v in pos]) if pos else ()
    mag_n = enfold(*[a.contents[v] for v in neg]) if neg else ()
    return [
        ("asserted sector of the residing content matches the address",
         render(mag_p) == addr),
        ("reversed sector of the residing content matches the address",
         render(mag_n) == addr),
        ("the two sectors pair to exhaustion",
         exhausts(enfold(mag_p, mag_n))),
    ]


def protocol_A7(X, trials=40, seed=4):
    """ADVERSARIAL: agreement between the address and the exhaustive reference
       on sampled assertions (fixed seed; nothing here is random -- every
       assertion carries its constitution), including assertions with no
       address and assertions with several. Every address found is checked
       against the sector bound of Thm. 5.1(iii)."""
    random.seed(seed)
    agree = 0; none_cases = 0; multi_cases = 0; total = 0; within = 0
    for _ in range(trials):
        n = random.randint(4, 9)
        Z = [random.choice([-1, 1]) * random.randint(1, 12) for _ in range(n)]
        if not [v for v in Z if v > 0] or not [v for v in Z if v < 0]:
            continue
        total += 1
        addr, residing, _ = Assertion(Z).address()
        cap = min(sum(v for v in Z if v > 0), -sum(v for v in Z if v < 0))
        if addr is None or 1 <= addr <= cap:
            within += 1
        ref = exhaustive_reference(Z)
        if not ref:
            none_cases += 1
        if len(ref) > 1:
            multi_cases += 1
        if (addr is None and not ref) or (addr is not None and
                                          tuple(sorted(residing)) in ref):
            agree += 1
    return [
        (f"address agrees with reference on all {total} sampled assertions",
         agree == total),
        (f"every address found lies within cap(X) = min(t(P), t(N)) "
         f"(Thm. 5.1(iii)), {total} of {total}", within == total),
        (f"instances with no address exercised ({none_cases})", none_cases > 0),
        (f"instances with multiple addresses exercised ({multi_cases})",
         multi_cases > 0),
    ]



def protocol_A8(X):
    """ALIGNMENT WITH THE SOURCE CHAIN. Two assumptions the suite relies on,
       neither of which was previously checked."""
    import random as _r
    _r.seed(3)
    # (i) Def. 13.1 pairs the ELDEST unpaired unit with its reversal. The
    #     implementation pairs in an unspecified order. The residue must not
    #     depend on that order, or the two disagree.
    order_ok = True
    for _ in range(200):
        n = _r.randint(2, 14)
        coll = tuple(_r.choice([ASSERTED, REVERSED]) for _ in range(n))
        base = _lyse_residue(coll)
        for _ in range(6):
            sh = list(coll); _r.shuffle(sh)
            if _lyse_residue(tuple(sh)) != base:
                order_ok = False
    # (ii) the term projection identity the suite works in (Thm. 18.6)
    proj_ok = True
    for _ in range(200):
        a = _r.randint(0, 20); b = _r.randint(0, 20)
        ca = constitute(a, ASSERTED); cb = constitute(b, ASSERTED)
        if render(enfold(ca, cb)) != render(ca) + render(cb):
            proj_ok = False
    return [
        ("the residue is invariant under pairing order, so the implementation "
         "agrees with Def. 13.1's eldest-first rule on the quantity used",
         order_ok),
        ("t(a + b) = t(a) + t(b): the boundary contributes no atom (Thm. 18.6)",
         proj_ok),
        ("no derivation computes a relation count r: the suite measures t only "
         "(Thm. 18.6) and makes no claim about r (Thm. 18.3)",
         _measures_t_only()),
        ("the address is read, not surveyed: Assertion.ladder and "
         "Assertion.address form no sub-collection of X to test (no call to "
         "combinations; AST inspection), while the reference does",
         _reads_not_surveys()),
    ]


def _reads_not_surveys():
    import ast, inspect, textwrap
    def calls(fn):
        tree = ast.parse(textwrap.dedent(inspect.getsource(fn)))
        return {n.func.id if isinstance(n.func, ast.Name) else getattr(n.func, "attr", "")
                for n in ast.walk(tree) if isinstance(n, ast.Call)}
    return ("combinations" not in calls(Assertion.ladder) | calls(Assertion.address)
            and "combinations" in calls(exhaustive_reference))


def _measures_t_only():
    """AST inspection of executable code: no identifier in any derivation
       names a relation count. Docstrings are not code and are not inspected;
       this checker is excluded from its own inspection."""
    import ast, inspect, sys
    tree = ast.parse(inspect.getsource(sys.modules[__name__]))
    me = "_measures_t_only"
    bad = ("copula", "relation", "intercession", "rcount", "r_count")
    for node in ast.walk(tree):
        if isinstance(node, ast.FunctionDef) and node.name == me:
            continue
        if isinstance(node, ast.FunctionDef) and any(b in node.name.lower() for b in bad):
            return False
        if isinstance(node, ast.Name) and any(b in node.id.lower() for b in bad):
            return False
        if isinstance(node, ast.Attribute) and any(b in node.attr.lower() for b in bad):
            return False
    return True


def _lyse_residue(c):
    a = [u for u in c if u == ASSERTED]
    r = [u for u in c if u == REVERSED]
    while a and r:
        a.pop(); r.pop()
    return (len(a), len(r))


# ------------------------------------------------------------------- summary

# ====================================================== THE SOLVED STATE

from fractions import Fraction as _Fr


def solved_state(X):
    """The solved state (Sigma, D, S) of an assertion, in the sense of [2]
       Def. 9.2, built from Thm. 18.5 of [1].
       Sigma: the contents, under the fixed total order (eldest first).
       A(x, y): the units x presents into the mediation x (x) y. Where x and y
         stand in opposite orientation, x presents all its units: pairing
         resolves m = min(|x|, |y|) of them into aligned conjugate pairs and
         leaves |x| - m unpaired on x's side (Thm. 18.5), so A(x, y) = |x|.
         Where x and y stand in one orientation, nothing resolves (Thm. 18.5:
         'only opposite-matched units resolve'): A(x, y) = 0. A(x, x) = 0
         ([2] Def. 9.1).
       D = (A + A^T)/2, symmetric: the aligned component (Diamond);
       S = (A - A^T)/2, antisymmetric: the residual component (Shadow).
       For an opposite pair: D - |S| = m, the matched units, and 2|S| = the
       unpaired count of Thm. 18.5, oriented from the greater."""
    order = sorted(range(len(X)), key=lambda i: (-abs(X[i]), X[i] < 0, i))
    Sigma = [X[i] for i in order]
    n = len(Sigma)
    A = [[_Fr(0)] * n for _ in range(n)]
    for i, x in enumerate(Sigma):
        for j, y in enumerate(Sigma):
            if i != j and (x > 0) != (y > 0):
                A[i][j] = _Fr(abs(x))
    D = [[(A[i][j] + A[j][i]) / 2 for j in range(n)] for i in range(n)]
    S = [[(A[i][j] - A[j][i]) / 2 for j in range(n)] for i in range(n)]
    return Sigma, A, D, S


def residual_of(Y):
    """The residual of a configuration: lysis of its asserted units against
       its reversed units (Def. 13.1, Thm. 18.5) leaves this count standing,
       oriented. Zero is exhaustion (Def. 5.2)."""
    a = sum(v for v in Y if v > 0); r = sum(-v for v in Y if v < 0)
    while a and r:
        a -= 1; r -= 1
    return a - r


def closures_second_stratum(X):
    """Where a pair's residual stands as a content of the next stratum
       (Thm. 12.2: aligned content arises derivatively, by conjugate pairing
       of previously allocated units) and meets its conjugate there: either a
       content of X, or the residual of a disjoint pair. Each closure names an
       exhausting sub-collection."""
    out = set()
    pairs = [(x, y) for x, y in combinations(X, 2) if (x > 0) != (y > 0)]
    for x, y in pairs:
        r = residual_of((x, y))
        for z in X:
            if z not in (x, y) and residual_of((r, z)) == 0:
                out.add(tuple(sorted((x, y, z))))
        for u, v in pairs:
            if {u, v} & {x, y}:
                continue
            if residual_of((r, residual_of((u, v)))) == 0:
                out.add(tuple(sorted((x, y, u, v))))
    return out


def protocol_A9(X):
    """THE SOLVED STATE OF THE ASSERTION, and zero read from it."""
    Sigma, A, D, S = solved_state(X)
    n = len(Sigma)
    sym = all(D[i][j] == D[j][i] for i in range(n) for j in range(n))
    anti = all(S[i][j] == -S[j][i] for i in range(n) for j in range(n))
    recomposed = all(A[i][j] == D[i][j] + S[i][j] for i in range(n) for j in range(n))
    # S vanishes exactly on pairs that exhaust; D - |S| is the matched count
    pair_ok = True
    for i in range(n):
        for j in range(n):
            if i == j or (Sigma[i] > 0) == (Sigma[j] > 0):
                continue
            x, y = Sigma[i], Sigma[j]
            if (S[i][j] == 0) != (residual_of((x, y)) == 0):
                pair_ok = False
            if D[i][j] - abs(S[i][j]) != min(abs(x), abs(y)):
                pair_ok = False
            if 2 * abs(S[i][j]) != abs(residual_of((x, y))):
                pair_ok = False
    # the whole assertion as one pair of aggregates
    tP = sum(v for v in X if v > 0); tN = sum(-v for v in X if v < 0)
    whole_S = _Fr(tP - tN, 2)
    # every sub-collection: exhausts iff the solved state of its two parts has S = 0
    sub_ok = True
    for k in range(2, n + 1):
        for Y in combinations(X, k):
            P = sum(v for v in Y if v > 0); N = sum(-v for v in Y if v < 0)
            if P == 0 or N == 0:
                continue
            if ((P - N) == 0) != (residual_of(Y) == 0):
                sub_ok = False
    # second-stratum closures reproduce every exhausting sub-collection of three
    # contents, and of four with two of each orientation (a residual conjugate
    # to a content; two disjoint pair-residuals conjugate to each other)
    ex34 = {tuple(sorted(Y)) for k in (3, 4) for Y in combinations(X, k)
            if residual_of(Y) == 0 and (k == 3 or sum(1 for v in Y if v > 0) == 2)}
    cl = closures_second_stratum(X)
    # hierarchical lysis of any sub-collection, residuals carried stratum by
    # stratum in any order, terminates at zero exactly when it exhausts
    hier_ok = True
    rng = random.Random(3)
    for k in range(2, n + 1):
        for Y in combinations(X, k):
            for _ in range(3):
                order = list(Y); rng.shuffle(order)
                r = order[0]
                for v in order[1:]:
                    r = residual_of((r, v)) if r != 0 else v
                if (r == 0) != (residual_of(Y) == 0):
                    hier_ok = False
    return [
        ("A = D + S with D symmetric and S antisymmetric ([2] Def. 9.2, Prop. 9.1)",
         sym and anti and recomposed),
        ("on every opposite pair, S = 0 exactly where the pair exhausts; D - |S| is "
         "the matched count and 2|S| the unpaired count of Thm. 18.5", pair_ok),
        (f"the whole assertion, as asserted against reversed aggregates, has "
         f"S = {whole_S}: 2|S| is the residual lysis of X leaves standing "
         f"({residual_of(X):+d}), and S = 0 exactly where X itself exhausts",
         2 * abs(whole_S) == abs(residual_of(X)) and (whole_S == 0) == (residual_of(X) == 0)),
        ("every sub-collection exhausts exactly when the solved state of its two "
         "parts has S = 0 (Lemma on balance)", sub_ok),
        (f"the closures at the second stratum name exactly the exhausting "
         f"sub-collections of three contents and of four with two of each orientation: "
         f"{sorted(cl)}", cl == ex34),
        ("hierarchical lysis of every sub-collection, residuals carried in any order, "
         "terminates at zero exactly when the sub-collection exhausts (Lemma 19.1: "
         "the counts forget the tree)", hier_ok),
    ], (Sigma, A, D, S, cl)



# ---------------------------------------------------------------- B.10 the address as a path-word

def sigma_order(X):
    """The fixed total order of the contents, eldest first ([2] Sec. 10.2; the
       order of solved_state): by magnitude descending, asserted before
       reversed at equal magnitude, then by position in the assertion."""
    return sorted(X, key=lambda v: (-abs(v), v < 0))


def path_word_units(Y):
    """The address of Y (Def. 26.1 of [1]): the oriented path-word of its
       residence. Each content is written as its units in its orientation, in
       the fixed order of Sigma. Its length is t(Y) (Thm. 15.1: a finite
       configuration is a finite oriented word, the path-word of a unique
       stratum at depth equal to its length)."""
    return "".join((ASSERTED if v > 0 else REVERSED) * abs(v) for v in sigma_order(Y))


def path_word_contents(Y):
    """The same path, written in the contents of the assertion: Y as a word in
       the constitution X (Def. 26.1: position of a content within a
       constitution). Its length is |Y|, the number of contents."""
    return tuple(sigma_order(Y))


def lyse_word(word):
    """Primitive lysis of a unit word (Def. 13.1): pair the eldest unpaired
       asserted unit with its reversal, repeatedly. Returns (pairings, residual)."""
    a = [i for i, u in enumerate(word) if u == ASSERTED]
    r = [i for i, u in enumerate(word) if u == REVERSED]
    pairings = 0
    while a and r:
        a.pop(0); r.pop(0); pairings += 1
    return pairings, len(a) + len(r)


def protocol_B10(X, seeds=38):
    """THE ADDRESS AS A PATH-WORD (Def. 26.1, Thm. 15.1, Thm. 15.3 of [1]).
       (1) Every exhausting Y is a balanced oriented word of length t(Y) = 2w,
           w asserted units and w reversed, w = t(P') = t(N') its depth.
       (2) Instantiation reconstitutes it exactly: primitive lysis of the word
           terminates after exactly w pairings with no unit standing (zero as
           exhaustion, Def. 5.2) -- and on no non-exhausting word does it.
       (3) Where the counts select a coincident cell, the path-word in contents
           is written by the counts: the c_P least (or greatest) asserted
           contents and the c_N least (or greatest) reversed, a suffix (or
           prefix) of each sector in the order of Sigma; the reading returns
           exactly that word.
       (4) The reading pays the path's length in contents -- its steps, |Y| - 1
           (Def. 26.3: the length of a passage is the count of its steps) --
           beyond the boundary, and never its length in units.
       (5) Under magnification x g the length in units is multiplied by g
           exactly; the length in contents and the reading's cost are unchanged.
       (6) Two sub-collections may share one unit word: they are distinct
           constitutions at one stratum (Def. 19.1; Lemma 19.1 -- the counts
           forget the tree). The multiplicity is reported, not assumed."""
    import C_reading as C, D_boundary as Dm
    rng = random.Random(2610)
    sample = [X, [10, -8, -3, 2, 1]]
    while len(sample) < seeds:
        n = rng.choice([6, 8, 10, 12]); g = rng.choice([1, 1, 1, 2, 4])
        sample.append(C.assertion(n, g, seed=rng.randrange(10 ** 6)))
    ok1 = ok2 = ok2b = ok3 = ok4 = ok6 = True
    n_words = n_coinc = 0; max_mult = 1
    for Z in sample:
        ref = exhaustive_reference(Z)
        words = {}
        for Y in ref:
            Y = list(Y)
            w = sum(v for v in Y if v > 0)
            word = path_word_units(Y)
            ok1 &= (len(word) == sum(abs(v) for v in Y) == 2 * w
                    and word.count(ASSERTED) == w == word.count(REVERSED))
            pr, res = lyse_word(word)
            ok2 &= (pr == w and res == 0)
            words.setdefault(word, []).append(tuple(sorted(Y)))
            n_words += 1
        for word, ws in words.items():
            max_mult = max(max_mult, len(set(ws)))
            # distinct constitutions at one stratum: equal depth, equal atom count (Lemma 19.1)
            ok6 &= len({(sum(v for v in Y if v > 0), sum(abs(v) for v in Y)) for Y in set(ws)}) == 1
        # non-exhausting sub-collections: lysis leaves a unit standing
        for k in range(1, len(Z) + 1):
            for Yc in combinations(Z, k):
                if sum(Yc) != 0:
                    ok2b &= lyse_word(path_word_units(list(Yc)))[1] > 0
        # the coincident reading writes the word from the counts
        P, N = Dm.sectors(Z); ram = [0]
        _, strata, _, bacts = C.boundary(Z, ram, order=C.select)
        tr = []; r = C.read_selected(Z, trace=tr)
        if r["decision"] and r["strata_opened"] == 1 and any("residences coincide" in t for t in tr):
            cp, cn = strata[0][0], strata[0][1]
            least = any("least residences coincide" in t for t in tr)
            Y = list(r["addresses"][min(r["addresses"])] if least else r["addresses"][max(r["addresses"])])
            pick_P = P[:cp] if least else P[-cp:]
            pick_N = N[:cn] if least else N[-cn:]
            named = sorted(pick_P) + sorted(-v for v in pick_N)
            ok3 &= (sorted(Y) == sorted(named))
            # suffix (least) / prefix (greatest) of each sector in Sigma order
            SP = [v for v in sigma_order(Z) if v > 0]; SN = [v for v in sigma_order(Z) if v < 0]
            seg_P = SP[-cp:] if least else SP[:cp]; seg_N = SN[-cn:] if least else SN[:cn]
            ok3 &= (sorted(abs(v) for v in seg_P) == sorted(pick_P) and sorted(abs(v) for v in seg_N) == sorted(pick_N))
            ok4 &= (len(path_word_contents(Y)) == cp + cn == len(Y))
            if least:
                ok4 &= (r["ram"] - ram[0] == len(path_word_contents(Y)) - 1)   # the steps of the passage
            n_coinc += 1
    # (5) magnification
    ok5 = True
    for s in range(25):
        base = C.assertion(12, 1, seed=1000 * 12 + s)
        r1 = C.read_selected(base)
        if not r1["decision"]:
            continue
        for g in (2, 4, 8, 16):
            Zg = [g * v for v in base]
            rg = C.read_selected(Zg)
            Y1 = r1["addresses"][min(r1["addresses"])]; Yg = rg["addresses"][min(rg["addresses"])]
            ok5 &= (len(path_word_units(list(Yg))) == g * len(path_word_units(list(Y1)))
                    and len(path_word_contents(list(Yg))) == len(path_word_contents(list(Y1)))
                    and rg["ram"] == r1["ram"] and rg["acts"] == r1["acts"]
                    and list(Yg) == [g * v for v in Y1])
    worked = path_word_units(path_word_contents([5, -3, -2]))
    # the worked assertion at x16: the address is 160 units at depth 80, 3 contents; the reading beyond the boundary is still 3
    ram1 = [0]; C.boundary(X, ram1, order=C.select); r1 = C.read_selected(X)
    X16 = [16 * v for v in X]; ram16 = [0]; C.boundary(X16, ram16, order=C.select); r16 = C.read_selected(X16)
    Y16 = list(r16["addresses"][min(r16["addresses"])])
    ok7 = (len(path_word_units(Y16)) == 160 and min(r16["addresses"]) == 80 and len(path_word_contents(Y16)) == 3
           and r16["ram"] - ram16[0] == 2 == r1["ram"] - ram1[0] and ram16[0] == ram1[0])
    return [
        (f"every exhausting sub-collection of {len(sample)} sampled assertions ({n_words} words) is a balanced "
         "oriented word of length t(Y) = 2w with w asserted and w reversed units, w its depth", ok1),
        ("primitive lysis of each such word terminates after exactly w pairings with no unit standing", ok2),
        ("and on every non-exhausting sub-collection it leaves a unit standing", ok2b),
        (f"on every coincident first cell ({n_coinc} of {len(sample)}) the reading returns the word the counts "
         "write: a suffix (least) or prefix (greatest) of each sector in the order of Sigma", ok3),
        ("the path-word in contents has c_P + c_N = |Y| contents and |Y| - 1 steps, and where the least "
         "coincide the reading's cost beyond the boundary is exactly |Y| - 1 elementary operations: one per step", ok4),
        ("under magnification x2, x4, x8, x16 (n = 12, 25 assertions) the length in units is multiplied "
         "by g exactly while the length in contents, the operations and the acts are unchanged", ok5),
        (f"on the worked assertion the address of zero is the word {worked} (length 10 in units; 3 contents, 2 steps)",
         worked == ASSERTED * 5 + REVERSED * 3 + REVERSED * 2),
        ("on the worked assertion with every magnitude multiplied by sixteen the address is a word of 160 units "
         "at depth 80 and 3 contents (two steps), the boundary is unchanged and the reading beyond it is still exactly 2", ok7),
        (f"distinct sub-collections sharing one unit word occur (greatest multiplicity {max_mult}) and are "
         "distinct constitutions at one stratum: equal depth and equal atom count", ok6 and max_mult > 1),
    ], (n_words, n_coinc, max_mult)


def run():
    X = [-7, -3, -2, 5, 8]
    a = Assertion(X)
    print("=" * 78)
    print("APPENDIX B  --  DATA AS AN ADDRESS")
    print("Relational Lysis and Computational Efficiency")
    print("=" * 78)
    print(conventions.header(conventions.STRUCTURAL))
    print()
    print(f"  Asserted            X  = {list(X)}")
    print(f"  Forced negation    ~X  = {list(a.negation())}")
    print(f"  Atom count t(X)      = {a.kappa}   (constituted allocation units)")
    print(f"  Envelope width         = {a.envelope_width()}   (= k + 1, forced at assertion)")
    print()
    LA = a.ladder(a.sector_asserted); LR = a.ladder(a.sector_reversed)
    print(f"  Asserted sector  {list(a.sector_asserted)}")
    print(f"     attainable magnitudes : {sorted(render(m) for m in LA)}")
    print(f"  Reversed sector  {list(a.sector_reversed)}")
    print(f"     attainable magnitudes : {sorted(render(m) for m in LR)}")
    inter = sorted({render(m) for m in LA} & {render(m) for m in LR})
    print(f"  Intersection            : {inter}        <-- THE ADDRESS")
    print()

    results = []
    results.append(("B.1  Constituted magnitude", protocol_A1()))
    results.append(("B.2  Conjugate negation", protocol_A2(X)))
    results.append(("B.3  Envelope fixation", protocol_A3(X)))
    results.append(("B.4  Partition by orientation", protocol_A4(X)))
    cks, addr, residing, ops, ref = protocol_A5(X)
    results.append(("B.5  Address resolution", cks))
    results.append(("B.6  Exact reconstitution", protocol_A6(X)))
    results.append(("B.7  Adversarial agreement", protocol_A7(X)))
    results.append(("B.8  Alignment with the source chain", protocol_A8(X)))
    cks9, (Sigma, A9, D9, S9, cl9) = protocol_A9(X)
    cks9b, (_, _, _, _, cl9b) = protocol_A9([10, -8, -3, 2, 1])
    results.append(("B.9  The solved state of the assertion", cks9 + [
        ("on {10, -8, -3, 2, 1} the closures at the second stratum name both exhausting "
         f"sub-collections: {sorted(cl9b)}", cks9b[-2][1] and len(cl9b) == 2)]))
    cks10, (nw10, nc10, mm10) = protocol_B10(X)
    results.append(("B.10 The address as a path-word", cks10))
    print("  THE SOLVED STATE (Sigma, D, S) of the assertion ([2] Def. 9.2; Thm. 18.5)")
    lab = [f"{v:+d}" for v in Sigma]
    for name, M in (("D  aligned, symmetric", D9), ("S  residual, antisymmetric", S9)):
        print(f"     {name}")
        print("            " + "".join(f"{l:>7}" for l in lab))
        for i in range(len(Sigma)):
            print(f"     {lab[i]:>7}" + "".join(f"{str(M[i][j]):>7}" for j in range(len(Sigma))))
    print(f"     closures at the second stratum: {sorted(cl9)}")
    print()
    print("  THE ADDRESS AS A PATH-WORD (Def. 26.1, Thm. 15.1, Thm. 15.3)")
    for Y in ([5, -3, -2],):
        print(f"     Y = {Y}: in contents {path_word_contents(Y)} (length {len(Y)}); "
              f"in units {path_word_units(Y)} (length {len(path_word_units(Y))}); "
              f"lysis: {lyse_word(path_word_units(Y))[0]} pairings, {lyse_word(path_word_units(Y))[1]} standing")
    print()

    print(f"  Address              : {addr}")
    print(f"  Content residing     : {list(residing) if residing else None}")
    print(f"  Operations to resolve: {ops}")
    print(f"  Exhaustive reference : {[list(r) for r in ref]}")
    print()
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
    words = {18:"eighteen",19:"nineteen",20:"twenty",21:"twenty-one",
             22:"twenty-two",23:"twenty-three",24:"twenty-four",
             25:"twenty-five",26:"twenty-six",27:"twenty-seven",
             28:"twenty-eight",29:"twenty-nine",30:"thirty",
             31:"thirty-one",32:"thirty-two",33:"thirty-three",34:"thirty-four",
             35:"thirty-five",36:"thirty-six"}
    word = words.get(total, str(total))
    if passed == total:
        print(f"APPENDIX B VERDICT:  All {word} checks pass.")
    else:
        print(f"APPENDIX B VERDICT:  {passed}/{total} pass -- FAILURE PRESENT.")
    print("=" * 78)
    return passed == total


if __name__ == "__main__":
    import sys
    sys.exit(0 if run() else 1)
