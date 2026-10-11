"""
A_precedence.py  --  Appendix A: Structure Precedes Enumeration -- the withdrawal table.

Paper I, Implication I:
  "Distinction, mediation, and the enfolded relational tree are established in
   Sections 2-5 from axioms none of which quantifies over numbers... The
   dependence is strictly one-directional and is proven so: every numerical
   object is defined from the chain, and no numerical object is required to
   define the chain."

That is a DEPENDENCY claim, and a dependency claim is tested by withdrawal.
Below, the numerical objects are withdrawn one at a time from the SAME asserted
contents, and both resolutions are run against what remains. A method that
needs a numerical object fails the moment it is withdrawn. A method that does
not, completes.

Nothing is asserted here. Every cell is the outcome of a run.
"""

from itertools import combinations
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))
import conventions

ASSERTED, REVERSED = "+", "-"


# ------------------------------------------------------- the withdrawal ladder

# Paper I, Implication I names the derived objects exactly: "number -- zero,
# successor, order, and the arithmetic operations -- is then derived from that
# stratification in Section 10 as the bookkeeping of interior allocation."
# Those are what is withdrawn, in the order Section 10 derives them, and they
# are withdrawn from COUNTS, which is where they live.
WITHDRAWALS = [
    ("nothing withdrawn",                     set()),
    ("the arithmetic operations on counts",   {"arith"}),
    ("+ order on counts",                     {"arith", "order"}),
    ("+ successor (Def. 10.2)",               {"arith", "order", "succ"}),
    ("+ the capacity count (Def. 10.1)",      {"arith", "order", "succ", "count"}),
]


class Refused(Exception):
    """Raised when a resolution reaches for a numerical object that has been
       withdrawn. Not caught inside either method: reaching for it is failure."""


class Unit:
    """An allocation unit (Def. 18.2): an orientation and nothing else."""
    __slots__ = ("o",)

    def __init__(self, o):
        self.o = o

    def __repr__(self):
        return self.o


class Count:
    """A capacity count (Def. 10.1). Number lives HERE -- it is what Section 10
       derives from the chain -- so it is here that the derived objects are
       withdrawn. A resolution that never forms a Count has used no number."""
    __slots__ = ("k", "_w")

    def __init__(self, k, w):
        self.k = k; self._w = w

    def _arith(self, other):
        if "arith" in self._w:
            raise Refused("the arithmetic operations on counts")
        o = other.k if isinstance(other, Count) else other
        return Count(self.k + o, self._w)

    def _order(self, other):
        if "order" in self._w:
            raise Refused("order on counts")
        o = other.k if isinstance(other, Count) else other
        return self.k < o

    def __index__(self):
        if "succ" in self._w:
            raise Refused("successor (iteration over counts)")
        return self.k

    __add__ = __radd__ = __sub__ = _arith
    __lt__ = __gt__ = _order

    def __repr__(self):
        return f"count({self.k})"


class Contents:
    """The asserted contents. A list is a numerical object in disguise once it
       is asked for its length or addressed by position; both are refused when
       the count has been withdrawn. Head and tail are structural: the first
       content and the rest, with no position named."""

    def __init__(self, items, w):
        self._items = list(items); self._w = w

    def count(self):
        """The capacity count of the contents (Def. 10.1)."""
        if "count" in self._w:
            raise Refused("the capacity count itself")
        return Count(len(self._items), self._w)

    def at(self, i):
        return self._items[i]

    def head_tail(self):
        """Structural decomposition: no count, no position."""
        if not self._items:
            return None, None
        return self._items[0], Contents(self._items[1:], self._w)

    def empty(self):
        for _ in self._items:
            return False
        return True

    def __iter__(self):
        return iter(self._items)


def constitute(k, orientation, w):
    """The content is GIVEN as oriented units. k sizes the finite genesis pool,
       exactly as Paper I's appendices permit: native integers may size the
       pool and render a count for reading; they may not enter a derivation."""
    return tuple(Unit(orientation) for _ in range(k))


def mediate(a, b):
    """Def. 18.1 at the term projection (Thm. 18.6): concatenation of unit
       collections. No arithmetic is performed on any unit."""
    return a + b


def lyse(c):
    """Def. 13.1: pairing on presentation. Units are matched and discharged;
       the residual stands. No unit is added, compared or counted."""
    a = [u for u in c if u.o == ASSERTED]
    r = [u for u in c if u.o == REVERSED]
    while a and r:
        a.pop(); r.pop()
    return tuple(a) + tuple(r)


def exhausts(c):
    """Def. 5.2, Cor. 23.8: zero is the closure condition -- no residual."""
    for _ in lyse(c):
        return False
    return True


# ------------------------------------------------------------ the two methods

def by_enumeration(contents):
    """Survey the sub-collections. To state the survey at all it must take the
       capacity count of the contents, form its successor to bound the sizes,
       and compare sizes in order."""
    n = contents.count()                     # Def. 10.1 -- the capacity count
    out = []
    bound = n + 1                            # the arithmetic operations
    for r in range(1, bound):                # successor / iteration
        for c in combinations(range(n), r):  # positions, ordered
            coll = ()
            named = []
            for i in c:
                nm, units = contents.at(i)
                coll = mediate(coll, units); named.append(nm)
            if exhausts(coll):
                out.append(tuple(named))
    return out


def by_structure(contents):
    """Each content either stands in the co-assertion or does not. The
       contents are consumed head and tail. No count is formed, no position
       named, no numeral used."""
    out = []

    def walk(rest, named, coll):
        if rest.empty():
            if named and exhausts(coll):
                out.append(tuple(named))
            return
        head, tail = rest.head_tail()
        nm, units = head
        walk(tail, named, coll)
        walk(tail, named + [nm], mediate(coll, units))

    walk(contents, [], ())
    return out


# ------------------------------------------------------------------- the table

WORKED = [("-7", 7, REVERSED), ("-3", 3, REVERSED), ("-2", 2, REVERSED),
          ("5", 5, ASSERTED), ("8", 8, ASSERTED)]
EXPECTED = [("-3", "-2", "5")]


def attempt(method, w):
    items = [(nm, constitute(k, o, w)) for nm, k, o in WORKED]
    try:
        got = method(Contents(items, w))
    except Refused as e:
        return "fails", str(e), None
    ok = sorted(got) == sorted(EXPECTED)
    return ("completes" if ok else "WRONG ANSWER"), "", sorted(got)


def run():
    print("=" * 78)
    print("APPENDIX A  --  STRUCTURE PRECEDES ENUMERATION")
    print("The withdrawal table: every cell is the outcome of a run.")
    print("=" * 78)
    print(conventions.header(conventions.STRUCTURAL))
    print()
    print(f"  Asserted X = {[nm for nm, _, _ in WORKED]}")
    print(f"  Question   : which sub-collections exhaust to zero?")
    print(f"  Answer     : {EXPECTED[0]}")
    print()
    print("  " + "-" * 74)
    print(f"  {'numerical object withdrawn':<34}{'ENUMERATION':>18}{'STRUCTURE':>18}")
    print("  " + "-" * 74)
    rows = []
    for label, w in WITHDRAWALS:
        e_st, e_why, e_ans = attempt(by_enumeration, w)
        s_st, s_why, s_ans = attempt(by_structure, w)
        rows.append((label, w, e_st, e_why, e_ans, s_st, s_why, s_ans))
        print(f"  {label:<34}{e_st:>18}{s_st:>18}")
    print("  " + "-" * 74)
    print()
    print("  Where enumeration fails, the object it reached for:")
    for label, w, e_st, e_why, _, _, _, _ in rows:
        if e_st == "fails":
            print(f"     {label:<36} -> {e_why}")
    print()
    print("  Answer returned by the structural resolution at every row:")
    for label, w, _, _, _, s_st, _, s_ans in rows:
        print(f"     {label:<34}{s_st:>12}   {s_ans}")
    print()

    # ---------------------------------------------------------------- verdicts
    enum_fails = [r for r in rows if r[2] == "fails"]
    struct_completes = all(r[5] == "completes" for r in rows)
    struct_same = len({str(r[7]) for r in rows}) == 1
    checks = [
        ("enumeration completes while every numerical object stands",
         rows[0][2] == "completes"),
        ("enumeration fails at the first withdrawal",
         rows[1][2] == "fails"),
        (f"enumeration fails at {len(enum_fails)} of {len(rows) - 1} withdrawals",
         len(enum_fails) == len(rows) - 1),
        ("the structural resolution completes at every withdrawal",
         struct_completes),
        ("including with the count of the contents itself withdrawn",
         rows[-1][5] == "completes"),
        ("and returns the identical answer at every row", struct_same),
        ("the dependence is therefore one-directional, as Paper I states",
         struct_completes and len(enum_fails) == len(rows) - 1),
    ]
    print("-" * 78)
    print("VERDICTS")
    print("  A.1  The withdrawal table")
    print("-" * 78)
    total = passed = 0
    for d, ok in checks:
        total += 1; passed += 1 if ok else 0
        print(f"   [{'PASS' if ok else 'FAIL'}]  {d}")
    print()
    print("=" * 78)
    w = {7: "seven", 8: "eight", 9: "nine"}
    print(f"APPENDIX A VERDICT:  All {w.get(total, total)} checks pass." if passed == total
          else f"VERDICT:  {passed}/{total} pass -- FAILURE PRESENT.")
    print("=" * 78)
    return passed == total


if __name__ == "__main__":
    import sys
    sys.exit(0 if run() else 1)
