"""
conventions.py  --  the cost conventions of the suite, defined once.

Every appendix imports this module and prints its declared convention in its
own header. Two conventions are used, for two different purposes, and they are
never mixed in one table.

STRUCTURAL ACTS
    One act = one of the framework's own operations:
      relation asserted at the boundary (orientation, Def. 18.2; extremal
        reach; cardinality strata -- Appendix D)
      stratum opened (one partition of the envelope by sector cardinality)
      residence read (one configuration of one sector at one depth,
        Thm. 15.1)
      match (one test that both orientations are resident at one depth,
        Thm. 18.1, Def. 5.2)
      pairing discharge and exhaustion test where a content is certified
        (Def. 13.1, Thm. 18.5, Cor. 23.8)
      mediation (Def. 18.1 at the term projection, Thm. 18.6)
    Levels of magnitude are never acts. Used where the point of the appendix
    is WHAT IS AND IS NOT DONE: the precedence table, the address appendix,
    the cost appendix, the surplus appendix.

RECONCILIATION
    reconcile() resolves the worked assertion by reading the envelope by
    depth under the asserted boundary (Appendix B) and reports its cost under
    both conventions, so that any figure quoted in one convention can be read
    against the other.
"""

WORKED = [-7, -3, -2, 5, 8]

STRUCTURAL = "STRUCTURAL ACTS"
RAM = "RAM ELEMENTARY OPERATIONS"


def header(convention):
    assert convention in (STRUCTURAL, RAM)
    return f"  COST CONVENTION: {convention}  (defined in conventions.py)"


def reconcile(X=WORKED):
    """The worked assertion read by depth under the asserted boundary, counted
       under both conventions. Returns (acts, ram_ops)."""
    import importlib, os, sys
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    B = importlib.import_module("C_reading")
    r = B.resolve(X)
    return r["acts"], r["ram"]


if __name__ == "__main__":
    a, r = reconcile()
    print(f"worked assertion {WORKED}")
    print(f"  {STRUCTURAL:<28} {a}")
    print(f"  {RAM:<28} {r}")
