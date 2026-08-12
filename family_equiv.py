#!/usr/bin/env python3
"""Affine-equivalence decision for the family-hunt pair: A vs B.

If the two degree-4 Gallagher members were related by B = T1 o A o T2
with T1, T2 affine invertible, the multiplicity-invariant tie measured
by family_hunt.py would be trivial (the "moves" of Question 4 include
affine changes of coordinates). This script DECIDES that question
exactly over QQ, in both directions. Verdict: NOT affinely equivalent.
Origin: the 2026-08-12 adversarial review of the family hunt (recorded
in issue #14); promoted to a committed, CI-run certificate.

Method. Component total degrees are strictly separated for both members
((deg F1, deg F2, deg F3) = (12, 11, 4), asserted), and affine
composition preserves total degree, so T1^-1 is forced lower-triangular
across the slots and B = T1 o A o T2 forces the slot equations

    (S1)  F3^S o T2 = e0 + e3 F3^T                    e3 != 0
    (S2)  F2^S o T2 = f0 + f2 F2^T + f3 F3^T          f2 != 0
    (S3)  F1^S o T2 = g0 + g1 F1^T + g2 F2^T + g3 F3^T

(source S, target T; e3, f2, g1 nonzero by invertibility of T1). The
top form of F3 is x^3*z for both members, so unique factorization in
Q[x,y,z] forces the linear part of T2 to map x -> al*x, z -> be*z
(al, be != 0), with the y-row m4*x + m5*y + m6*z free (m5 != 0 by
invertibility).

Stage 1 solves (S1) by constraint propagation: every deduction is one
exact monomial-coefficient equation combined with a nonvanishing
constraint, each asserted in closed form, and completeness is certified
by the residual of (S1) vanishing IDENTICALLY on the resulting
parametric family (parameters al != 0, m4). Stage 2 substitutes the
family into (S2): the f's enter linearly and are eliminated exactly
from a full-rank pivot set; the surviving coefficient conditions form a
polynomial system in (al, m4), decided over QQ by a lex Groebner basis
saturated at al != 0. Basis {1} in BOTH directions = no affine (T1, T2)
exists; (S3) is never needed.

Scope: this excludes the entire affine group (linear conjugation and
one-sided affine composition are special cases). Equivalence under
NON-affine tame moves remains open -- that caveat lives in the README's
family-hunt status table.
"""
import sys
import time

import sympy as sp
from sympy import Rational as Q

from family_hunt import member_kit, x, y, z

al, m4 = sp.symbols('al m4')


def stage1(Msrc, Mtgt, sname, tname):
    """Solve slot S1; return the certified parametric family for T2."""
    aS, aT = Msrc['a'], Mtgt['a']
    assert aS != 0 and aT != 0
    c1, c3, m5, m6, c2, e0, e3 = sp.symbols('c1 c3 m5 m6 c2 e0 e3')
    F3S = x + aS*x**2*y + x**3*z          # canonical form, checked:
    assert sp.expand(F3S - Msrc['F'][2]) == 0
    F3T = x + aT*x**2*y + x**3*z
    assert sp.expand(F3T - Mtgt['F'][2]) == 0
    be = sp.symbols('be')
    X, Y, Z = al*x + c1, m4*x + m5*y + m6*z + c2, be*z + c3
    D = sp.expand(F3S.subs({x: X, y: Y, z: Z}, simultaneous=True)
                  - e0 - e3*F3T)
    P = sp.Poly(D, x, y, z)
    # every deduction below is one exact coefficient equation:
    eq_y = P.coeff_monomial(y)            # = aS*c1^2*m5
    assert sp.expand(eq_y - aS*c1**2*m5) == 0
    #   aS != 0, m5 != 0 (invertibility)  =>  c1 = 0
    sub = {c1: 0}
    P = sp.Poly(sp.expand(D.subs(sub)), x, y, z)
    eq_x2 = P.coeff_monomial(x**2)        # = aS*al^2*c2
    assert sp.expand(eq_x2 - aS*al**2*c2) == 0
    sub[c2] = 0                            # al != 0
    P = sp.Poly(sp.expand(D.subs(sub)), x, y, z)
    eq_x2z = P.coeff_monomial(x**2*z)     # = aS*al^2*m6
    assert sp.expand(eq_x2z - aS*al**2*m6) == 0
    sub[m6] = 0
    P = sp.Poly(sp.expand(D.subs(sub)), x, y, z)
    eq_1 = P.coeff_monomial(1)
    assert sp.expand(eq_1 + e0) == 0      # e0 = 0
    sub[e0] = 0
    P = sp.Poly(sp.expand(D.subs(sub)), x, y, z)
    eq_x = P.coeff_monomial(x)            # = al - e3
    assert sp.expand(eq_x - (al - e3)) == 0
    sub[e3] = al
    P = sp.Poly(sp.expand(D.subs(sub)), x, y, z)
    eq_x2y = P.coeff_monomial(x**2*y)     # = aS*al^2*m5 - al*aT
    assert sp.expand(eq_x2y - (aS*al**2*m5 - al*aT)) == 0
    sub[m5] = aT/(aS*al)
    P = sp.Poly(sp.expand(D.subs(sub)), x, y, z)
    eq_x3z = P.coeff_monomial(x**3*z)     # = al^3*be - al
    assert sp.expand(eq_x3z - (al**3*be - al)) == 0
    sub[be] = 1/al**2
    P = sp.expand(D.subs(sub))
    eq_x3 = sp.Poly(P, x, y, z).coeff_monomial(x**3)
    #   al^3*c3 + aS*al^2*m4 = 0  =>  c3 = -aS*m4/al
    assert sp.expand(eq_x3 - (al**3*c3 + aS*al**2*m4)) == 0
    sub[c3] = -aS*m4/al
    # completeness certificate: residual identically zero on the family
    resid = sp.simplify(sp.expand(D.subs(sub)))
    assert resid == 0, "slot-1 family residual nonzero: %s" % resid
    Xf = (al*x + c1).subs(sub)
    Yf = (m4*x + m5*y + m6*z + c2).subs(sub)
    Zf = (be*z + c3).subs(sub)
    print("  [%s = T1 o %s o T2] slot-1 family (params al != 0, m4):"
          % (tname, sname), flush=True)
    print("    T2: X=%s, Y=%s, Z=%s ; e0=0, e3=al" % (Xf, Yf, Zf),
          flush=True)
    return Xf, Yf, Zf


def stage2(Msrc, Mtgt, sname, tname):
    """Decide slot S2 over the slot-1 family. Returns False when the
    direction is excluded, None when inconclusive (slot-3 would be
    needed -- has not occurred for this pair)."""
    Xf, Yf, Zf = stage1(Msrc, Mtgt, sname, tname)
    F2S, F2T, F3T = Msrc['F'][1], Mtgt['F'][1], Mtgt['F'][2]
    t0 = time.time()
    lhs = sp.expand(F2S.subs({x: Xf, y: Yf, z: Zf}, simultaneous=True))
    # For each monomial m: c_m(al, m4) = f0*b0_m + f2*b2_m + f3*b3_m
    # where the b's are rational CONSTANTS. Solve the f's from a
    # full-rank pivot set of rows exactly; the remaining rows become
    # conditions on (al, m4).
    PL = sp.Poly(sp.expand(lhs), x, y, z)
    P2 = sp.Poly(F2T, x, y, z)
    P3 = sp.Poly(F3T, x, y, z)
    monos = sorted(set(PL.monoms()) | set(P2.monoms()) | set(P3.monoms())
                   | {(0, 0, 0)})
    rows, rhs = [], []
    for m in monos:
        b = [Q(1) if m == (0, 0, 0) else Q(0),
             Q(P2.coeff_monomial(m) or 0), Q(P3.coeff_monomial(m) or 0)]
        rows.append(b)
        rhs.append(sp.together(PL.coeff_monomial(m) or 0))
    Mb = sp.Matrix(rows)
    piv = Mb.T.rref()[1]      # column indices of M^T = pivot ROWS of M
    assert len(piv) == 3, "f-coefficient matrix rank %d != 3" % len(piv)
    fsol = sp.Matrix([rows[i] for i in piv]).solve(
        sp.Matrix([rhs[i] for i in piv]))
    conds = set()
    for b, c in zip(rows, rhs):
        r = sp.together(sp.expand(c - (sp.Matrix([b]).dot(fsol))))
        num = sp.fraction(sp.cancel(r))[0]
        if num != 0:
            conds.add(sp.factor(num))
    print("    slot-2: f2 = %s (must be nonzero)" % sp.cancel(fsol[1]),
          flush=True)
    print("    slot-2: %d residual conditions in (al, m4) after linear "
          "elimination of f's [%.0fs]" % (len(conds), time.time() - t0),
          flush=True)
    if not conds:
        print("    slot-2 imposes NO conditions -> equivalence candidates "
              "survive; slot-3 required", flush=True)
        return None
    tt = sp.Symbol('tt')
    gens = list(conds) + [tt*al - 1]      # saturate al != 0
    G = sp.groebner(gens, tt, al, m4, order='lex', domain='QQ')
    empty = (list(G.exprs) == [sp.Integer(1)])
    print("    slot-2 system Groebner basis trivial (no solution with "
          "al != 0): %s" % empty, flush=True)
    if empty:
        print("  => %s and %s are NOT affinely equivalent." % (sname, tname),
              flush=True)
        return False
    print("    surviving (al, m4) locus: %s" % list(G.exprs), flush=True)
    return None


def main():
    MA = member_kit([0, -1, 3, 4])
    MB = member_kit([0, -1, -2, Q(3, 2)])
    print("--- affine-equivalence decision, degrees strictly separated ---",
          flush=True)
    for name, M in (('A', MA), ('B', MB)):
        degs = [sp.total_degree(sp.expand(Fi), x, y, z) for Fi in M['F']]
        assert degs == [12, 11, 4], degs
    print("  degrees (F1,F2,F3) = [12, 11, 4] for both members", flush=True)

    rBA = stage2(MA, MB, 'A', 'B')
    rAB = stage2(MB, MA, 'B', 'A')
    if rBA is False and rAB is False:
        print("VERDICT: A and B are NOT affinely equivalent (no T1, T2 in "
              "either direction); linear conjugation and one-sided affine "
              "compositions are special cases, all excluded.", flush=True)
        return 0
    print("VERDICT: inconclusive at slot-2; slot-3 required.", flush=True)
    return 1


if __name__ == '__main__':
    sys.exit(main())
