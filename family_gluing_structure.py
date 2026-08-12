#!/usr/bin/env python3
"""Structural lemmas for the wall-gluing invariant (FAMILY_GLUING.md).

Machine-checks L1-L7 of the pre-registration, failure-loud, for both
family-hunt members. No A-vs-B invariant comparison happens here (the
pre-registration forbids it until the definition and gates are merged);
this file only pins the structural facts the definition rests on.

  L1  plane reduction: E depends on the target only through
      (P, R) = (B*C, A*C^2); off-wall n factors through the plane.
  L2  wall-limit eliminant E0 = -H + w*H'(0) has root structure
      {0 (double), 1, rho}, rho rational and member-specific.
  L3  gluing skeleton: the rho-sheet escapes at the wall; the
      near-wall pair condition B^2 + 4*q(0)*A > 0 coincides with the
      on-wall gamma-branch condition delta(A,B) > 0; the wall is a
      CRACK (n+ == n-) at generic (A,B) OFF the parabola {delta = 0},
      and a JUMP (4 | wall 1 | 2, side by sign of B) ON it -- both
      checked exactly at rational C = +/-1e-6.
  L4  delta(A,B) by two independent elimination routes agrees; the
      x = 0 wall branch solves linearly and uniquely for ALL (A,B),
      so wall count = 1 + (gamma pair: 0 or 2 by sign delta) is a
      theorem.
  L5  the discriminant curve D(P,R) = 0 is an irreducible quartic,
      deg_R = 3 with constant leading coefficient, and has NO smooth
      vertical tangents (saturation Groebner basis {1}), hence no
      compact ovals: all plane chambers -- and so all 3D chambers and
      wall strata -- are simply connected, and G3 needs no base points.
  L6  no phantom walls: the perfect-square locus (where E could have a
      non-real double root) is finite and every real point of it has
      REAL double roots (b^2 - 4c > 0), so every real arc of D = 0 is
      a genuine fiber-count jump. (A triple root of a real quartic is
      automatically real, so cusps cannot be phantom either.)
  L7  wall tangency: D restricted to the wall-approach path
      (P, R) = (tB, t^2 A) vanishes to order exactly 2 in t at generic
      (A,B), with t^2-coefficient proportional to the near-wall
      condition -- so closure(Sigma) meets the wall exactly in
      {delta = 0}, where the order-3 term takes over (the L3 jump).
"""
import sys

import mpmath as mp
import sympy as sp
from sympy import Rational as Q

from family_hunt import member_kit, n1_exact, n1_wall, x, y, z, w

Ps, Rs, Aw, Bw, t = sp.symbols('Ps Rs Aw Bw t')


def fail(msg):
    print("FAIL:", msg)
    sys.exit(1)


def curve_radical(expr, *gens):
    """Squarefree, lead-normalized product of the non-constant factors."""
    parts = [b for b, _ in sp.factor_list(sp.expand(expr))[1]]
    rad = sp.expand(sp.prod(parts)) if parts else sp.Integer(1)
    lead = sp.Poly(rad, *(gens or (Aw, Bw))).coeffs()[0]
    return sp.expand(rad/lead)


def gamma_deltas(M):
    """delta(A,B) for the gamma-branch by two independent eliminations."""
    a = M['a']
    F1, F2 = M['F'][0], M['F'][1]
    zg = -(1 + a*x*y)/x**2
    eqs = []
    for Fi, ti in ((F1, Aw), (F2, Bw)):
        num = sp.fraction(sp.cancel(Fi.subs(z, zg) - ti))[0]
        eqs.append(sp.expand(num))
    deltas = []
    for order in ((y, x), (x, y)):
        G = sp.groebner(eqs, *order, order='lex', domain='QQ(Aw,Bw)')
        v = order[1]
        uni = [e for e in G.exprs if e.free_symbols <= {v, Aw, Bw}]
        if not uni:
            fail("L4: no eliminant in %s" % v)
        P = sp.Poly(uni[-1], v)
        while P.coeff_monomial(1) == 0:
            P = sp.Poly(sp.cancel(P.as_expr()/v), v)
        deltas.append(sp.factor(sp.discriminant(P.as_expr(), v)))
    return deltas[0], deltas[1]


def check_member(name, roots, jump_pts):
    M = member_kit(roots)
    H, a, Hp0, p = M['H'], M['a'], M['Hp0'], M['p']
    F1, F2, F3 = M['F']

    # L1
    from family_hunt import TA, TB, TC
    EPR = -H + w*(Hp0 + Ps) - Rs
    if sp.expand(M['Et'] - EPR.subs({Ps: TB*TC, Rs: TA*TC**2})) != 0:
        fail("[%s] L1: E does not factor through (P, R)" % name)
    print("[%s] L1: E factors through (P, R) = (B*C, A*C^2)" % name)

    # L2
    E0 = sp.expand(-H + w*Hp0)
    r = sp.roots(sp.Poly(E0, w))
    if r.get(0, 0) != 2 or r.get(1, 0) != 1:
        fail("[%s] L2: E0 root structure wrong: %s" % (name, r))
    others = [k for k in r if k not in (0, 1)]
    if len(others) != 1 or not others[0].is_rational:
        fail("[%s] L2: rho not a single rational root: %s" % (name, r))
    rho = others[0]
    if sp.expand(H.subs(w, 0)) != 0 or sp.expand(H.subs(w, 1) - Hp0) != 0:
        fail("[%s] L2: structural identities behind the roots" % name)
    print("[%s] L2: E0 roots {0 (double), 1, rho = %s}" % (name, rho))

    # L3a: the rho-sheet escapes
    if sp.simplify(-rho - p.subs(w, rho)) == 0:
        fail("[%s] L3a: rho-sheet persists (-rho == p(rho))" % name)
    print("[%s] L3a: rho-sheet escapes at the wall" % name)

    # L3b: near-wall pair condition == on-wall gamma condition
    q0 = sp.cancel(E0/w**2).subs(w, 0)
    near = sp.expand(Bw**2 + 4*q0*Aw)
    delta1, delta2 = gamma_deltas(M)
    d1n, d1d = sp.fraction(delta1)
    if curve_radical(near) != curve_radical(d1n*d1d):
        fail("[%s] L3b: near-wall and on-wall conditions differ" % name)
    print("[%s] L3b: near-wall pair condition == on-wall delta curve (%s)"
          % (name, curve_radical(near)))

    # L4: two routes agree, and the x = 0 branch is linear and unique
    r2n, r2d = sp.fraction(delta2)
    if curve_radical(d1n*d1d) != curve_radical(r2n*r2d):
        fail("[%s] L4: elimination routes disagree" % name)
    sol = sp.solve([sp.expand(F1.subs(x, 0) - Aw),
                    sp.expand(F2.subs(x, 0) - Bw)], [y, z], dict=True)
    if len(sol) != 1:
        fail("[%s] L4: x = 0 wall branch not unique: %s" % (name, sol))
    print("[%s] L4: two-route delta agrees; x=0 branch unique "
          "(y = %s, z = %s)" % (name, sol[0][y], sol[0][z]))

    # L3c: crack off the parabola, exact n on both sides
    c = Q(1, 10**6)
    grid = [(Q(-3), Q(2, 3)), (Q(4), Q(1, 5)), (Q(-1, 8), Q(1)),
            (Q(6, 5), Q(-1)), (Q(-20), Q(-38, 3)), (Q(1, 4), Q(5, 2)),
            (Q(50), Q(1)), (Q(-50), Q(1)), (Q(0), Q(7)), (Q(9), Q(-9))]
    for av, bv in grid:
        if d1n.subs({Aw: av, Bw: bv}) == 0 or \
           d1d.subs({Aw: av, Bw: bv}) == 0:
            fail("[%s] L3c: grid point on the parabola" % name)
        np_, nm = n1_exact(M, (av, bv, c)), n1_exact(M, (av, bv, -c))
        if np_ is None or nm is None or np_ != nm:
            fail("[%s] L3c: crack violated at (%s, %s): %s vs %s"
                 % (name, av, bv, np_, nm))
        want = 4 if delta1.subs({Aw: av, Bw: bv}) > 0 else 2
        if np_ != want:
            fail("[%s] L3c: near-wall count %d != delta-predicted %d at "
                 "(%s, %s)" % (name, np_, want, av, bv))
    print("[%s] L3c: crack confirmed on %d-point off-parabola grid" %
          (name, len(grid)))

    # L3e: JUMP regression ON the parabola (adversarial review finding
    # F1): n(+eps) != n(-eps), wall fiber = 1, side selected by sign(B)
    for (av, bv), (wplus, wminus) in jump_pts:
        if sp.simplify(near.subs({Aw: av, Bw: bv})) != 0:
            fail("[%s] L3e: jump point not on the parabola" % name)
        np_, nm = n1_exact(M, (av, bv, c)), n1_exact(M, (av, bv, -c))
        nw = n1_wall(M, (av, bv, Q(0)))
        if (np_, nm, nw) != (wplus, wminus, 1):
            fail("[%s] L3e: jump pattern at (%s, %s): got (%s, %s, %s), "
                 "expected (%d, %d, 1)"
                 % (name, av, bv, np_, nm, nw, wplus, wminus))
    print("[%s] L3e: wall JUMP on the parabola confirmed (4 | 1 | 2, "
          "side by sign of B)" % name)

    # L5: discriminant curve -- irreducible quartic, no smooth vertical
    # tangents (=> no ovals => all chambers/strata simply connected)
    D = sp.expand(sp.discriminant(EPR, w))
    fl = sp.factor_list(D)[1]
    if len(fl) != 1 or fl[0][1] != 1:
        fail("[%s] L5: D not irreducible: %s" % (name, fl))
    Dp = sp.Poly(D, Ps, Rs)
    if Dp.total_degree() != 4:
        fail("[%s] L5: D not a quartic (degree %d)" % (name,
                                                       Dp.total_degree()))
    DR = sp.Poly(D, Rs)
    if DR.degree() != 3 or DR.LC().free_symbols:
        fail("[%s] L5: deg_R D != 3 with constant lc" % name)
    tt = sp.Symbol('tt')
    G = sp.groebner([D, sp.diff(D, Rs), 1 - tt*sp.diff(D, Ps)],
                    tt, Ps, Rs, order='lex', domain='QQ')
    if list(G.exprs) != [sp.Integer(1)]:
        fail("[%s] L5: smooth vertical tangent exists: %s" % (name,
                                                              G.exprs))
    print("[%s] L5: D irreducible quartic, deg_R 3 constant lc, no "
          "smooth vertical tangents (no ovals)" % name)

    # L6: no phantom walls -- perfect-square locus finite with REAL
    # double roots everywhere
    lc0 = sp.Poly(EPR, w).LC()
    b, cc = sp.symbols('b cc')
    diffE = sp.Poly(sp.expand(lc0*(w**2 + b*w + cc)**2 - EPR), w)
    eqs = [diffE.nth(k) for k in range(4)]
    sols = sp.solve(eqs, [b, cc, Ps, Rs], dict=True)
    nreal = 0
    for s in sols:
        if all(sp.im(sp.nsimplify(v)) == 0 for v in s.values()):
            nreal += 1
            disc2 = sp.simplify(s[b]**2 - 4*s[cc])
            if not disc2 > 0:
                fail("[%s] L6: PHANTOM WALL: non-real double roots at %s"
                     % (name, s))
    if nreal < 1:
        fail("[%s] L6: no real perfect-square point found (expected the "
             "node)" % name)
    print("[%s] L6: perfect-square locus: %d real point(s), all with "
          "real double roots -- no phantom walls" % (name, nreal))

    # L7: wall-path tangency and closure(Sigma) /\ wall = {delta = 0}
    Dpath = sp.expand(D.subs({Ps: t*Bw, Rs: t**2*Aw}))
    Pt = sp.Poly(Dpath, t)
    if Pt.nth(0) != 0 or sp.expand(Pt.nth(1)) != 0:
        fail("[%s] L7: path does not vanish to order 2" % name)
    c2 = sp.expand(Pt.nth(2))
    if curve_radical(c2) != curve_radical(near):
        fail("[%s] L7: t^2 coefficient not the near-wall condition: %s"
             % (name, c2))
    c3_on = sp.simplify(Pt.nth(3).subs(Aw, sp.solve(near, Aw)[0]))
    if c3_on == 0:
        fail("[%s] L7: t^3 term vanishes identically on the parabola"
             % name)
    print("[%s] L7: path tangency order 2, t^2 coeff == near-wall "
          "condition, t^3 term alive on the parabola" % name)

    # L3d: numeric sheet tracking (convergence/escape), 40 digits
    with mp.workdps(40):
        tompf = lambda qq: mp.mpf(int(qq.p))/int(qq.q)
        cH = [tompf(v) for v in sp.Poly(H, w).all_coeffs()]
        cp = [tompf(v) for v in sp.Poly(p, w).all_coeffs()]
        av, bv = mp.mpf(-3), mp.mpf(2)/3
        cv = mp.mpf(10)**-9
        cE = [-v for v in cH]
        cE[-2] += tompf(Hp0) + bv*cv
        cE[-1] -= av*cv**2
        rts = [mp.re(rr) for rr in mp.polyroots(cE, maxsteps=200,
                                                extraprec=100)
               if abs(mp.im(rr)) < mp.mpf(10)**-25]
        if len(rts) != 4:
            fail("[%s] L3d: expected 4 real sheets near wall" % name)
        ys = {}
        for w1 in rts:
            g = bv*cv - mp.polyval(cp, w1)
            xv = cv/g
            ys[float(w1)] = abs((w1*xv/cv - 1)/xv)
        near0 = [v for k, v in ys.items() if abs(k) < 1e-3]
        near1 = [v for k, v in ys.items() if abs(k - 1) < 1e-3]
        nearr = [v for k, v in ys.items() if abs(k - float(rho)) < 1e-3]
        if not (len(near0) == 2 and len(near1) == 1 and len(nearr) == 1):
            fail("[%s] L3d: sheet w-limits not {0,0,1,rho}" % name)
        if max(near0 + near1) > 100 or min(nearr) < 1e6:
            fail("[%s] L3d: persistence/escape pattern wrong" % name)
    print("[%s] L3d: sheet tracking: w->{0,0,1} persist, w->rho escapes"
          % name)


def main():
    check_member('A', [0, -1, 3, 4],
                 [((Q(5), Q(5)), (4, 2)), ((Q(1, 5), Q(-1)), (2, 4))])
    check_member('B', [0, -1, -2, Q(3, 2)],
                 [((Q(7, 5), Q(2)), (4, 2)), ((Q(7, 20), Q(-1)), (2, 4))])
    print("STRUCTURAL LEMMAS VERIFIED")
    return 0


if __name__ == '__main__':
    sys.exit(main())
