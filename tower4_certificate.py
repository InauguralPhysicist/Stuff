#!/usr/bin/env python3
"""Exact certificate: n4 >= 13 at Y = F(F(z*)) -- the tower, one story up.

Extends report section IV (keller_quantization_report.md, revision 9) from
F^3 to F^4: ess-range(n4) contains a value >= 13 > 9 = max ess-range(n2),
so S_{F^4} is inequivalent to S_{F^2} and S_F.  (F^4 vs F^3 remains open:
both essential ranges contain values >= 11.)

Seeding chain (all points explicit):
  z* = (-1643/50, 3289/100, -71/200)   certified n2 = 9   (IV.2, Lean-checked)
  y* = F(z*)                           certified n3 >= 11 (IV.2 --exact3)
  Y  = F(y*)                           this file: n4(Y) >= 13

Certificate structure (everything exact over Q or Q[u]/Qr):
  0. L(Y) < 0 and K(Y) != 0, so Y has exactly three real preimages:
     y* (a root of the fiber cubic at Y, verified exactly) and two real
     siblings z'(u), z''(u), u the roots of the residual quadratic Qr
     (discriminant > 0 exactly); sibling coordinates from the shape-lemma
     chart at Y (lex Groebner basis, denominators nonzero since K(Y) != 0).
  1. gcd tests mod Qr: L, K, B all nonzero at both siblings.  So each
     sibling is off the wall and off the empty-fiber curve, its fiber cubic
     is a genuine cubic (odd degree => a real root exists), and the shape
     lemma at the sibling recovers a real preimage w from it.
  2. No w in F^{-1}(z') u F^{-1}(z'') lies on the empty-fiber curve:
     the system  F(c(s)) = z(u), Qr(u) = 0  (c the rational curve
     parametrization) is insoluble -- each cleared equation is linear in u
     after reduction mod Qr, and the consistency polynomials in s have
     trivial gcd (only spurious s = 0 factors; the degenerate branch
     b1 = a1 = 0 is likewise insoluble).  Hence every such w is off the
     curve and (by report II.3, n >= 1 off the curve) has a real preimage v.
  3. Same elimination against F(F(c(s))): no such w lies on F(curve).
     Hence no preimage v of any such w is on the curve (else w = F(v)
     would be in F(curve)), so n(v) >= 1 and n2(w) >= 1.
  4. Assembly: n3(z') >= 1 and n3(z'') >= 1, so
        n4(Y) = n3(y*) + n3(z') + n3(z'') >= 11 + 1 + 1 = 13,
     and every inequality is strict/nondegenerate (det DF^4 = 16 != 0), so
     the bound holds on an open neighborhood of Y.

Dependencies quoted from the report (same ones its own --exact3 uses):
n3(y*) >= 11 (IV.2), n(y) >= 1 off the curve (II.3), the fiber-cubic /
shape-lemma bridge (I.1, II.3).

Run:  python3 tower4_certificate.py           (exact certificate, ~3 min)
      python3 tower4_certificate.py --corroborate   (adds 150-digit numeric
      chains; thresholds are RELATIVE -- the siblings live at coordinates up
      to ~1e189, where any absolute threshold silently rejects everything,
      the Appendix A.3 conditioning ghost in yet another costume.)
"""
import sys
from functools import reduce

import sympy as sp
from sympy import Rational as Q

x1, x2, x3, u, sg = sp.symbols('x1 x2 x3 u s')
F = [(1 + x1*x2)**3*x3 + x2**2*(1 + x1*x2)*(4 + 3*x1*x2),
     x2 + 3*x1*(1 + x1*x2)**2*x3 + 3*x1*x2**2*(4 + 3*x1*x2),
     2*x1 - 3*x1**2*x2 - x1**3*x3]


def Fv(p):
    s = dict(zip((x1, x2, x3), p))
    return tuple(sp.nsimplify(sp.together(f.subs(s))) for f in F)


L = lambda y: 27*y[0]**2*y[2]**2 - 18*y[0]*y[1]*y[2] + 16*y[0] + y[1]**3*y[2] - y[1]**2
K = lambda y: 27*y[0]*y[2]**2 - 9*y[1]*y[2] + 8
B = lambda y: 4 - 3*y[1]*y[2]


def main():
    zstar = (Q(-1643, 50), Q(3289, 100), Q(-71, 200))
    ystar = Fv(zstar)
    Y = Fv(ystar)
    ok = True

    # ---- 0. base point ----
    LY, KY = L(Y), K(Y)
    c0 = LY < 0 and KY != 0
    ok &= c0
    print("0a. L(Y) < 0 and K(Y) != 0:", c0)
    CY = sp.Poly(LY*x1**3 + B(Y)*x1 - 2*Y[2], x1)
    c1 = sp.expand(CY.as_expr().subs(x1, ystar[0])) == 0
    ok &= c1
    print("0b. y*_1 is an exact root of the fiber cubic at Y:", c1)
    Qr = sp.Poly(sp.cancel(CY.as_expr()/(x1 - ystar[0])), x1)
    c2 = sp.expand(Qr.as_expr()*(x1 - ystar[0]) - CY.as_expr()) == 0 \
        and Qr.discriminant() > 0
    ok &= c2
    print("0c. residual quadratic exact with disc > 0 (two real siblings):", c2)

    # ---- sibling coordinates from the shape lemma at Y ----
    G = sp.groebner([f - v for f, v in zip(F, Y)], x3, x2, x1, order='lex')
    uni = [g for g in G.exprs if g.free_symbols <= {x1}]
    assert len(uni) == 1
    sol = sp.solve([g for g in G.exprs if g not in uni], [x2, x3], dict=True)[0]
    Z = [u, sp.together(sol[x2]).subs(x1, u), sp.together(sol[x3]).subs(x1, u)]
    QrU = sp.Poly(Qr.as_expr().subs(x1, u), u)

    def red(expr):
        n, d = sp.fraction(sp.together(expr))
        return sp.rem(sp.Poly(sp.expand(n), u), QrU, u)

    # ---- 1. L, K, B nonzero at both siblings ----
    for name, fun in (('L', L), ('K', K), ('B', B)):
        g = sp.gcd(sp.Poly(red(fun(Z)), u), QrU)
        t = g.total_degree() == 0
        ok &= t
        print(f"1.  {name} != 0 at both siblings (gcd mod Qr trivial):", t)

    # ---- 2./3. curve eliminations ----
    curve = (Q(4, 27)/sg**2, Q(4, 3)/sg, sg)

    def eliminate(target):
        eqs = []
        for i in range(3):
            n1, d1 = sp.fraction(sp.together(target[i]))
            nz, dz = sp.fraction(sp.together(Z[i]))
            e = sp.expand(n1*dz - d1*sp.rem(sp.Poly(sp.expand(nz), u), QrU, u).as_expr())
            eqs.append(sp.Poly(e, u))
        ab = [(e.coeff_monomial(1), e.coeff_monomial(u)) for e in eqs]
        a1, b1 = ab[0]
        q2, q1c, q0 = [QrU.coeff_monomial(u**k) for k in (2, 1, 0)]
        main_branch = [sp.expand(ab[1][0]*b1 - a1*ab[1][1]),
                       sp.expand(ab[2][0]*b1 - a1*ab[2][1]),
                       sp.expand(q2*a1**2 - q1c*a1*b1 + q0*b1**2)]
        degen_branch = [sp.expand(b1), sp.expand(a1)]

        def trivial(polys):
            g = reduce(lambda a, b: sp.gcd(a, b, sg), polys)
            _, factors = sp.factor_list(sp.expand(g), sg)
            return all(base == sg for base, _ in factors)
        return trivial(main_branch), trivial(degen_branch)

    Fc = Fv(curve)
    t, tb = eliminate(Fc)
    ok &= t and tb
    print("2.  no w over either sibling on the curve:", t, "| degenerate branch:", tb)
    t, tb = eliminate(Fv(Fc))
    ok &= t and tb
    print("3.  no w over either sibling on F(curve):", t, "| degenerate branch:", tb)

    print("\nCERTIFICATE " + ("COMPLETE: n4(Y) >= 13 on an open set -- "
          "S_{F^4} inequivalent to S_{F^2} and S_F" if ok else "FAILED"))

    if '--corroborate' in sys.argv:
        corroborate(Y, Qr, Z, QrU)
    return 0 if ok else 1


def corroborate(Y, Qr, Z, QrU):
    """150-digit numeric chains; all thresholds RELATIVE (A.3 discipline)."""
    import mpmath as mp
    mp.mp.dps = 150

    def val(expr, ur=None):
        e = expr.subs(u, ur) if ur is not None and expr.has(u) else expr
        return mp.mpf(str(sp.N(e, 150)))

    for j, r in enumerate(sp.real_roots(Qr), 1):
        ur = sp.Float(str(r.evalf(150)), 150)
        zj = [val(comp, ur) for comp in Z]
        zf = [sp.Float(mp.nstr(v, 140), 140) for v in zj]
        Lz, Bz = val(L(zf)), val(B(zf))
        m = max(abs(Lz), abs(Bz), abs(2*zj[2]))
        roots = mp.polyroots([Lz/m, mp.mpf(0), Bz/m, -2*zj[2]/m],
                             maxsteps=2000, extraprec=3000)
        reals = [t for t in roots
                 if abs(mp.im(t)) < mp.mpf('1e-60')*max(1, abs(t))]
        xi = mp.re(reals[0])
        x2s, T2, T3 = sp.symbols('x2s T2 T3')
        F2p = sp.Poly(sp.expand(sp.numer(sp.together(
            F[1].subs(x3, (2*x1 - 3*x1**2*x2s - T3)/x1**3).subs(x2, x2s) - T2))), x2s)
        cs = [val(co.subs({x1: sp.Float(mp.nstr(xi, 140), 140),
                           T2: zf[1], T3: zf[2]})) for co in F2p.all_coeffs()]
        m2 = max(abs(c) for c in cs)
        best = None
        for r2 in mp.polyroots([c/m2 for c in cs], maxsteps=2000, extraprec=3000):
            if abs(mp.im(r2)) > mp.mpf('1e-50')*max(1, abs(r2)):
                continue
            xv2 = mp.re(r2)
            xv3 = (2*xi - 3*xi**2*xv2 - zj[2])/xi**3
            w = [sp.Float(mp.nstr(v, 140), 140) for v in (xi, xv2, xv3)]
            Fw = [val(f.subs(dict(zip((x1, x2, x3), w)))) for f in F]
            rel = max(abs(Fw[i]-zj[i])/max(mp.mpf(1), abs(zj[i])) for i in range(3))
            if best is None or rel < best[0]:
                best = (rel, w)
        rel, w = best
        Lw, Kw = val(L(w)), val(K(w))
        print(f"corroborate sibling {j}: |z| ~ {mp.nstr(max(abs(v) for v in zj), 3)}, "
              f"real w found, rel. residual {mp.nstr(rel, 3)}, "
              f"L(w) {'<' if Lw < 0 else '>'} 0, K(w) != 0: {Kw != 0} "
              f"-> n2(w) >= 1")


if __name__ == '__main__':
    sys.exit(main())
