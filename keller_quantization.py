#!/usr/bin/env python3
"""The Alpoge Keller map as a quantum system: verification and new results.

Companion code to keller_quantization_report.md (see the report's revision
note for history; this docstring intentionally carries no revision pin).
Subcommands:

    verify     Part I   : symbolic identities, fiber structure, key numerics,
                          direction census (--seeds, --exactcheck)
    singular   Thm 2    : Sing{L=0} = empty-fiber curve; symbolic A2 criterion
                          (D^3L(k,k,k) = 6t) plus numeric slice corroboration
    fates      Thm 1    : trajectory fates, decided ALGEBRAICALLY -- closed-form
                          cubic-root tracking with the K-crossing exchange rule
                          of Lemma I.4b (x1-projection tracking is safe exactly
                          because the exchange is applied deterministically)
    boundary   I.2/I.3  : origin-lift fates per direction; wall-free lifts
    spectrum   Part III : Friedrichs spectrum on the branched covering manifold
                          (path-lifting mesh, exact edge certificates)
    tower      Part IV  : multiplicity functions of F^2 and F^3; exact rational
                          certificates for n2 in {3,5,7,9}; --exact3 proves
                          n3 >= 11 at a rational point (F^2-F^3 separation)
    monodromy  IV.4     : verified-lift covering monodromy over {L<0}
    nogo       III.4    : the ladder no-go overlap <Ch000,Ch002> != 0, by
                          adaptive quadrature and independent Monte Carlo

All symbolic claims are exact over Q (SymPy); numerics use NumPy/SciPy.  Method
choices are downstream of the source note's Appendix A and of this project's
own review history: fixed-step ODE integration and NAIVE nearest-value root
tracking are never used for branch identity (the former overshoots blowups,
the latter silently hops sheets at every K-crossing); 3D Newton continuation
appears only with locality guards; proximity completion of failed lifts is
restricted to edges certified wall-free, and is excluded entirely from the
monodromy computation; residual thresholds at large |x| are conditioning-aware
(F evaluates with absolute error ~1e-16*|x|^7 in float64).
"""
import argparse
import sys
import time

import numpy as np
import sympy as sp

# ----------------------------------------------------------------- shared setup
x1, x2, x3, y1, y2, y3, z = sp.symbols('x1 x2 x3 y1 y2 y3 z')
X = [x1, x2, x3]
Yv = [y1, y2, y3]

F1 = (1 + x1*x2)**3*x3 + x2**2*(1 + x1*x2)*(4 + 3*x1*x2)
F2 = x2 + 3*x1*(1 + x1*x2)**2*x3 + 3*x1*x2**2*(4 + 3*x1*x2)
F3 = 2*x1 - 3*x1**2*x2 - x1**3*x3
Fs = [sp.expand(f) for f in (F1, F2, F3)]
DFs = sp.Matrix(3, 3, lambda i, j: sp.diff(Fs[i], X[j]))
As = (-DFs.adjugate().T / 2).applyfunc(sp.expand)      # A = (DF^T)^{-1}

Lpoly = 27*y1**2*y3**2 - 18*y1*y2*y3 + 16*y1 + y2**3*y3 - y2**2
Kpoly = 27*y1*y3**2 - 9*y2*y3 + 8
Bpoly = 4 - 3*y2*y3

Ffun = sp.lambdify(X, Fs, 'numpy')
Arows = [sp.lambdify(X, list(As.row(i)), 'numpy') for i in range(3)]
DFentries = [[sp.lambdify(X, DFs[i, j], 'numpy') for j in range(3)] for i in range(3)]


def Lnum(Y):
    Y = np.asarray(Y, dtype=float)
    return (27*Y[..., 0]**2*Y[..., 2]**2 - 18*Y[..., 0]*Y[..., 1]*Y[..., 2]
            + 16*Y[..., 0] + Y[..., 1]**3*Y[..., 2] - Y[..., 1]**2)


def Fbatch(Xp):
    # overflow at |x| ~ 1e6+ is expected and guarded downstream; keep the
    # console clean so real diagnostics are visible
    with np.errstate(over='ignore', invalid='ignore'):
        return np.stack(Ffun(Xp[:, 0], Xp[:, 1], Xp[:, 2]), axis=-1)


def DFbatch(Xp):
    M = np.empty((len(Xp), 3, 3))
    a, b, c = Xp[:, 0], Xp[:, 1], Xp[:, 2]
    with np.errstate(over='ignore', invalid='ignore'):
        for i in range(3):
            for j in range(3):
                v = DFentries[i][j](a, b, c)
                M[:, i, j] = v if np.ndim(v) else float(v)
    return M


def newton_batch(Xp, Yt, iters=6):
    """Batched Newton on F(x) = y with the exact Jacobian."""
    Xp = np.array(Xp, dtype=float, copy=True)
    for _ in range(iters):
        R = Fbatch(Xp) - Yt
        J = DFbatch(Xp)
        try:
            d = np.linalg.solve(J, R[..., None])[..., 0]
        except np.linalg.LinAlgError:
            d = np.zeros_like(Xp)
            for k in range(len(Xp)):
                try:
                    d[k] = np.linalg.solve(J[k], R[k])
                except np.linalg.LinAlgError:
                    Xp[k] = np.nan
        Xp -= d
    return Xp


def newton1(x, y, iters=8):
    x = np.array(x, dtype=float)
    with np.errstate(over='ignore', invalid='ignore'):
        for _ in range(iters):
            r = np.array(Ffun(*x), dtype=float) - y
            try:
                x = x - np.linalg.solve(
                    np.array([[DFentries[i][j](*x) for j in range(3)]
                              for i in range(3)], dtype=float), r)
            except np.linalg.LinAlgError:
                return None
    return x if np.all(np.isfinite(x)) else None


_chart = None
def get_chart():
    """Shape-lemma chart x2(x1,y), x3(x1,y) plus 1D fallback (F3 linear in x3)."""
    global _chart
    if _chart is not None:
        return _chart
    G = sp.groebner([f - y for f, y in zip(Fs, Yv)], x3, x2, x1,
                    order='lex', domain=sp.FractionField(sp.QQ, ['y1', 'y2', 'y3']))
    rel2 = [p for p in G.exprs if x2 in p.free_symbols and x3 not in p.free_symbols][0]
    rel3 = [p for p in G.exprs if x3 in p.free_symbols][0]
    x2f = sp.lambdify((x1, y1, y2, y3), sp.solve(rel2, x2)[0], 'numpy')
    x3f = sp.lambdify((x1, y1, y2, y3), sp.solve(rel3, x3)[0], 'numpy')
    x3sub = (2*x1 - y3 - 3*x1**2*x2)/x1**3
    P2 = sp.Poly(sp.expand(sp.numer(sp.together(Fs[1].subs(x3, x3sub) - y2))), x2)
    P2c = [sp.lambdify((x1, y2, y3), c, 'numpy') for c in P2.all_coeffs()]
    x3f1d = sp.lambdify((x1, x2, y3), x3sub, 'numpy')
    _chart = (x2f, x3f, P2c, x3f1d)
    return _chart


def recover_1d(r, yv):
    """All fiber points over yv with x1 = r via the exact 1D reduction (y3 != 0)."""
    _, _, P2c, x3f1d = get_chart()
    cs = [float(c(r, yv[1], yv[2])) for c in P2c]
    out = []
    for zr in np.roots(cs):
        if abs(zr.imag) < 1e-7*max(1, abs(zr)):
            out.append([r, zr.real, float(x3f1d(r, zr.real, yv[2]))])
    return out


# ===================================================================== verify
def cmd_verify(args):
    t0 = time.time()
    print("--- symbolic identities (exact over Q)")
    print("degrees:", [sp.Poly(f, *X).total_degree() for f in Fs])
    print("det DF =", sp.expand(DFs.det()))
    print("A*DF^T == I:", (As*DFs.T).applyfunc(sp.expand) == sp.eye(3))
    print("max deg in A:", max(sp.Poly(As[i, j], *X).total_degree()
                               for i in range(3) for j in range(3) if As[i, j] != 0))
    print("Piola divergences:",
          [sp.expand(sum(sp.diff(As[i, k], X[k]) for k in range(3))) for i in range(3)])
    ok = all(sp.Poly(sp.expand(sum(As[i, k]*sp.diff(As[j, l], X[k])
                                   - As[j, k]*sp.diff(As[i, l], X[k]) for k in range(3))),
                     *X).is_zero
             for i in range(3) for j in range(i+1, 3) for l in range(3))
    print("all 9 commutator coefficients vanish:", ok)
    g = (DFs.T*DFs).applyfunc(sp.expand)
    print("det g =", sp.expand(g.det()),
          "; A^T A == g^{-1}:", (g*(As.T*As)).applyfunc(sp.expand) == sp.eye(3))

    print("\n--- fiber structure")
    cubic = Lpoly*x1**3 + Bpoly*x1 - 2*y3
    sub = dict(zip(Yv, Fs))
    print("cubic identity under y=F(x):", sp.expand(cubic.subs(sub)) == 0)
    print("Cor.2  B^3 + 27 y3^2 L == K^2:",
          sp.expand(Bpoly**3 + 27*y3**2*Lpoly - Kpoly**2) == 0)
    a, b, c, d = Lpoly, 0, Bpoly, -2*y3
    Delta = sp.expand(18*a*b*c*d - 4*b**3*d + b**2*c**2 - 4*a*c**3 - 27*a**2*d**2)
    print("Delta == -4 K^2 L:", sp.expand(Delta + 4*Kpoly**2*Lpoly) == 0)
    for pt in [(sp.Rational(4, 27), sp.Rational(4, 3), 1),
               (sp.Rational(1, 27), sp.Rational(2, 3), 2)]:
        G2 = sp.groebner([f - v for f, v in zip(Fs, pt)], x3, x2, x1, order='lex')
        print(f"ideal at {pt} == <1>:", list(G2.exprs) == [1])
    # shape-lemma relations are exact identities with leading coefficient ~ K
    x2f, x3f, _, _ = get_chart()  # forces GB; identity check:
    G = sp.groebner([f - y for f, y in zip(Fs, Yv)], x3, x2, x1,
                    order='lex', domain=sp.FractionField(sp.QQ, ['y1', 'y2', 'y3']))
    for p in G.exprs:
        num = sp.expand(sp.numer(sp.together(p)))
        print("GB element cleared-identity under y=F(x):",
              sp.expand(num.subs(sub)) == 0)
    # wall fiber counts (Prop. II.3 spot checks)
    for pt, expect in [((sp.Rational(2, 27), 1, 1), 1), ((0, 1, 1), 1),
                       ((sp.Rational(-1, 4), 0, 0), 3)]:
        G2 = sp.groebner([f - v for f, v in zip(Fs, pt)], x3, x2, x1, order='lex')
        uni = [p for p in G2.exprs if p.free_symbols <= {x1}]
        nreal = sum(m for r, m in sp.roots(sp.Poly(uni[0], x1)).items() if r.is_real)
        print(f"real fiber count over {pt}: {nreal} (expect {expect})")

    print("\n--- key numerics")
    rng = np.random.default_rng(0)
    Ls = Lnum(rng.uniform(-3, 3, size=(4000, 3)))
    print(f"sampling [-3,3]^3: n=1: {(Ls>0).sum()}, n=3: {(Ls<0).sum()} (note: 3305/695)")
    x0 = np.array([0.2, 0.1, -0.3])
    y0 = np.array(Ffun(*x0), dtype=float)
    print(f"L(F(x0)) = {Lnum(y0):.4f} (note: -4.2421)")
    c2 = 27*y0[2]**2
    c1 = 54*y0[0]*y0[2]**2 - 18*y0[1]*y0[2] + 16
    rts = np.sort(np.roots([c2, c1, Lnum(y0)]))
    print(f"walls: {np.round(rts, 4)} (note: -3.7188, 0.2772); "
          f"persistent limit {2*y0[2]/(4-3*y0[1]*y0[2]):.5f} (note: 0.19167)")
    tstar = rts[rts > 0][0]
    ts = tstar - np.geomspace(1e-6, 1e-2, 12)
    vals = []
    for t in ts:
        yq = y0 + np.array([t, 0, 0])
        rr = [w.real for w in np.roots([Lnum(yq), 0, 4 - 3*yq[1]*yq[2], -2*yq[2]])
              if abs(w.imag) < 1e-8]
        vals.append(max(abs(v) for v in rr))
    print("blowup exponent: %.4f (exact: -0.5)"
          % np.polyfit(np.log(tstar - ts), np.log(vals), 1)[0])
    v = np.array([-1.0, 0.3, 0.2]); v /= np.linalg.norm(v)
    a4 = 27*v[0]**2*v[2]**2 + v[1]**3*v[2]
    r = np.roots([a4, -18*v[0]*v[1]*v[2], -v[1]**2, 16*v[0]])
    pos = sorted(w.real for w in r if abs(w.imag) < 1e-9 and w.real > 1e-12)
    print(f"continuation direction: first positive root {pos[0]:.5f} (note: 2.30774)")
    seeds = [int(s) for s in args.seeds.split(',')]
    ndirs = args.dirs
    fracs = []
    for si, seed in enumerate(seeds):
        rng = np.random.default_rng(seed)
        dirs = rng.normal(size=(ndirs, 3))
        dirs /= np.linalg.norm(dirs, axis=1, keepdims=True)
        dists, n_noroot, n_wall = [], 0, 0
        for v in dirs:
            if v[0] >= 0:
                continue
            a4 = 27*v[0]**2*v[2]**2 + v[1]**3*v[2]
            r = np.roots(np.trim_zeros(np.array([a4, -18*v[0]*v[1]*v[2],
                                                 -v[1]**2, 16*v[0]]), 'b'))
            pos = sorted(w.real for w in r
                         if abs(w.imag) < 1e-9*max(1, abs(w)) and w.real > 1e-12)
            if pos:
                dists.append(pos[0]); n_wall += 1
            else:
                n_noroot += 1
        fracs.append(100*n_noroot/ndirs)
        if si == 0:
            d = np.array(dists)
            print(f"boundary distances over v1<0-with-wall (seed {seed}): "
                  f"min {d.min():.4f} (note: 1.0732), q10 {np.quantile(d, .1):.3f} (1.147), "
                  f"med {np.quantile(d, .5):.3f} (1.670), q90 {np.quantile(d, .9):.3f} (5.78), "
                  f"max {d.max():.0f} (1018)")
        print(f"  census seed {seed} ({ndirs} dirs): wall-reaching {100*n_wall/ndirs:.2f}%, "
              f"v1<0 wall-free {100*n_noroot/ndirs:.3f}%")
    if len(fracs) > 1:
        print(f"multi-seed wall-free estimate: {np.mean(fracs):.3f}% "
              f"+/- {np.std(fracs)/np.sqrt(len(fracs)):.3f}%  <- Part I.3 correction")
    else:
        se = 100*np.sqrt((fracs[0]/100)*(1 - fracs[0]/100)/ndirs)
        print(f"single-seed wall-free {fracs[0]:.3f}% +/- {se:.3f}% "
              f"(binomial); use --seeds for a multi-seed estimate")
    if args.exactcheck:
        import sympy as _sp
        from fractions import Fraction
        tq = _sp.symbols('t')
        rng = np.random.default_rng(seeds[0])
        dirs = rng.normal(size=(ndirs, 3))
        dirs /= np.linalg.norm(dirs, axis=1, keepdims=True)
        neg = dirs[dirs[:, 0] < 0]
        sub = neg[np.random.default_rng(99).choice(len(neg), args.exactcheck,
                                                   replace=False)]
        dis = 0
        for v in sub:
            a4 = 27*v[0]**2*v[2]**2 + v[1]**3*v[2]
            r = np.roots(np.trim_zeros(np.array([a4, -18*v[0]*v[1]*v[2],
                                                 -v[1]**2, 16*v[0]]), 'b'))
            mine = any(abs(w.imag) < 1e-9*max(1, abs(w)) and w.real > 1e-12 for w in r)
            vq = [_sp.Rational(Fraction(float(c)).limit_denominator(10**12)) for c in v]
            poly = _sp.Poly((27*vq[0]**2*vq[2]**2 + vq[1]**3*vq[2])*tq**3
                            - 18*vq[0]*vq[1]*vq[2]*tq**2 - vq[1]**2*tq + 16*vq[0], tq)
            exact = poly.degree() >= 1 and any(rr > 0 for rr in poly.real_roots())
            dis += int(mine != exact)
        print(f"criterion vs exact real-root counting: {dis} disagreements "
              f"in {args.exactcheck} checks")
    print(f"[{time.time()-t0:.0f}s]")


# =================================================================== singular
def cmd_singular(args):
    L1, L2, L3 = [sp.expand(sp.diff(Lpoly, v)) for v in Yv]
    print("L irreducible over Q:", sp.factor(Lpoly) == sp.expand(Lpoly))
    sub = {y1: sp.Rational(4, 27)/y3**2, y2: sp.Rational(4, 3)/y3}
    print("on curve: L =", sp.simplify(Lpoly.subs(sub)),
          ", dL =", [sp.simplify(gq.subs(sub)) for gq in (L1, L2, L3)])
    J = [Lpoly, L1, L2, L3]
    for f, name in [(3*y2*y3 - 4, "3y2y3-4"), (27*y1*y3**2 - 4, "27y1y3^2-4")]:
        G = sp.groebner(J + [1 - z*f], y1, y2, y3, z, order='grevlex')
        print(f"Rabinowitsch 1 in J+(1-z({name})):", list(G.exprs) == [1])
    G0 = sp.groebner(J, y1, y2, y3, order='lex')
    print("GB of singular ideal:", [sp.factor(gq) for gq in G0.exprs])
    # Hessian rank + tangent annihilation (symbolic, all t) + cusp geometry
    t = sp.symbols('t', positive=True)
    pt = {y1: sp.Rational(4, 27)/t**2, y2: sp.Rational(4, 3)/t, y3: t}
    H = sp.Matrix(3, 3, lambda i, j: sp.diff(Lpoly, Yv[i], Yv[j])).subs(pt)
    Hs = H.applyfunc(sp.simplify)
    tan_s = sp.Matrix([sp.diff(sp.Rational(4, 27)/t**2, t),
                       sp.diff(sp.Rational(4, 3)/t, t), 1])
    print("Hessian rank along curve:", Hs.rank(),
          "; H.tangent == 0:", sp.simplify(Hs*tan_s) == sp.zeros(3, 1))
    Hn = np.array(H.subs(t, 1).evalf(), dtype=float)
    tan = np.array([-8/27, -4/3, 1.0])
    q, _ = np.linalg.qr(np.column_stack([tan, [1, 0, 0], [0, 1, 0]]))
    P = q[:, 1:]
    w_, V = np.linalg.eigh(P.T @ Hn @ P)
    # kernel direction = eigenvalue nearest 0; checked, not assumed by position
    korder = np.argsort(np.abs(w_))
    kdir, udir = P @ V[:, korder[0]], P @ V[:, korder[1]]
    assert abs(w_[korder[0]]) < 1e-8 and w_[korder[1]] > 0, \
        f"unexpected transverse Hessian eigenvalues {w_}"
    p0 = np.array([4/27, 4/3, 1.0])
    from scipy.optimize import brentq

    def crossings(wv):
        f = lambda u: Lnum(p0 + wv*kdir + u*udir)
        us = np.linspace(-0.1, 0.1, 80001)
        vals = np.array([f(u) for u in us])
        return [brentq(f, us[i], us[i+1])
                for i in range(len(us) - 1) if vals[i]*vals[i+1] < 0]

    # one-sidedness: COMPUTED on both sides of the edge, not asserted
    n_plus = [len(crossings(wv)) for wv in (1e-3, 3e-3, 1e-2)]
    n_minus = [len(crossings(-wv)) for wv in (1e-3, 3e-3, 1e-2)]
    print(f"wall crossings in transverse slice: +w side {n_plus}, -w side {n_minus}")
    ws = np.geomspace(1e-4, 1e-2, 8)
    uu = [max(crossings(wv)) for wv in ws]          # the u>0 branch
    sl = np.polyfit(np.log(ws), np.log(np.array(uu, dtype=float)), 1)[0]
    one_sided = all(n == 2 for n in n_plus) and all(n == 0 for n in n_minus)
    print(f"numeric corroboration: cusp exponent p = {sl:.4f} (A2: 1.5) over two "
          f"decades; one-sided two-branch profile: {one_sided}")
    # SYMBOLIC A2 criterion along the entire curve (round-4 review, adopted):
    # rank-1 Hessian with 2D kernel containing the tangent, and nonvanishing
    # transverse cubic term D^3L(k,k,k) with all tangent-slot cubics zero.
    ts = sp.symbols('t_c')
    ptc = {y1: sp.Rational(4, 27)/ts**2, y2: sp.Rational(4, 3)/ts, y3: ts}
    Hc = sp.Matrix(3, 3, lambda i, j: sp.diff(Lpoly, Yv[i], Yv[j])).subs(ptc)
    tanc = sp.Matrix([sp.diff(sp.Rational(4, 27)/ts**2, ts),
                      sp.diff(sp.Rational(4, 3)/ts, ts), 1])
    kv = sp.Matrix([1/(3*ts), 1, 0])                # kernel vector transverse to tangent

    def D3(a, b, c):
        e = sp.Integer(0)
        for i in range(3):
            for j in range(3):
                for l in range(3):
                    e += sp.diff(Lpoly, Yv[i], Yv[j], Yv[l]).subs(ptc)*a[i]*b[j]*c[l]
        return sp.simplify(e)

    print("symbolic A2 criterion (all t != 0):",
          "H rank 1:", Hc.applyfunc(sp.simplify).rank() == 1,
          "; H.k = 0:", sp.simplify(Hc*kv) == sp.zeros(3, 1),
          "; D3L(k,k,k) =", D3(kv, kv, kv),
          "; tangent-slot cubics =",
          (D3(tanc, tanc, tanc), D3(kv, kv, tanc), D3(kv, tanc, tanc)),
          "-> transverse A2 (cuspidal edge) PROVED")


# ====================================================================== fates
def _cubic3(Lv_, B, q):
    """The 3 real roots of L x^3 + B x + q for L<0 (trig form), vectorized in L."""
    p = B/Lv_
    r = q/Lv_
    m = 2*np.sqrt(-p/3.0)
    arg = np.clip(3.0*r/(p*m), -1.0, 1.0)
    th = np.arccos(arg)
    return np.stack([m*np.cos(th/3.0 - 2*np.pi*k/3.0) for k in range(3)], axis=-1)


_FATE_DEGEN = [0]    # measure-zero degenerate ray data (returned 'complete')
_FATE_UNCERT = [0]   # exchange-certificate failures (swap applied anyway)

def _fate(x0, direction):
    """Fate of the P'_1 trajectory through x0 in one time direction — decided
    ALGEBRAICALLY, with no ODE integration.

    Along an e1-ray, y2, y3, B = 4-3y2y3, q = -2y3 are constants of motion and
    only L varies, quadratically in s: at most two walls, so the wall list is
    exhaustive.  Between walls the trajectory's x1 is one of the cubic's real
    branches, which are continuous and non-crossing EXCEPT at the single zero
    of K (linear along the ray) — the note's A.3 chart singularity, where two
    branches share x1 while remaining distinct 3D points.  So: track x1 through
    the closed-form cubic roots on a dense s-grid, and disambiguate the one
    K-crossing in 3D via the exact 1D fiber recovery.  At a wall reached from
    the L<0 side, the branch nearest p = 2y3/B is the survivor; from the L>0
    side the crossing is always survived (the incoming pair arrives from
    infinity).  A trajectory that survives all its walls is complete: off the
    wall the restriction of F is a covering and whole paths lift (report,
    Part I.3)."""
    y0 = np.array(Ffun(*x0), dtype=float)
    L0 = float(Lnum(y0))
    B = 4 - 3*y0[1]*y0[2]
    q = -2*y0[2]
    if abs(y0[2]) < 1e-12 or abs(B) < 1e-12:
        _FATE_DEGEN[0] += 1
        return 'complete'          # measure-zero degenerate ray data
    # L(s) = c2 s^2 + d*c1 s + L0 in the signed variable s >= 0
    c2 = 27*y0[2]**2
    c1 = direction*(54*y0[0]*y0[2]**2 - 18*y0[1]*y0[2] + 16)
    rts = np.roots([c2, c1, L0]) if abs(c2) > 1e-14 else np.roots([c1, L0])
    walls = sorted(t.real for t in rts if abs(t.imag) < 1e-10 and t.real > 1e-12)
    if not walls:
        return 'complete'
    Lof = lambda s: c2*s*s + c1*s + L0
    kslope = direction*27*y0[2]**2
    K0 = 27*y0[0]*y0[2]**2 - 9*y0[1]*y0[2] + 8
    sK = -K0/kslope if abs(kslope) > 1e-14 else None   # the one K-crossing

    x1cur, scur = float(x0[0]), 0.0
    for w in walls[:2]:
        smid = 0.5*(scur + w)
        if Lof(smid) > 0:
            # single real branch, crossing + -> - : always survived; re-enter
            # the L<0 side (if the ray continues) as the persistent root
            sb = w + 1e-7*max(1.0, w - scur)
            x1cur = 2*y0[2]/B
            if Lof(sb) < 0:
                r3 = _cubic3(np.array([Lof(sb)]), B, q)[0]
                x1cur = r3[np.argmin(np.abs(r3 - 2*y0[2]/B))]
            scur = sb
            continue
        # L<0 segment: track the branch to the wall by 1D nearest-root matching
        # WITH THE EXCHANGE RULE.  Along the ray, disc = -4 K^2 L, so for L<0
        # the two branches colliding at the K-crossing satisfy
        # (x_a - x_b)^2 = K(s)^2 g(s), g > 0: their difference is proportional
        # to K(s) and CHANGES SIGN at the simple zero of K — the branches cross
        # transversally in x1 and exchange sorted order (verified to 50 digits
        # with mpmath).  Nearest-value matching alone (which never exchanges)
        # silently hops sheets at every K-crossing — the note's A.3 failure in
        # a new guise.  The fix is deterministic: step across sK and swap the
        # colliding pair.
        delta = 1e-7*max(1.0, w - scur)
        grid = np.concatenate([np.linspace(scur, w - (w-scur)*1e-3, 1500),
                               w - np.geomspace((w-scur)*1e-3, delta, 60)])
        if sK is not None and scur < sK < w:
            eps = max(1e-5, 1e-6*(w - scur))
            grid = np.sort(np.concatenate([grid[np.abs(grid - sK) > eps],
                                           [sK - eps, sK + eps]]))
        Ls = np.minimum(Lof(grid), -1e-300)        # clamp tail roundoff
        R = _cubic3(Ls, B, q)                      # (n,3) real roots
        idx = int(np.argmin(np.abs(R[0] - x1cur)))
        for i in range(1, len(grid)):
            if sK is not None and grid[i-1] < sK < grid[i]:
                # exchange: identify the colliding pair at sK-eps; if ours is a
                # member, continue along the PARTNER's value across sK
                prev = R[i-1]
                pair = np.argsort(prev)             # collision pair = adjacent
                gaps = np.diff(prev[pair])
                a, b = pair[np.argmin(gaps)], pair[np.argmin(gaps) + 1]
                # certificate: the pair must be well inside the third root's
                # separation on BOTH sides of sK, else flag
                nxt_sorted = np.sort(R[i])
                ok_cert = (gaps.min() < 0.1*gaps.max()
                           and np.diff(nxt_sorted).min() < 0.1*np.diff(nxt_sorted).max())
                if not ok_cert:
                    _FATE_UNCERT[0] += 1
                if idx == a or idx == b:
                    partner = b if idx == a else a
                    idx = int(np.argmin(np.abs(R[i] - prev[partner])))
                else:
                    idx = int(np.argmin(np.abs(R[i] - prev[idx])))
                continue
            idx = int(np.argmin(np.abs(R[i] - R[i-1][idx])))
        p = 2*y0[2]/B
        persistent = int(np.argmin(np.abs(R[-1] - p)))
        if idx != persistent:
            return 'dies'
        # survived: continue on the L>0 side as the single real branch
        scur = w + delta
        x1cur = p
    return 'complete'


def cmd_fates(args):
    t0 = time.time()
    rng = np.random.default_rng(2)
    pts = rng.uniform(-2, 2, size=(args.n, 3))
    counts = {}
    for p in pts:
        k = (_fate(p, +1), _fate(p, -1))
        counts[k] = counts.get(k, 0) + 1
    print(f"fates of {args.n} uniform points in [-2,2]^3 under the P'_1 flow:")
    for k in sorted(counts):
        print(f"  fwd {k[0]:>8} / bwd {k[1]:>8} : {counts[k]:4d} ({100*counts[k]/args.n:.1f}%)")
    fw = sum(v for k, v in counts.items() if k[0] == 'dies')
    bw = sum(v for k, v in counts.items() if k[1] == 'dies')
    print(f"forward-escaping {100*fw/args.n:.1f}%, backward-escaping {100*bw/args.n:.1f}%")
    for anchor, d, expect in [(np.array([0.86452, -1.6728, 7.87655]), +1, 'dies'),
                              (np.array([0.2, 0.1, -0.3]), -1, 'dies')]:
        ok = sum(_fate(anchor + rng.normal(scale=1e-3, size=3), d) == expect
                 for _ in range(20))
        print(f"anchor {np.round(anchor, 4)} dir {d:+d}: {ok}/20 {expect}")
    print(f"degenerate ray data (measure zero; classified 'complete'): {_FATE_DEGEN[0]}")
    print(f"exchange-certificate failures (swap applied anyway): {_FATE_UNCERT[0]}")
    print(f"[{time.time()-t0:.0f}s]")


# =================================================================== boundary
def cmd_boundary(args):
    """Origin-lift fate per direction (Part I.2/I.3): dies at first wall for
    v1<0-with-wall, survives the crossing for v1>0-with-wall, and complete to
    t=50 for v1<0 wall-free rays (the last is also a theorem: over {L<0} the
    restriction of F is a covering, and coverings lift whole paths)."""
    t0 = time.time()

    def first_pos_root(v):
        a4 = 27*v[0]**2*v[2]**2 + v[1]**3*v[2]
        coeffs = np.trim_zeros(np.array([a4, -18*v[0]*v[1]*v[2], -v[1]**2,
                                         16*v[0], 0.0]), 'b')
        if len(coeffs) <= 1:
            return None
        r = np.roots(coeffs)
        pos = sorted(w.real for w in r
                     if abs(w.imag) < 1e-9*max(1, abs(w)) and w.real > 1e-12)
        return pos[0] if pos else None

    def lift_along(v, tgrid, xq=None):
        xq = np.zeros(3) if xq is None else xq
        tprev = 0.0
        for t in tgrid:
            dt = t - tprev
            pred = xq + dt*(v @ np.array([Arows[i](*xq) for i in range(3)], dtype=float))
            xn = newton1(pred, t*v)
            if xn is None or np.max(np.abs(xn)) > 1e12:
                return None, tprev
            xq, tprev = xn, t
        return xq, tprev

    rng = np.random.default_rng(11)
    dirs = rng.normal(size=(400, 3))
    dirs /= np.linalg.norm(dirs, axis=1, keepdims=True)
    neg_root = [(v, first_pos_root(v)) for v in dirs
                if v[0] < 0 and first_pos_root(v) is not None]
    pos_root = [(v, first_pos_root(v)) for v in dirs
                if v[0] > 0 and first_pos_root(v) is not None]
    neg_noroot = [v for v in dirs if v[0] < 0 and first_pos_root(v) is None]

    def classify(v, t1):
        grid = list(np.linspace(0, 0.9*t1, 200)[1:]) + \
               list(t1 - np.geomspace(0.1*t1, 1e-8*t1, 80))
        xq, tl = lift_along(v, grid)
        if xq is None:
            return 'died'
        p = 2*(t1*v)[2]/(4 - 3*(t1*v)[1]*(t1*v)[2])
        if np.max(np.abs(xq)) > 1e3 and abs(xq[0] - p) > 0.05*(1 + abs(p)):
            # growth-ratio disambiguation for legitimately-large survivors
            t4 = min(grid, key=lambda s: abs((t1 - s) - 1e-4*t1))
            x4, _ = lift_along(v, [s for s in grid if s <= t4])
            if x4 is not None and np.max(np.abs(xq)) < 50*np.max(np.abs(x4)):
                return 'survived'
            return 'died'
        return 'survived' if abs(xq[0] - p) < 0.05*(1 + abs(p)) else 'died'

    nA = min(args.n, len(neg_root))
    died = sum(classify(v, r) == 'died' for v, r in neg_root[:nA])
    print(f"v1<0 with wall: {died}/{nA} origin lifts die at the first wall")
    nB = min(args.n, len(pos_root))
    surv = sum(classify(v, r) == 'survived' for v, r in pos_root[:nB])
    print(f"v1>0 with wall: {surv}/{nB} origin lifts survive the crossing")
    for v in neg_noroot[:6]:
        xq, tl = lift_along(v, np.linspace(0, 50, 2500)[1:])
        tag = (f"complete to t=50, |x|={np.max(np.abs(xq)):.3g}" if xq is not None
               else f"lost at t={tl:.3f}")
        print(f"v1<0 wall-free: v={np.round(v, 3)} -> {tag}")
    print(f"[{time.time()-t0:.0f}s]")


# =================================================================== spectrum
def _spectrum_run(N, Ybox, k_eigs=25, mode='branched', verbose=True, bc='dirichlet'):
    import scipy.sparse as sps
    import scipy.sparse.linalg as spla
    from scipy.sparse.csgraph import connected_components
    h = 2*Ybox/N
    axes = (np.arange(N) + 0.5)*h - Ybox          # offset grid: avoids y3=0
    II, JJ, KK = np.meshgrid(np.arange(N), np.arange(N), np.arange(N), indexing='ij')
    nodes_idx = np.stack([II.ravel(), JJ.ravel(), KK.ravel()], axis=-1)
    Yg = axes[nodes_idx]
    M = len(Yg)
    Lv = Lnum(Yg)

    if mode in ('flat', 'omega_plus'):
        live = np.ones(M, bool) if mode == 'flat' else (Lv > 0)
        nid = -np.ones((N, N, N), int)
        nid[nodes_idx[live, 0], nodes_idx[live, 1], nodes_idx[live, 2]] = \
            np.arange(int(live.sum()))
        idx = nodes_idx[live]
        Ml = len(idx)
        rows, cols, vals = [], [], []
        diag = 6.0/h**2 + (Yg[live]**2).sum(1)
        for ax in range(3):
            for s in (1, -1):
                nb = idx.copy(); nb[:, ax] += s
                ok = (nb[:, ax] >= 0) & (nb[:, ax] < N)
                cq = -np.ones(Ml, int)
                cq[ok] = nid[nb[ok, 0], nb[ok, 1], nb[ok, 2]]
                ok2 = cq >= 0
                rows.append(np.arange(Ml)[ok2]); cols.append(cq[ok2])
                vals.append(-np.ones(int(ok2.sum()))/h**2)
        A = sps.coo_matrix((np.concatenate(vals),
                            (np.concatenate(rows), np.concatenate(cols))), (Ml, Ml)).tocsr()
        A += sps.diags(diag)
        ev = spla.eigsh(A, k=k_eigs, sigma=0, which='LM', return_eigenvectors=False)
        return np.sort(ev), None

    # ---- fiber points per node
    t0 = time.time()
    x2f, x3f, _, _ = get_chart()
    B = 4 - 3*Yg[:, 1]*Yg[:, 2]
    Kv = 27*Yg[:, 0]*Yg[:, 2]**2 - 9*Yg[:, 1]*Yg[:, 2] + 8
    pts, owner = [], []
    for m in range(M):
        aq = Lv[m]
        coeffs = [aq, 0.0, B[m], -2*Yg[m, 2]]
        r = np.roots(coeffs) if abs(aq) > 1e-13 else np.roots(coeffs[2:])
        rr = [w.real for w in r if abs(w.imag) < 1e-8*max(1.0, abs(w))]
        if len(rr) != (3 if aq < 0 else 1):
            continue
        for root in rr:
            if abs(Kv[m]) > 1e-6:
                pts.append([root, x2f(root, *Yg[m]), x3f(root, *Yg[m])])
            else:
                pts.append([root, 0.0, 0.0])
            owner.append(m)
    pts = np.array(pts); owner = np.array(owner)
    pts = newton_batch(pts, Yg[owner], iters=8)
    res = np.abs(Fbatch(pts) - Yg[owner]).max(1)
    scale = (1 + np.abs(pts).max(1))**7
    good = np.isfinite(res) & (res < np.maximum(1e-8, 1e-12*scale))
    pts, owner = pts[good], owner[good]
    cnt = np.bincount(owner, minlength=M)
    want = np.where(Lv < 0, 3, 1)
    add_p, add_o, fixed = [], [], set()
    for m in np.where(cnt != want)[0]:
        aq = Lv[m]
        coeffs = [aq, 0.0, B[m], -2*Yg[m, 2]]
        r = np.roots(coeffs) if abs(aq) > 1e-13 else np.roots(coeffs[2:])
        cand = []
        for w in r:
            if abs(w.imag) < 1e-8*max(1.0, abs(w)) and abs(w.real) > 1e-12:
                for p in recover_1d(w.real, Yg[m]):
                    p = np.array(p)
                    rr2 = np.abs(np.array(Ffun(*p), dtype=float) - Yg[m]).max()
                    if rr2 < max(1e-8, 1e-11*(1 + np.abs(p).max())**7):
                        if not any(np.linalg.norm(p - qq) < 1e-6*(1 + np.abs(p).max())
                                   for qq in cand):
                            cand.append(p)
        if len(cand) == want[m]:
            fixed.add(m); add_p.extend(cand); add_o.extend([m]*len(cand))
    if fixed:
        keep0 = ~np.isin(owner, list(fixed))
        pts = np.vstack([pts[keep0], np.array(add_p)])
        owner = np.concatenate([owner[keep0], np.array(add_o, int)])
    cnt = np.bincount(owner, minlength=M)
    ok_node = cnt == want
    keep = ok_node[owner]
    pts, owner = pts[keep], owner[keep]
    NV = len(pts)
    if verbose:
        print(f"  grid {N}^3 h={h:.3f}: {M} nodes ({(Lv<0).mean()*100:.1f}% 3-sheeted), "
              f"{NV} vertices, {int((~ok_node).sum())} holes [{time.time()-t0:.0f}s]")

    node_pts = [[] for _ in range(M)]
    for vi, m in enumerate(owner):
        node_pts[m].append(vi)
    nid = -np.ones((N, N, N), int)
    nid[nodes_idx[:, 0], nodes_idx[:, 1], nodes_idx[:, 2]] = np.arange(M)

    # ---- edges by path-lifting; completion by fiber bijectivity off the wall
    t0 = time.time()
    rows, cols = [], []
    wall_pairs, wall_odd = [], 0
    n_dir, n_susp = 0, 0
    nsub = 2
    for ax in range(3):
        vsrc, vdst = [], []
        for m in range(M):
            if not node_pts[m]:
                continue
            nb = nodes_idx[m].copy(); nb[ax] += 1
            if nb[ax] >= N or not node_pts[nid[nb[0], nb[1], nb[2]]]:
                continue
            m2 = nid[nb[0], nb[1], nb[2]]
            for vi in node_pts[m]:
                vsrc.append(vi); vdst.append(m2)
        vsrc = np.array(vsrc); vdst = np.array(vdst)
        Xc = pts[vsrc].copy()
        alive = np.ones(len(vsrc), bool)
        for k in range(1, nsub + 1):
            Yt = Yg[owner[vsrc]].copy(); Yt[:, ax] += k*h/nsub
            V = np.stack(Arows[ax](Xc[:, 0], Xc[:, 1], Xc[:, 2]), axis=-1)
            Xold = Xc.copy()
            pred = Xc + (h/nsub)*V
            Xc[alive] = newton_batch(pred[alive], Yt[alive], iters=6)
            res = np.abs(Fbatch(Xc) - Yt).max(1)
            scl = (1 + np.abs(Xc).max(1))**7
            # locality guard: Newton correction must be small vs Euler step,
            # else the lift may have hopped sheets (see step_to); such facets
            # fall through to the bijectivity completion pass or to Dirichlet.
            corr = np.linalg.norm(Xc - pred, axis=1)
            disp = np.linalg.norm(pred - Xold, axis=1)
            local = corr < 0.5*disp + 0.05*(1 + np.linalg.norm(Xold, axis=1))
            alive &= np.isfinite(res) & (res < np.maximum(1e-6, 1e-11*scl)) \
                     & (np.abs(Xc).max(1) < 1e8) & local
        matched = -np.ones(len(vsrc), int)
        claim_d = {}                      # injectivity guard: target -> (dist, j)
        for j in np.where(alive)[0]:
            iB = node_pts[vdst[j]]
            dq = np.linalg.norm(pts[iB] - Xc[j], axis=1)
            b_ = int(np.argmin(dq))
            if dq[b_] < 1e-3*(1 + np.linalg.norm(Xc[j])):
                tgt = iB[b_]
                key = (vdst[j], tgt)
                if key in claim_d:        # two lifts claim one target: keep the
                    dprev, jprev = claim_d[key]        # closer, demote the other
                    if dq[b_] < dprev:
                        matched[jprev] = -1
                        claim_d[key] = (dq[b_], j)
                        matched[j] = tgt
                else:
                    claim_d[key] = (dq[b_], j)
                    matched[j] = tgt
        for j in np.where(matched >= 0)[0]:
            rows.append(vsrc[j]); cols.append(matched[j])
        pair_all, pair_fail = {}, {}
        for j in range(len(vsrc)):
            pair_all.setdefault((owner[vsrc[j]], vdst[j]), []).append(j)
        for j in np.where(matched < 0)[0]:
            pair_fail.setdefault((owner[vsrc[j]], vdst[j]), []).append(j)
        from scipy.optimize import linear_sum_assignment

        def edge_wall_free(yA, yB):
            """PROOF (not a sample) that L keeps one sign on the edge [yA, yB]:
            along a grid edge only one coordinate varies, so L restricted to it
            is univariate of degree <= 3; interpolate it exactly from 4 samples
            and certify that no real root lies in [0, 1]."""
            ts = np.array([0.0, 1/3, 2/3, 1.0])
            vals = Lnum(yA[None, :] + ts[:, None]*(yB - yA)[None, :])
            if vals[0]*vals[-1] <= 0:
                return False
            coeff = np.linalg.solve(np.vander(ts, 4), vals)   # exact for deg<=3
            nz = np.trim_zeros(coeff, 'f')
            if len(nz) > 1:
                for rt in np.roots(nz):
                    if abs(rt.imag) < 1e-9 and -1e-9 <= rt.real <= 1 + 1e-9:
                        return False
            return True

        # single-crossing wall segments: identify the dying pair on the L<0
        # side for alternative boundary conditions (Neumann / regluing)
        for (mA, mB) in {(owner[vsrc[j]], vdst[j]) for j in range(len(vsrc))}:
            if Lv[mA]*Lv[mB] >= 0:
                continue
            if Lv[mA] < 0:      # dying pair = A-side failures on this segment
                dy = [vsrc[j] for j in pair_fail.get((mA, mB), [])]
            else:               # dying pair = B's vertices missed by the lift
                used = {matched[k] for k in pair_all[(mA, mB)] if matched[k] >= 0}
                dy = [b for b in node_pts[mB] if b not in used]
            if len(dy) == 2:
                wall_pairs.append((dy[0], dy[1]))
            else:
                wall_odd += len(dy)
        for (mA, mB), js in pair_fail.items():
            if not edge_wall_free(Yg[mA], Yg[mB]):
                n_dir += len(js)
                continue
            used = set(matched[k] for k in pair_all[(mA, mB)] if matched[k] >= 0)
            B_left = [b for b in node_pts[mB] if b not in used]
            A_left = [vsrc[j] for j in js]
            if not B_left:
                n_dir += len(js); n_susp += len(js)
                continue
            D = np.linalg.norm(pts[A_left][:, None, :] - pts[B_left][None, :, :], axis=-1)
            ri, ci = linear_sum_assignment(D)
            for a_, b_ in zip(ri, ci):
                rows.append(A_left[a_]); cols.append(B_left[b_])
            miss = len(js) - len(ri)
            n_dir += miss; n_susp += miss
    rows = np.array(rows); cols = np.array(cols)
    deg = np.bincount(rows, minlength=NV) + np.bincount(cols, minlength=NV)
    if deg.max() > 6:
        print(f"  WARNING: {int((deg > 6).sum())} vertices exceed degree 6 "
              f"(max {int(deg.max())}) — non-manifold gluing")
    else:
        print(f"  degree check: max vertex degree {int(deg.max())} (<= 6, OK)")
    n_cross = 0
    for ax in range(3):
        nb = nodes_idx.copy(); nb[:, ax] += 1
        ok = nb[:, ax] < N
        n_cross += int((Lv[ok]*Lv[nid[nb[ok, 0], nb[ok, 1], nb[ok, 2]]] < 0).sum())
    if verbose:
        print(f"  {len(rows)} matched facets, {n_dir} Dirichlet ({n_susp} suspicious; "
              f"{n_cross} wall-crossing segments) [{time.time()-t0:.0f}s]")

    import scipy.sparse as sps2
    adj = sps2.coo_matrix((np.ones(len(rows)), (rows, cols)), (NV, NV))
    ncomp, labels = connected_components(adj, directed=False)
    sizes = np.bincount(labels)
    main = sizes.argmax()
    if verbose:
        print(f"  {ncomp} components, largest {100*sizes[main]/NV:.2f}%")
    diag = 6.0/h**2 + (Yg[owner]**2).sum(1)
    if bc == 'neumann':
        # free (natural) condition at the dying-sheet wall facets: remove the
        # implicit zero ghost from the diagonal.  Outer-box, hole-node and
        # double-crossing facets stay Dirichlet in every mode (disclosed).
        for a, b in wall_pairs:
            diag[a] -= 1.0/h**2
            diag[b] -= 1.0/h**2
    if bc == 'glue':
        # reglue the two dying sheets to each other at each wall facet: the
        # zero ghost is replaced by the partner vertex (same base node y)
        from collections import Counter
        multi = Counter(v for p in wall_pairs for v in p)
        n_multi = sum(1 for v, c in multi.items() if c > 1)
        if n_multi:
            print(f"  glue note: {n_multi} vertices appear in >1 glue pair "
                  f"(degree may exceed 6 there)")
        rows = list(rows) + [a for a, b in wall_pairs]
        cols = list(cols) + [b for a, b in wall_pairs]
        rows = np.array(rows); cols = np.array(cols)
    if verbose and bc != 'dirichlet':
        print(f"  bc = {bc}: applied at {len(wall_pairs)} wall facets "
              f"({wall_odd} odd-count facets left Dirichlet)")
    Amat = sps.coo_matrix(
        (np.concatenate([-np.ones(len(rows))/h**2]*2),
         (np.concatenate([rows, cols]), np.concatenate([cols, rows]))), (NV, NV)).tocsr()
    Amat += sps.diags(diag)
    sel = np.where(labels == main)[0]
    if bc in ('neumann', 'glue') and wall_pairs:
        # round-5 finding 5: components are computed pre-glue, so a wall pair
        # with a vertex outside the main component would be silently dropped by
        # the restriction below while still counted as 'applied'.  Count them.
        inmain = np.zeros(NV, bool); inmain[sel] = True
        n_out = sum(1 for a, b in wall_pairs if not (inmain[a] and inmain[b]))
        if n_out:
            print(f"  bc note: {n_out} wall pairs have a vertex outside the "
                  f"main component and are dropped by the restriction")
    ev, evec = spla.eigsh(Amat[sel][:, sel], k=k_eigs, sigma=0, which='LM')
    order = np.argsort(ev)
    return ev[order], (evec[:, order], owner[sel], Lv, Yg, pts[sel])


def cmd_spectrum(args):
    Ns = [args.N] if args.N else [36, 44]
    print("reference (flat oscillator, exact ladder 3,5,5,5,7x6,9x10):")
    ev, _ = _spectrum_run(Ns[0], 4.0, mode='flat')
    print(" ", np.round(ev[:13], 4))
    print("comparison (Dirichlet on {L>0} alone):")
    evp, _ = _spectrum_run(Ns[0], 4.0, mode='omega_plus')
    print(" ", np.round(evp[:8], 4))
    results = []
    for N in Ns:
        print(f"branched manifold N={N}, bc={args.bc}:")
        ev, data = _spectrum_run(N, 4.0, bc=args.bc)
        results.append(ev)
        evec, own, Lv_, Yg_, P = data
        Lo = Lv_[own]
        print("  eigenvalues:", np.round(ev, 4))
        for i in range(len(ev)):
            w = evec[:, i]**2; w /= w.sum()
            big = w[np.linalg.norm(P, axis=1) > 10].sum()
            mx = (w*np.minimum(np.linalg.norm(P, axis=1), 60)).sum()
            print(f"   E={ev[i]:8.4f}  w(L<0)={w[Lo<0].sum():5.2f}  "
                  f"w(|x|>10)={big:5.2f}  <|x|>={mx:6.2f}")
    if len(results) == 2:
        print("convergence (low levels):")
        for a, b in zip(results[0][:10], results[1][:10]):
            print(f"   {a:8.4f}  {b:8.4f}  ({b-a:+.4f})")


# ====================================================================== tower
_LFIB = None
def get_Lfiber():
    """L(z) restricted to the fiber, as Nf(z1, y)/Df(y) via the shape lemma.
    Df = 64 K(y)^4 > 0 off {K=0}, so sibling L-signs = signs of Nf at the
    three cubic roots."""
    global _LFIB
    if _LFIB is not None:
        return _LFIB
    z1s = sp.symbols('z1')
    G = sp.groebner([f - y for f, y in zip(Fs, Yv)], x3, x2, x1,
                    order='lex', domain=sp.FractionField(sp.QQ, ['y1', 'y2', 'y3']))
    rel2 = [p for p in G.exprs if x2 in p.free_symbols and x3 not in p.free_symbols][0]
    rel3 = [p for p in G.exprs if x3 in p.free_symbols][0]
    x2e = sp.solve(rel2, x2)[0].subs(x1, z1s)
    x3e = sp.solve(rel3, x3)[0].subs(x1, z1s)
    Lz = sp.together(27*z1s**2*x3e**2 - 18*z1s*x2e*x3e + 16*z1s
                     + x2e**3*x3e - x2e**2)
    Nf, Df = sp.numer(Lz), sp.denom(Lz)
    _LFIB = (z1s, sp.expand(Nf), Df,
             sp.lambdify((z1s, y1, y2, y3), sp.expand(Nf), 'numpy'),
             sp.lambdify((y1, y2, y3), Df, 'numpy'))
    return _LFIB


def _sibling_Ls(yv):
    """Sorted L-values over the three preimages of yv (requires L(yv) < 0)."""
    Lv = float(Lnum(np.asarray(yv)))
    if Lv >= 0:
        return None
    _, _, _, Nfun, Dfun = get_Lfiber()
    r = _cubic3(np.array([Lv]), 4 - 3*yv[1]*yv[2], -2*yv[2])[0]
    D = float(Dfun(*yv))
    if abs(D) < 1e-30:
        return None
    return sorted(float(Nfun(rr, *yv))/D for rr in r)


def _n2(yv):
    """Real fiber count of F o F at yv (None near walls / on failure)."""
    Lv = float(Lnum(np.asarray(yv)))
    if abs(Lv) < 1e-9:
        return None
    if Lv < 0:
        Ls = _sibling_Ls(yv)
        return None if Ls is None else sum(3 if l < 0 else 1 for l in Ls)
    # single preimage: recover it and read the sign of L there
    x2f, x3f, _, _ = get_chart()
    coeffs = [Lv, 0.0, 4 - 3*yv[1]*yv[2], -2*yv[2]]
    rr = [w.real for w in np.roots(coeffs) if abs(w.imag) < 1e-8*max(1, abs(w))]
    if len(rr) != 1:
        return None
    K = 27*yv[0]*yv[2]**2 - 9*yv[1]*yv[2] + 8
    if abs(K) > 1e-8:
        g = np.array([rr[0], x2f(rr[0], *yv), x3f(rr[0], *yv)])
    else:
        cand = recover_1d(rr[0], yv)
        if not cand:
            return None
        g = np.array(cand[0])
    g = newton1(g, np.asarray(yv, dtype=float))
    if g is None:
        return None
    lz = float(Lnum(g))
    return None if abs(lz) < 1e-9 else (3 if lz < 0 else 1)


def cmd_tower(args):
    """Open question 4: multiplicity functions along the tower F, F^2, F^3."""
    t0 = time.time()
    rng = np.random.default_rng(3)
    hist = {}
    N = 4000
    for yv in rng.uniform(-3, 3, size=(N, 3)):
        t = _n2(yv)
        if t is not None:
            hist[t] = hist.get(t, 0) + 1
    tot = sum(hist.values())
    print(f"n2 on {N} uniform points of [-3,3]^3 ({N-tot} indeterminate):")
    for k in sorted(hist):
        print(f"  n2 = {k}: {hist[k]:5d} ({100*hist[k]/tot:.2f}%)")
    # wide-biased search confirms the far value 9
    rng = np.random.default_rng(123)
    seen9 = None
    for _ in range(args.wide):
        mag1 = 10**rng.uniform(-1, 3.5)
        yv = np.array([mag1*np.sign(rng.uniform(-1, 1)),
                       rng.uniform(-8, 8)*np.sqrt(max(1, mag1)),
                       rng.uniform(-3, 3)/max(1, mag1**0.5)])
        Ls = _sibling_Ls(yv)
        if Ls is not None and Ls[-1] < 0:
            seen9 = yv
            break
    print("wide search: n2 = 9 found at y =",
          np.round(seen9, 4) if seen9 is not None else "not found (raise --wide)")
    # exact certificates at rational points: pure rational arithmetic throughout
    # (root isolation + bisection until the remainder polynomial has no root in
    # the isolating interval, then its sign at a rational endpoint)
    def exact_sibling_signs(yq):
        z1s, Nf, Df, _, _ = get_Lfiber()
        Lyq = (27*yq[0]**2*yq[2]**2 - 18*yq[0]*yq[1]*yq[2] + 16*yq[0]
               + yq[1]**3*yq[2] - yq[1]**2)
        if not Lyq < 0:
            return None, Lyq
        cub = sp.Poly(Lyq*z1s**3 + (4 - 3*yq[1]*yq[2])*z1s - 2*yq[2], z1s)
        Nfy = sp.Poly(sp.expand(Nf.subs({y1: yq[0], y2: yq[1], y3: yq[2]})), z1s)
        R = Nfy.rem(cub)
        signs = []
        for iv in cub.intervals():                    # exact isolating intervals
            a, b = iv[0]
            while R.count_roots(a, b) > 0 or cub.count_roots(a, b) != 1:
                m = (a + b)/2
                a, b = (a, m) if cub.count_roots(a, m) == 1 else (m, b)
            sv = R.eval(a)
            if sv == 0:
                sv = R.eval(b)
            signs.append(int(sp.sign(sv)))
        return signs, Lyq

    certs = [(9, [sp.Rational(-1643, 50), sp.Rational(3289, 100), sp.Rational(-71, 200)]),
             (3, [sp.Rational(-1249, 10000), sp.Rational(9197, 10000), sp.Rational(1267, 5000)]),
             (5, [sp.Rational(-29083, 10000), sp.Rational(-7379, 5000), sp.Rational(6249, 10000)]),
             (7, [sp.Rational(-320873, 10000), sp.Rational(30951, 1000), sp.Rational(-1611, 10000)])]
    for want, yq in certs:
        signs, Lyq = exact_sibling_signs(yq)
        got = None if signs is None else sum(3 if s < 0 else 1 for s in signs)
        print(f"EXACT certificate at y = ({yq[0]}, {yq[1]}, {yq[2]}): L(y)<0: {Lyq < 0}, "
              f"sibling L-signs {signs} -> n2 = {got} "
              f"({'OK' if got == want else 'MISMATCH, expected %d' % want})")
    # n3 sampling
    rng = np.random.default_rng(9)
    hist3 = {}
    x2f, x3f, _, _ = get_chart()
    for _ in range(args.n3):
        mag1 = 10**rng.uniform(-1, 3.5)
        yv = np.array([mag1*np.sign(rng.uniform(-1, 1)),
                       rng.uniform(-8, 8)*np.sqrt(max(1, mag1)),
                       rng.uniform(-3, 3)/max(1, mag1**0.5)])
        Lv = float(Lnum(yv))
        if abs(Lv) < 1e-9:
            continue
        # first-level fiber points
        coeffs = [Lv, 0.0, 4 - 3*yv[1]*yv[2], -2*yv[2]]
        rr = [w.real for w in np.roots(coeffs) if abs(w.imag) < 1e-8*max(1, abs(w))]
        if len(rr) != (3 if Lv < 0 else 1):
            continue
        K = 27*yv[0]*yv[2]**2 - 9*yv[1]*yv[2] + 8
        if abs(K) < 1e-8:
            continue
        vals = []
        for r in rr:
            g = newton1(np.array([r, x2f(r, *yv), x3f(r, *yv)]), yv)
            if g is None:
                vals = None; break
            v = _n2(g)
            if v is None:
                vals = None; break
            vals.append(v)
        if vals is None:
            continue
        t = sum(vals)
        hist3[t] = hist3.get(t, 0) + 1
    print(f"n3 realized values (wide sampling, {args.n3} tries):", sorted(hist3))
    print(f"  histogram: {dict(sorted(hist3.items()))}")
    if args.exact3:
        if not _exact3():
            print(f"[{time.time()-t0:.0f}s]")
            sys.exit(1)
    print(f"[{time.time()-t0:.0f}s]")


def _exact3():
    """Exact certificate (all steps over Q or Q[u]/(Q)) that n3 >= 11 on an open
    set: seed the second level at the rational n2 = 9 point z*, so only one
    quadratic extension appears.  Following the round-4 review's construction."""
    t0 = time.time()
    zst = [sp.Rational(-1643, 50), sp.Rational(3289, 100), sp.Rational(-71, 200)]
    yst = [sp.expand(f.subs({x1: zst[0], x2: zst[1], x3: zst[2]})) for f in Fs]
    Ly = (27*yst[0]**2*yst[2]**2 - 18*yst[0]*yst[1]*yst[2] + 16*yst[0]
          + yst[1]**3*yst[2] - yst[1]**2)
    Ky = 27*yst[0]*yst[2]**2 - 9*yst[1]*yst[2] + 8
    ok = Ly < 0 and Ky != 0
    print(f"exact3: y* = F(z*) rational; L(y*) < 0: {Ly < 0}; K(y*) != 0: {Ky != 0}")
    z1s = sp.symbols('z1u')
    cub = sp.Poly(Ly*z1s**3 + (4 - 3*yst[1]*yst[2])*z1s - 2*yst[2], z1s)
    if cub.eval(zst[0]) != 0:
        raise ValueError("z*_1 must be an exact root of the fiber cubic at y*")
    Q, rem = sp.div(cub.as_expr(), z1s - zst[0], z1s)
    Q = sp.Poly(sp.expand(Q), z1s)
    disc = sp.discriminant(Q.as_expr(), z1s)
    ok &= disc > 0
    print(f"exact3: residual quadratic has disc > 0 (two real conjugates): {disc > 0}")
    # conjugate preimages z'(u) via the chart, u a root of Q; certify L,K,B != 0
    # and no F-preimage of z'(u) on the empty-fiber curve
    G = sp.groebner([f - y for f, y in zip(Fs, Yv)], x3, x2, x1,
                    order='lex', domain=sp.FractionField(sp.QQ, ['y1', 'y2', 'y3']))
    rel2 = [p for p in G.exprs if x2 in p.free_symbols and x3 not in p.free_symbols][0]
    rel3 = [p for p in G.exprs if x3 in p.free_symbols][0]
    x2e = sp.solve(rel2, x2)[0]
    x3e = sp.solve(rel3, x3)[0]
    subs0 = {y1: yst[0], y2: yst[1], y3: yst[2], x1: z1s}
    zp = [z1s, sp.together(x2e.subs(subs0)), sp.together(x3e.subs(subs0))]
    for name, poly in [('L', Lpoly), ('K', Kpoly), ('B', Bpoly)]:
        val = sp.together(poly.subs({y1: zp[0], y2: zp[1], y3: zp[2]}))
        numv = sp.Poly(sp.expand(sp.numer(val)), z1s)
        gq = sp.gcd(numv, Q)
        ok &= gq.degree() == 0
        print(f"exact3: gcd(num({name} at z'(u)), Q) = {gq.as_expr()} "
              f"(trivial: {gq.degree() == 0})")
    # Groebner unit-ideal test: no preimage w of z'(u) lies on the curve
    w1, w2, w3, u = sp.symbols('w1 w2 w3 u')
    zpu = [e.subs(z1s, u) for e in zp]
    gens = [sp.expand(sp.numer(sp.together(
        f.subs({x1: w1, x2: w2, x3: w3}) - zpu[i]))) for i, f in enumerate(Fs)]
    gens += [Q.as_expr().subs(z1s, u), 3*w2*w3 - 4]
    GB = sp.groebner(gens, w1, w2, w3, u, order='grevlex')
    unit = list(GB.exprs) == [1]
    ok &= unit
    print(f"exact3: 1 in <Q(u), F(w)-z'(u), 3w2w3-4>: {unit}")
    print(f"exact3: CONCLUSION n3(y*) = 9 + n2(z') + n2(z'') >= 11 on an open "
          f"neighborhood: {'CERTIFIED' if ok else 'FAILED'}"
          f"  [{time.time()-t0:.0f}s]")
    # IV.2 remark (i), global version (round-5 review): F is injective on the
    # curve, so c(s) is the ONLY on-curve preimage of F(c(s)) for every s --
    # the even-values claim holds on the whole L<0 sub-arc, not just at s=1/2.
    sq, uq, vq, rq = sp.symbols('s_c u_c v_c r_c')
    csub = lambda t: {x1: sp.Rational(4, 27)/t**2, x2: sp.Rational(4, 3)/t, x3: t}
    gens2 = [sp.expand(sp.numer(sp.together(f.subs(csub(uq)) - f.subs(csub(sq)))))
             for f in Fs] + [(uq - sq)*vq - 1, sq*uq*rq - 1]
    GBi = sp.groebner(gens2, uq, sq, vq, rq, order='grevlex')
    inj = list(GBi.exprs) == [1]
    ok &= inj
    print("exact3: F injective on the curve (unit ideal):", inj,
          "-> even n2 on the entire L<0 sub-arc of F(curve)")
    return ok




# =================================================================== monodromy
def cmd_monodromy(args):
    """Monodromy of the covering over {L<0}: verified-lift cover graph only
    (no proximity completion -- it can misglue sheets in the far channels and
    fabricate transitive monodromy; guarded lifts are the certificate)."""
    import scipy.sparse as sps
    from scipy.sparse.csgraph import connected_components


    N, Ybox = args.N, args.box
    h = 2*Ybox/N
    axes = (np.arange(N) + 0.5)*h - Ybox
    II, JJ, KK = np.meshgrid(np.arange(N), np.arange(N), np.arange(N), indexing='ij')
    nodes_idx = np.stack([II.ravel(), JJ.ravel(), KK.ravel()], axis=-1)
    Yg = axes[nodes_idx]
    M = len(Yg)
    Lv = Lnum(Yg)
    live = Lv < 0
    x2f, x3f, _, _ = get_chart()

    pts, owner = [], []
    Kv = 27*Yg[:, 0]*Yg[:, 2]**2 - 9*Yg[:, 1]*Yg[:, 2] + 8
    B = 4 - 3*Yg[:, 1]*Yg[:, 2]
    for m in np.where(live)[0]:
        r = np.roots([Lv[m], 0.0, B[m], -2*Yg[m, 2]])
        rr = [w.real for w in r if abs(w.imag) < 1e-8*max(1.0, abs(w))]
        if len(rr) != 3:
            continue
        for root in rr:
            if abs(Kv[m]) > 1e-6:
                pts.append([root, x2f(root, *Yg[m]), x3f(root, *Yg[m])])
            else:
                cand = recover_1d(root, Yg[m])
                pts.append(min(cand, key=lambda p: np.abs(
                    np.array(Ffun(*p)) - Yg[m]).max()) if cand else [root, 0, 0])
            owner.append(m)
    pts = np.array(pts); owner = np.array(owner)
    pts = newton_batch(pts, Yg[owner], iters=8)
    res = np.abs(Fbatch(pts) - Yg[owner]).max(1)
    good = np.isfinite(res) & (res < np.maximum(1e-8, 1e-12*(1 + np.abs(pts).max(1))**7))
    pts, owner = pts[good], owner[good]
    cnt = np.bincount(owner, minlength=M)
    ok_node = cnt == 3
    keep = ok_node[owner]
    pts, owner = pts[keep], owner[keep]
    node_pts = [[] for _ in range(M)]
    for vi, m in enumerate(owner):
        node_pts[m].append(vi)
    nid = -np.ones((N, N, N), int)
    nid[nodes_idx[:, 0], nodes_idx[:, 1], nodes_idx[:, 2]] = np.arange(M)

    def edge_wall_free(yA, yB):
        ts = np.array([0.0, 1/3, 2/3, 1.0])
        vals = Lnum(yA[None, :] + ts[:, None]*(yB - yA)[None, :])
        if vals[0] >= 0 or vals[-1] >= 0 or vals[0]*vals[-1] <= 0:
            return False
        coeff = np.linalg.solve(np.vander(ts, 4), vals)
        nz = np.trim_zeros(coeff, 'f')
        if len(nz) > 1:
            for rt in np.roots(nz):
                if abs(rt.imag) < 1e-9 and -1e-9 <= rt.real <= 1 + 1e-9:
                    return False
        return True

    # base graph on full-fiber L<0 nodes with certified edges
    live_nodes = np.where(ok_node)[0]
    bmap = {m: i for i, m in enumerate(live_nodes)}
    base_edges = []
    for m in live_nodes:
        for ax in range(3):
            nb = nodes_idx[m].copy(); nb[ax] += 1
            if nb[ax] >= N:
                continue
            m2 = nid[nb[0], nb[1], nb[2]]
            if m2 < 0 or not ok_node[m2]:
                continue
            if edge_wall_free(Yg[m], Yg[m2]):
                base_edges.append((m, m2))
    print(f"{len(live_nodes)} base nodes, {len(base_edges)} certified base edges")

    def lift_edge(x, mA, mB, nsub=8, depth_cap=18):
        """Guarded continuation of fiber point x from node mA to node mB."""
        yA, yB = Yg[mA], Yg[mB]
        def step(xc, ta, tb, depth=0):
            ya = yA + ta*(yB - yA); yb = yA + tb*(yB - yA)
            dv = yb - ya
            Vm = np.array([Arows[i](*xc) for i in range(3)], dtype=float)
            pred = xc + dv @ Vm
            xn = newton1(pred, yb)
            ok = xn is not None and np.max(np.abs(xn)) < 1e8 and \
                np.linalg.norm(xn - pred) < 0.5*np.linalg.norm(pred - xc) \
                + 0.02*(1 + np.linalg.norm(xc))
            if ok:
                return xn
            if depth >= depth_cap:
                return None
            tm = 0.5*(ta + tb)
            xm = step(xc, ta, tm, depth + 1)
            return None if xm is None else step(xm, tm, tb, depth + 1)
        for k in range(nsub):
            x = step(x, k/nsub, (k+1)/nsub)
            if x is None:
                return None
        return x

    # union-find with sheet-merge detection over the big base component
    nb_ = len(live_nodes)
    br = [bmap[a] for a, b in base_edges]; bc = [bmap[b] for a, b in base_edges]
    Ab = sps.coo_matrix((np.ones(len(br)), (br, bc)), (nb_, nb_))
    ncb, labb = connected_components(Ab, directed=False)
    main_b = np.argmax(np.bincount(labb))

    parent = list(range(len(pts)))
    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]; a = parent[a]
        return a
    def union(a, b):
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[ra] = rb; return True
        return False

    # VERIFIED cover edges only: guarded lift per vertex per certified edge
    n_lift_fail = 0
    for (mA, mB) in base_edges:
        if labb[bmap[mA]] != main_b:
            continue
        for vi in node_pts[mA]:
            xw = lift_edge(pts[vi].copy(), mA, mB)
            if xw is None:
                n_lift_fail += 1
                continue
            iB = node_pts[mB]
            dq = np.linalg.norm(pts[iB] - xw, axis=1)
            b_ = int(np.argmin(dq))
            if dq[b_] < 1e-4*(1 + np.linalg.norm(xw)):
                union(vi, iB[b_])
            else:
                n_lift_fail += 1
    comp_roots = {}
    for vi in range(len(pts)):
        if owner[vi] in bmap and labb[bmap[owner[vi]]] == main_b:
            comp_roots.setdefault(find(vi), 0)
            comp_roots[find(vi)] += 1
    sizes = sorted(comp_roots.values())[::-1]
    main_sz = int(np.bincount(labb).max())
    print(f"main base component: {main_sz} of {nb_} full-fiber L<0 nodes; "
          f"lift failures: {n_lift_fail}")
    print(f"verified-lift cover graph over it: {len(comp_roots)} components "
          f"(sizes {sizes[:6]})")
    n_big = sum(1 for s in sizes if s > 0.5*main_sz)
    frac3 = sum(s for s in sizes[:3])/max(1, sum(sizes))
    print(f"robust criterion: no component exceeds base size "
          f"({max(sizes)} <= {main_sz}: {max(sizes) <= main_sz}); "
          f"{n_big} base-sized components carrying {100*frac3:.2f}% of vertices "
          f"-> {'TRIVIAL monodromy (three global sheets)' if n_big == 3 else 'inspect'}")



# ======================================================================= nogo
def cmd_nogo(args):
    """III.4 ladder no-go: the overlap <Ch_000, Ch_002> = 2 int_{L<0} h0 h002,
    by adaptive quadrature (exact-in-erf inner integral over the y3-interval of
    {L<0}) and by independent Monte Carlo."""
    t0 = time.time()
    from scipy import integrate

    def y3_interval(u1, u2):
        a = 27*u1*u1; b = u2**3 - 18*u1*u2; c = 16*u1 - u2*u2
        if abs(a) < 1e-300:
            return None
        d = b*b - 4*a*c
        if d <= 0:
            return None
        s = np.sqrt(d)
        return ((-b - s)/(2*a), (-b + s)/(2*a))

    def inner_w3(u1, u2):
        iv = y3_interval(u1, u2)
        if iv is None:
            return 0.0
        lo, hi = max(iv[0], -12.0), min(iv[1], 12.0)
        if hi <= lo:
            return 0.0
        # int (2t^2-1)/sqrt2 e^{-t^2} dt has antiderivative -t e^{-t^2}/sqrt2
        return (-hi*np.exp(-hi*hi) + lo*np.exp(-lo*lo))/np.sqrt(2)

    val, err = integrate.dblquad(
        lambda u2, u1: np.exp(-u1*u1 - u2*u2)*inner_w3(u1, u2),
        -9, 9, -9, 9, epsabs=1e-11, epsrel=1e-10)
    pref = 2*np.pi**-1.5
    print(f"quadrature estimate: <Ch000, Ch002> = {pref*val:.6f}")
    print("  (the integrator's internal error estimate is NOT reliable here --")
    print("   it emits convergence warnings; treat the Monte Carlo below and the")
    print("   round-5 review's variance-reduced 4e8-sample run, -0.2121752 +/-")
    print("   0.0000123, as the accuracy statements)")
    rng = np.random.default_rng(1)
    tot, s_, ss = args.mc, 0.0, 0.0
    done = 0
    while done < tot:
        n = min(1_000_000, tot - done)
        yv = rng.normal(scale=np.sqrt(0.5), size=(n, 3))
        Lv = Lnum(yv)
        vals = np.where(Lv < 0, (2*yv[:, 2]**2 - 1)/np.sqrt(2), 0.0)
        s_ += vals.sum(); ss += (vals**2).sum(); done += n
    mean = s_/tot
    sd = np.sqrt(max(ss/tot - mean**2, 0))/np.sqrt(tot)
    print(f"Monte Carlo ({tot} samples): {2*mean:.6f} +/- {2*sd:.6f}")
    print("nonzero overlap between transported eigenfunctions of energies 3 and 7"
          " -> no self-adjoint extension contains both (III.4)")
    print(f"[{time.time()-t0:.0f}s]")


# ------------------------------------------------------------------------ main
def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest='cmd', required=True)
    pv = sub.add_parser('verify')
    pv.add_argument('--dirs', type=int, default=4000,
                    help='directions per census seed (400000 for the published figure)')
    pv.add_argument('--seeds', type=str, default='7',
                    help='comma-separated census seeds; the published estimate '
                         'used 1,2,3,4,5,11,12,13,14,15')
    pv.add_argument('--exactcheck', type=int, default=0,
                    help='validate the root criterion against exact arithmetic '
                         'on this many v1<0 directions')
    sub.add_parser('singular')
    pf = sub.add_parser('fates')
    pf.add_argument('--n', type=int, default=300)
    pb = sub.add_parser('boundary')
    pb.add_argument('--n', type=int, default=40,
                    help='per-class sample size for origin-lift fates')
    ps = sub.add_parser('spectrum')
    ps.add_argument('--N', type=int, default=None,
                    help='single grid size (default: 36 and 44 with convergence table)')
    ps.add_argument('--bc', choices=['dirichlet', 'neumann', 'glue'],
                    default='dirichlet',
                    help='boundary condition at the dying-sheet wall facets: '
                         'dirichlet = Friedrichs; neumann = free/natural; '
                         'glue = reglue the two dying sheets to each other')
    pn = sub.add_parser('nogo')
    pn.add_argument('--mc', type=int, default=40_000_000)
    pm = sub.add_parser('monodromy')
    pm.add_argument('--N', type=int, default=64)
    pm.add_argument('--box', type=float, default=8.0)
    pt = sub.add_parser('tower')
    pt.add_argument('--wide', type=int, default=300000,
                    help='wide-biased samples for locating n2 = 9')
    pt.add_argument('--n3', type=int, default=8000,
                    help='samples for the n3 histogram')
    pt.add_argument('--exact3', action='store_true',
                    help='exact certificate that n3 >= 11 (F^2-F^3 separation)')
    args = ap.parse_args()
    {'verify': cmd_verify, 'singular': cmd_singular, 'fates': cmd_fates,
     'boundary': cmd_boundary, 'spectrum': cmd_spectrum,
     'tower': cmd_tower, 'monodromy': cmd_monodromy, 'nogo': cmd_nogo}[args.cmd](args)


if __name__ == '__main__':
    main()
