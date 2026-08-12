#!/usr/bin/env python3
"""Family hunt, phase 0: same-degree members of the Gallagher family.

Question 4's completeness half (report section IV.5) asks whether the
fiber-count multiplicity function is a COMPLETE invariant of the quantized
Keller maps. It was written as blocked on unavailable family members; the
published counterexample families (arXiv:2608.00222; Gallagher's atlas,
jacobianfun.org/counterexamples) lift the block: the weighted-lift
construction is parametrized by an auxiliary polynomial H with n simple
roots {0, r_2, ..., r_n}, 1 not a root, satisfying the endpoint identity
prod(1 - r_i) = prod_{i>=2}(-r_i), lambda != 0, H''(1) != -2 -- so each
fiber degree n carries a moduli of genuinely distinct members.

This script builds two distinct n = 4 members exactly:
  A: roots [0, -1, 3, 4]      (the atlas row)
  B: roots [0, -1, -2, 3/2]   (alternative solution of the endpoint identity)
verifies both are Keller maps (det J == 1 identically, all components
polynomial), that they differ as polynomial maps, and takes first exact
fiber-count measurements (Groebner eliminant + Sturm count per rational
sample point).

Phase 1 (fiber determination, C != 0): for any target (A,B,C) with
C != 0, the w = u*gamma values of the preimages are exactly the real
roots of

    E(w) = -H(w) + w*(H'(0) + B*C) - A*C^2        (constant leading coeff!)

with the chart x = C/(B*C - p(w)), u = w*x/C, y = (u-1)/x,
z = (gamma-1-a*(u-1))/x^2 lifting each root off the escape locus
{B*C = p(w)}. Since C != 0 forces x != 0 at every preimage,
n1 = count_roots(E) EXACTLY off the guarded (measure-zero) strata.
No Groebner per point. Structural fact (verified at import): the guard
polynomial B*C - p(w) is exactly E'(w), so the gcd(E, guard) check is
precisely a squarefreeness test on E -- every surviving target has a
squarefree quartic E with constant leading coefficient, hence
n1 in {0, 2, 4} off the wall is a THEOREM (parity), not a sampling
observation.

Wall (C = 0) fibers: F3 = x*gamma, so C = 0 splits exactly into the
branches x = 0 and (gamma = 0, x != 0); n1_wall counts each branch over
QQ (lex Groebner in shape-lemma form, every branch verified by exact
substitution into F modulo the eliminant) and returns the exact total.

CORRECTION (adversarial review, 2026-08-12): phase 0's odd n1 values
1, 3 were initially misdiagnosed as "eliminant artifacts". They are
GENUINE wall fibers -- every odd phase-0 count occurred at a C = 0
target, where the parity theorem does not apply, and n1_wall confirms
fibers of size 1 and 3 exist there (e.g. (-3, 2/3, 0) has true fiber 3
for both members). The C != 0 pipeline had been *discarding* the wall
(n1_exact returns None), not correcting an artifact; phase 0's eliminant
was right at those points. Wall counts are real data for the separation
hunt and are now measured, not thrown away.

Findings (2026-08-12, corrected): certified n1 value sets off the wall
are {0, 2, 4} for BOTH members (N = 400 exact); attained wall values are
{1, 3}, identical for both members at every audited wall target.
Through n1 the multiplicity invariant does not separate the same-degree
pair -- the completeness question is live. Next: n2 (see phase 2), then
the extreme n2 strata / wall-gluing data.
"""
import argparse
import random
import sys
import time

import sympy as sp
from sympy import Rational as Q

x, y, z, w = sp.symbols('x y z w')


def build_member(roots):
    """Gallagher weighted-lift member from a valid root set (0 first)."""
    roots = [Q(r) for r in roots]
    if not (roots[0] == 0 and Q(1) not in roots
            and len(set(roots)) == len(roots)):
        raise ValueError("need distinct roots, 0 first, 1 not a root")
    G = sp.prod([(w - r) for r in roots])
    Gp = sp.diff(G, w)
    if sp.expand(G.subs(w, 1) - Gp.subs(w, 0)) != 0:
        raise ValueError("endpoint identity fails for %s" % (roots,))
    lam = Gp.subs(w, 0) - Gp.subs(w, 1)
    if lam == 0:
        raise ValueError("lambda = 0")
    H = sp.expand(G/lam)
    Hp = sp.diff(H, w)
    p = sp.expand(Hp - Hp.subs(w, 0))
    q = sp.expand(w*Hp - H)
    kappa = sp.diff(Hp, w).subs(w, 1)
    if kappa == -2:
        raise ValueError("kappa = -2")
    a = -(1 + kappa)/(2 + kappa)
    ok = (p.subs(w, 0) == 0 and p.subs(w, 1) == -1
          and sp.integrate(p, (w, 0, 1)) == 0
          and q.subs(w, 0) == 0 and sp.diff(q, w).subs(w, 0) == 0)
    if not ok:
        raise ValueError("weighted-lift hypotheses fail")
    u = 1 + x*y
    gam = 1 + a*x*y + x**2*z
    W = sp.expand(u*gam)
    F1 = sp.cancel(sp.expand(u*gam**2 + q.subs(w, W))/(x**2*gam**2))
    F2 = sp.cancel(sp.expand(gam + p.subs(w, W))/(x*gam))
    F3 = sp.expand(x*gam)
    for i, Fi in enumerate((F1, F2, F3), 1):
        den = sp.fraction(sp.together(Fi))[1]
        if den.free_symbols:
            raise ValueError("F%d is not polynomial" % i)
    F = tuple(sp.expand(Fi) for Fi in (F1, F2, F3))
    J = sp.Matrix([[sp.diff(f, v) for v in (x, y, z)] for f in F])
    det = sp.expand(J.det())
    if det != 1:
        raise ValueError("det J = %s != 1" % det)
    return dict(roots=roots, a=a, H=H, F=F)


def member_kit(roots):
    """build_member + inverse-equation data, with the two identities verified."""
    M = build_member(roots)
    H, a = M['H'], M['a']
    Hp0 = sp.diff(H, w).subs(w, 0)
    p = sp.expand(sp.diff(H, w) - Hp0)
    F1, F2, F3 = M['F']
    u = 1 + x*y
    gam = 1 + a*x*y + x**2*z
    W = sp.expand(u*gam)
    inv_id = sp.expand(-H.subs(w, W) + W*(Hp0 + F2*F3) - F1*F3**2)
    chart_id = sp.expand(x*(F2*F3 - p.subs(w, W)) - F3)
    if inv_id != 0 or chart_id != 0:
        raise ValueError("fiber-determination identities failed")
    # guard == E' (so the gcd(E, guard) check in n1_exact is exactly a
    # squarefreeness test on E, and n1 in {0, 2, 4} off the wall is a
    # parity theorem): dE/dw = -H' + H'(0) + B*C = B*C - p.
    TA, TB, TC = sp.symbols('_TA _TB _TC')
    Et = -H + w*(Hp0 + TB*TC) - TA*TC**2
    if sp.expand(sp.diff(Et, w) - (TB*TC - p)) != 0:
        raise ValueError("guard != E' -- squarefreeness guard broken")
    return dict(M, Hp0=Hp0, p=p)


def _real_sols_shape(eqs, v1, v2):
    """Distinct real solutions of a zero-dimensional bivariate system,
    exact over QQ via a lex Groebner basis in shape-lemma form: a
    univariate eliminant g(v2) and v1 linear over it.  Returns
    (count, (g_squarefree, v1_expr)) or (0, None) for the empty system.
    Raises on any shape the certification cannot handle (failure-loud)."""
    G = sp.groebner(eqs, v1, v2, order='lex', domain='QQ')
    exprs = list(G.exprs)
    if exprs == [sp.Integer(1)]:
        return 0, None
    uni = [e for e in exprs if e.free_symbols <= {v2}]
    if not uni:
        raise ValueError("no univariate eliminant: %s" % exprs)
    g = sp.Poly(uni[-1], v2)
    if g.degree() < 1:
        raise ValueError("degenerate eliminant: %s" % g)
    gsf = sp.Poly(sp.prod([b for b, _ in sp.factor_list(g.as_expr())[1]]), v2)
    for e in exprs:
        if v1 in e.free_symbols and sp.degree(e, v1) == 1:
            c = sp.Poly(e, v1)
            if (c.nth(1).free_symbols <= {v2}
                    and c.nth(0).free_symbols <= {v2}
                    and sp.gcd(sp.Poly(c.nth(1), v2), gsf).total_degree() == 0):
                return gsf.count_roots(), (gsf, sp.cancel(-c.nth(0)/c.nth(1)))
    raise ValueError("system is not in shape-lemma form: %s" % exprs)


def _verify_branch(M, tgt, subs_map, gsf, var):
    """Exact substitution check: every branch solution really maps to tgt
    (all three components, modulo the squarefree eliminant)."""
    for Fi, ti in zip(M['F'], tgt):
        num, den = sp.fraction(sp.cancel(
            Fi.subs(subs_map, simultaneous=True) - ti))
        if sp.rem(sp.expand(num), gsf.as_expr(), var) != 0:
            raise ValueError("branch verification failed (numerator)")
        if sp.gcd(sp.Poly(den, var), gsf).total_degree() > 0:
            raise ValueError("branch verification failed (denominator)")


def n1_wall(M, target):
    """EXACT real fiber count at a wall target (C = 0), by branch
    decomposition of F3 = x*gamma = 0.  The branches are disjoint
    (x = 0 forces gamma = 1).  No chart, no E; every count is verified
    by exact substitution into F."""
    Av, Bv, Cv = target
    if Cv != 0:
        raise ValueError("n1_wall is for C = 0 targets")
    F1, F2, F3 = M['F']
    a = M['a']
    # branch x = 0
    e1 = sp.expand(F1.subs(x, 0) - Av)
    e2 = sp.expand(F2.subs(x, 0) - Bv)
    n_x0, data = _real_sols_shape([e1, e2], z, y)
    if n_x0:
        gsf, zlin = data
        _verify_branch(M, target, {x: 0, z: zlin}, gsf, y)
    # branch gamma = 0, x != 0:  z = -(1 + a*x*y)/x^2
    zg = -(1 + a*x*y)/x**2
    eqs = []
    for Fi, ti in ((F1, Av), (F2, Bv)):
        num, den = sp.fraction(sp.cancel(Fi.subs(z, zg) - ti))
        if any(b != x for b, _ in sp.factor_list(den)[1]):
            raise ValueError("unexpected denominator on gamma-branch: %s" % den)
        eqs.append(sp.expand(num))
    n_g0 = 0
    G = sp.groebner(eqs, y, x, order='lex', domain='QQ')
    exprs = list(G.exprs)
    if exprs != [sp.Integer(1)]:
        uni = [e for e in exprs if e.free_symbols <= {x}]
        if not uni:
            raise ValueError("no univariate eliminant on gamma-branch")
        # drop the x = 0 factor: it belongs to (and is counted by) the
        # other branch, and this branch requires x != 0
        keep = [b for b, _ in sp.factor_list(uni[-1])[1] if b != x]
        if keep:
            gsf = sp.Poly(sp.prod(keep), x)
            ylin = None
            for e in exprs:
                if y in e.free_symbols and sp.degree(e, y) == 1:
                    c = sp.Poly(e, y)
                    if (c.nth(1).free_symbols <= {x}
                            and c.nth(0).free_symbols <= {x}
                            and sp.gcd(sp.Poly(c.nth(1), x),
                                       gsf).total_degree() == 0):
                        ylin = sp.cancel(-c.nth(0)/c.nth(1))
                        break
            if ylin is None:
                raise ValueError("gamma-branch not in shape-lemma form")
            _verify_branch(M, target,
                           {y: ylin, z: sp.cancel(zg.subs(y, ylin))}, gsf, x)
            n_g0 = gsf.count_roots()
    return n_x0 + n_g0


# Wall regression targets: true exact fiber counts established by the
# 2026-08-12 adversarial review (branch decomposition, substitution
# verified) -- the values phase 0 reported and phase 1 wrongly dismissed.
WALL_REGRESSION = [((Q(-3), Q(2, 3), Q(0)), 3), ((Q(4), Q(1, 5), Q(0)), 1)]


def n1_exact(M, target):
    """CERTIFIED n1 for rational target with C != 0 (None on guarded strata)."""
    Av, Bv, Cv = target
    if Cv == 0:
        return None
    E = sp.Poly(-M['H'] + w*(M['Hp0'] + Bv*Cv) - Av*Cv**2, w)
    guard = sp.Poly(Bv*Cv - M['p'], w)
    if sp.gcd(E, guard).total_degree() > 0:
        return None
    return sp.count_roots(E)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--samples', type=int, default=80)
    ap.add_argument('--seed', type=int, default=7)
    args = ap.parse_args()
    ok = True

    A = member_kit([0, -1, 3, 4])
    B = member_kit([0, -1, -2, Q(3, 2)])
    print("A (atlas n=4) and B (alternative n=4) built; det J == 1 and both")
    print("fiber-determination identities verified symbolically: True")
    distinct = not all(sp.expand(fa - fb) == 0 for fa, fb in zip(A['F'], B['F']))
    ok &= distinct
    print("A and B are distinct polynomial maps:", distinct)

    for name, M in (('A', A), ('B', B)):
        tgt = (Q(0), -M['Hp0'], Q(1))
        c = n1_exact(M, tgt)
        ok &= (c == 4)
        print("member %s attains the full fiber count 4 at its target: %s"
              % (name, c == 4))

    for tgt, want in WALL_REGRESSION:
        got = tuple(n1_wall(M, tgt) for M in (A, B))
        ok &= (got == (want, want))
        print("wall regression %s: true fiber (A, B) = %s, expected %d: %s"
              % (tgt, got, want, got == (want, want)))

    random.seed(args.seed)
    hist = {'A': {}, 'B': {}}
    wall_hist = {'A': {}, 'B': {}}
    wall_agree = True
    t0 = time.time()
    for i in range(args.samples):
        scale = random.choice([1, 1, 2, 5, 10])
        pt = tuple(Q(random.randint(-6*scale, 6*scale), random.randint(1, 8))
                   for _ in range(3))
        counts = {}
        for name, M in (('A', A), ('B', B)):
            if pt[2] == 0:
                c = n1_wall(M, pt)
                wall_hist[name][c] = wall_hist[name].get(c, 0) + 1
                counts[name] = c
            else:
                c = n1_exact(M, pt)
                if c is not None:
                    hist[name][c] = hist[name].get(c, 0) + 1
        if len(counts) == 2 and counts['A'] != counts['B']:
            wall_agree = False
            print("  WALL SEPARATION CANDIDATE at %s: A=%d B=%d"
                  % (pt, counts['A'], counts['B']))
    print("certified n1 histograms, off-wall (C != 0) [%ds]:"
          % (time.time() - t0))
    print("  A:", dict(sorted(hist['A'].items())))
    print("  B:", dict(sorted(hist['B'].items())))
    print("attained sets off-wall: A = %s, B = %s"
          % (sorted(hist['A']), sorted(hist['B'])))
    print("exact wall (C = 0) histograms:")
    print("  A:", dict(sorted(wall_hist['A'].items())))
    print("  B:", dict(sorted(wall_hist['B'].items())))
    print("members agree at every sampled wall target:", wall_agree)
    odd = [v for v in list(hist['A']) + list(hist['B']) if v % 2]
    ok &= not odd
    print("no odd values off-wall (theorem: guard = E', E squarefree):",
          not odd)

    print("\nPHASE 0 %s" % ("COMPLETE" if ok else "FAILED"))
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
