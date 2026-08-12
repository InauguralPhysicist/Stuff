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

Phase 1 (fiber determination, DONE): for any target (A,B,C) with C != 0,
the w = u*gamma values of the preimages are exactly the real roots of

    E(w) = -H(w) + w*(H'(0) + B*C) - A*C^2        (constant leading coeff!)

with the chart x = C/(B*C - p(w)), u = w*x/C, y = (u-1)/x,
z = (gamma-1-a*(u-1))/x^2 lifting each root off the escape locus
{B*C = p(w)}. Both the inverse identity E(u*gamma) == 0 and the chart
identity x*(B*C - p(w)) == C are verified symbolically at import (the
analogs of F's cubic_identity/shape identities). Since C != 0 forces
x != 0 at every preimage, n1 = count_roots(E) EXACTLY off the guarded
(measure-zero) strata. No Groebner per point, no chart artifacts.

Phase 0/1 findings (2026-08-12): phase 0's odd n1 values 1, 3 were
eliminant artifacts -- certified n1 value sets are {0, 2, 4} for BOTH
members (N = 400 exact). Phase 2 (numeric n2, 60-digit relative-threshold
discipline): both members attain n2 in {0, 2, 4, 6, 8, 10, 12} (wide
log-scaled search, 486 targets total); neither has reached 14 or 16.
Through n2, the multiplicity invariant does NOT separate the same-degree
pair -- the completeness question is live. Next: hunt the extreme n2
strata to certify max ess-range(n2) per member, then n3 or the
wall-gluing data directly.
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
    return dict(M, Hp0=Hp0, p=p)


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

    random.seed(args.seed)
    hist = {'A': {}, 'B': {}}
    t0 = time.time()
    for i in range(args.samples):
        scale = random.choice([1, 1, 2, 5, 10])
        pt = tuple(Q(random.randint(-6*scale, 6*scale), random.randint(1, 8))
                   for _ in range(3))
        for name, M in (('A', A), ('B', B)):
            c = n1_exact(M, pt)
            if c is not None:
                hist[name][c] = hist[name].get(c, 0) + 1
    print("certified n1 histograms [%ds]:" % (time.time() - t0))
    print("  A:", dict(sorted(hist['A'].items())))
    print("  B:", dict(sorted(hist['B'].items())))
    print("attained sets: A = %s, B = %s"
          % (sorted(hist['A']), sorted(hist['B'])))
    odd = [v for v in list(hist['A']) + list(hist['B']) if v % 2]
    ok &= not odd
    print("no odd (chart-artifact) values in certified counts:", not odd)

    print("\nPHASE 0 %s" % ("COMPLETE" if ok else "FAILED"))
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
