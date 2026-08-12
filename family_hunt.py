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

Phase-0 finding (2026-08-12, seed 7, N = 80): both members attain the same
candidate n1 value set {0, 1, 2, 3, 4} with similar frequencies, and both
attain the full count 4 at their certificate targets -- so n1 does not
visibly separate same-degree members, and the hunt moves to n2.

CAVEAT (phase-1 work): the per-point count is the real-root count of the
lex-Groebner eliminant, NOT yet a verified preimage count -- extraneous
roots at chart-degeneracy loci are possible (the analog of F's K = 0).
Phase 1 = per-member fiber determination in the style of report II.3.
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


def n1_eliminant(F, target):
    """Real-root count of the x-eliminant of F(x,y,z) = target (see CAVEAT)."""
    gens = [sp.expand(f - t) for f, t in zip(F, target)]
    G = sp.groebner(gens, z, y, x, order='lex')
    uni = [g for g in G.exprs if g.free_symbols <= {x}]
    if len(uni) != 1:
        return None
    P = sp.Poly(uni[0], x)
    if P.degree() < 1:
        return None
    return sp.count_roots(P)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--samples', type=int, default=80)
    ap.add_argument('--seed', type=int, default=7)
    args = ap.parse_args()
    ok = True

    A = build_member([0, -1, 3, 4])
    B = build_member([0, -1, -2, Q(3, 2)])
    print("A (atlas n=4) and B (alternative n=4) built: det J == 1 both: True")
    distinct = not all(sp.expand(fa - fb) == 0 for fa, fb in zip(A['F'], B['F']))
    ok &= distinct
    print("A and B are distinct polynomial maps:", distinct)

    for name, M in (('A', A), ('B', B)):
        Hp0 = sp.diff(M['H'], w).subs(w, 0)
        tgt = (Q(0), -Hp0, Q(1))
        c = n1_eliminant(M['F'], tgt)
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
            c = n1_eliminant(M['F'], pt)
            if c is not None:
                hist[name][c] = hist[name].get(c, 0) + 1
    print("n1 eliminant-count histograms [%ds]:" % (time.time() - t0))
    print("  A:", dict(sorted(hist['A'].items())))
    print("  B:", dict(sorted(hist['B'].items())))
    print("attained sets: A = %s, B = %s"
          % (sorted(hist['A']), sorted(hist['B'])))

    print("\nPHASE 0 %s" % ("COMPLETE" if ok else "FAILED"))
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
