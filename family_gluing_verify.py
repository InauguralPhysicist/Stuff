#!/usr/bin/env python3
"""Independent confirmation of the G2 separation (anomaly protocol).

The census pipeline (family_gluing_census.py) reported, with all gates
green: G0 and G1 tie, but the labeled incidence graphs (G2) differ --
the load-bearing fact being WHICH singular strata bound the origin
branch of the discriminant curve (the Sigma-component whose closure
meets the wall, intrinsically marked by its incidence with the wall
strata):

    member A: origin branch ends at {node, cusp}
    member B: origin branch ends at {cusp, cusp}
              (it crosses the node's critical line at a regular point)

This script re-establishes that fact by a method independent of the
engine's strip/matching code: fixed-step rational continuation from the
origin anchor with exact root isolation at every step, stopping at a
fixed standoff h from each critical line, where branch clusters have
radius O(h^(1/2)) ~ 0.05 against O(1) line-root gaps. Node vs cusp
identity of the singular points is not re-derived here: the L6 harness
(family_gluing_structure.py) already pins exactly one perfect-square
(node) point per member -- rational, listed below -- so the algebraic
singular points are the cusps. Failure-loud; CI-run."""
import sys

import sympy as sp
from sympy import Rational as Q

from family_hunt import member_kit
from family_gluing_census import (plane_data, real_roots_exact, Ps, Rs)


def fail(msg):
    print("FAIL:", msg)
    sys.exit(1)


def continue_branch(D, p_start, r_start, p_target, standoff=Q(1, 512)):
    """Branch continuation with fixed rational steps and exact root
    isolation; returns the branch R-value at standoff from the target
    critical line."""
    direction = 1 if p_target.evalf(60) > sp.Float(p_start, 60) else -1
    tgt = Q(sp.Rational(sp.Float(p_target.evalf(60), 60))) - \
        direction*standoff
    p = Q(p_start)
    r_now = sp.Float(r_start, 60)
    step = Q(direction, 32)
    while (p < tgt) if direction > 0 else (p > tgt):
        p_next = p + step
        if (p_next > tgt) if direction > 0 else (p_next < tgt):
            p_next = tgt
        rr = real_roots_exact(D.subs(Ps, p_next), Rs)
        if not rr:
            fail("branch lost at P=%s" % p_next)
        vals = [r.evalf(60) for r in rr]
        d = [abs(v - r_now) for v in vals]
        j = min(range(len(vals)), key=lambda k: d[k])
        gaps = [abs(vals[i + 1] - vals[i]) for i in range(len(vals) - 1)]
        tube = (min(gaps)/2) if gaps else sp.Float(10)
        if d[j] > tube and abs(step) > Q(1, 2**20):
            step = step/2
            continue
        p, r_now = p_next, vals[j]
    return r_now


def line_roots(D, uc):
    if uc.is_rational:
        return real_roots_exact(D.subs(Ps, uc), Rs)
    mpu = sp.minimal_polynomial(uc, Ps)
    elim = sp.resultant(mpu, D, Ps)
    cand = real_roots_exact(elim, Rs)
    return [r for r in cand if sp.simplify(D.subs({Ps: uc, Rs: r})) == 0]


def nearest(rc, val):
    j = min(range(len(rc)), key=lambda k: abs(rc[k].evalf(60) - val))
    d = abs(rc[j].evalf(60) - val)
    others = [abs(rc[k].evalf(60) - val) for k in range(len(rc)) if k != j]
    if d > sp.Float('0.2') or (others and min(others) < 4*d):
        fail("line-root classification ambiguous (d=%s)" % d)
    return rc[j]


def check(name, roots, node_PR, expect):
    """expect: dict side -> ('node'|'cusp'|('regular_then', 'cusp'))"""
    M = member_kit(roots)
    EPR, D, _ = plane_data(M)
    DR = sp.diff(D, Rs)
    crit = sorted(set(sp.Poly(sp.expand(sp.resultant(D, DR, Rs)),
                              Ps).real_roots()),
                  key=lambda r: r.evalf(60))
    G = sp.groebner([D, sp.diff(D, Ps), DR], Ps, Rs, order='lex',
                    domain='QQ')
    sing = [(s[Ps], s[Rs]) for s in sp.solve(G.exprs, [Ps, Rs], dict=True)
            if s[Ps].is_real and s[Rs].is_real]
    if len(sing) != 3:
        fail("[%s] expected 3 real singular points" % name)

    def kind_of(uc, r):
        for u0, v0 in sing:
            if abs(uc.evalf(60) - u0.evalf(60)) < 1e-40 and \
                    abs(r.evalf(60) - v0.evalf(60)) < 1e-40:
                if u0.is_rational and v0.is_rational and \
                        (u0, v0) == node_PR:
                    return 'node'
                return 'cusp'
        return 'regular'

    left = max([c for c in crit if c.evalf(60) < 0],
               key=lambda c: c.evalf(60))
    right = min([c for c in crit if c.evalf(60) > 0],
                key=lambda c: c.evalf(60))
    for tgt, side in ((left, 'left'), (right, 'right')):
        rlim = continue_branch(D, Q(0), 0, tgt)
        hit = nearest(line_roots(D, tgt), rlim)
        kind = kind_of(tgt, hit)
        want = expect[side]
        if isinstance(want, tuple):
            # regular crossing, then continue to the NEXT critical line
            if kind != 'regular':
                fail("[%s] %s: expected regular crossing, got %s"
                     % (name, side, kind))
            direction = -1 if side == 'left' else 1
            nxt_candidates = [c for c in crit
                              if (c.evalf(60) < tgt.evalf(60)) ==
                              (direction < 0) and c != tgt]
            nxt = max(nxt_candidates, key=lambda c: c.evalf(60)) \
                if direction < 0 else \
                min(nxt_candidates, key=lambda c: c.evalf(60))
            # anchor just past the crossed line, on the same branch
            h = Q(1, 512)
            p1 = Q(sp.Rational(sp.Float(tgt.evalf(60), 60))) + direction*h
            rr = real_roots_exact(D.subs(Ps, p1), Rs)
            anchor = min(rr, key=lambda r: abs(r.evalf(60) - rlim))
            rlim2 = continue_branch(D, p1, anchor.evalf(60), nxt)
            hit2 = nearest(line_roots(D, nxt), rlim2)
            kind2 = kind_of(nxt, hit2)
            if kind2 != want[1]:
                fail("[%s] %s (second leg): expected %s, got %s"
                     % (name, side, want[1], kind2))
            print("[%s] origin branch %s: regular crossing at P=%s, "
                  "then %s at P=%s -- as measured"
                  % (name, side, tgt.evalf(8), kind2, nxt.evalf(8)))
        else:
            if kind != want:
                fail("[%s] %s: expected %s, got %s"
                     % (name, side, want, kind))
            print("[%s] origin branch %s: %s at P=%s -- as measured"
                  % (name, side, kind, tgt.evalf(8)))


def main():
    # node coordinates: the unique real perfect-square points (L6)
    check('A', [0, -1, 3, 4], (Q(-3), Q(1)),
          {'left': 'node', 'right': 'cusp'})
    check('B', [0, -1, -2, Q(3, 2)], (Q(-21, 32), Q(-343, 512)),
          {'left': ('regular_then', 'cusp'), 'right': 'cusp'})
    print("G2 SEPARATION FACT CONFIRMED INDEPENDENTLY:")
    print("  A: wall-attached Sigma-branch ends at {node, cusp}")
    print("  B: wall-attached Sigma-branch ends at {cusp, cusp}")
    return 0


if __name__ == '__main__':
    sys.exit(main())
