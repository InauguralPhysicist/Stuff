#!/usr/bin/env python3
"""Screen the degree-4 endpoint-identity moduli for G0-G2-tied pairs.

The completeness hunt (issue #14) needs a pair of members whose
multiplicity landscapes tie through G2 (the census pipeline separated
the original pair (A, B) at G2 -- PR #20). This script enumerates
small-height rational members and screens them pairwise with the same
validated instrument (family_gluing_census.py).

Moduli parametrization: roots {0, a, b, c} satisfy the endpoint
identity  prod(1 - r_i) = prod_{i>=2}(-r_i)  iff  e2 = e1 - 1, i.e.

    c = (1-a)(1-b) / [ (1-a)(1-b) - a*b ]        (rational in a, b).

Screening outputs are MEASUREMENTS with the CI-pinned instrument, not
banked adoptions: any tied pair found here still needs its own gate run
(V1 grid on the new members) and a non-triviality decision
(family_equiv.py-style, plus the tame caveat) before it becomes the
completeness test case. Members that violate an engine assumption
(phantom arcs, degenerate origin structure, ...) raise loudly and are
recorded as SKIPPED with the reason -- never silently dropped.
"""
import argparse
import sys
import time

import sympy as sp
from sympy import Rational as Q

from family_hunt import member_kit
from family_gluing_census import (CensusError, PlaneCensus, plane_data,
                                  point_oracle_factory, assemble_3d,
                                  Ps, Rs)


def enumerate_members(vals):
    """Distinct valid members {0, a, b, c} from a list of rational
    candidate values for (a, b)."""
    seen = {}
    order = []
    for a in vals:
        for b in vals:
            if a == b or 0 in (a, b) or 1 in (a, b):
                continue
            den = (1 - a)*(1 - b) - a*b
            if den == 0:
                continue
            c = (1 - a)*(1 - b)/den
            if c in (0, 1, a, b):
                continue
            key = tuple(sorted([a, b, Q(c)]))
            if key in seen:
                continue
            seen[key] = True
            order.append(key)
    return order


def screen_member(roots_key):
    """Build + census one member; returns dict or raises."""
    M = member_kit([0] + list(roots_key))
    EPR, D, label = plane_data(M)
    # allow_folds=True: a smooth vertical tangent in the (P,R) frame is
    # a presentation feature, not an intrinsic stratum; the engine
    # coarsens it away correctly (L5 made folds *absent* for A and B,
    # but absence is not required for correctness)
    pc = PlaneCensus(D, Ps, Rs, label, point_oracle_factory(4, True))
    cx = pc.result()
    g3d = assemble_3d(M, pc, cx)
    return dict(M=M, plane=cx, g3d=g3d,
                census=tuple(sorted(g3d.census().items())))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--halves', action='store_true',
                    help='include half-integer parameter values')
    ap.add_argument('--span', type=int, default=5,
                    help='integer parameter range [-span, span]')
    args = ap.parse_args()

    vals = [Q(k) for k in range(-args.span, args.span + 1)]
    if args.halves:
        vals += [Q(2*k + 1, 2) for k in range(-args.span, args.span)]
    members = enumerate_members(vals)
    print("moduli candidates (distinct root triples): %d" % len(members))

    results = {}
    skipped = []
    t00 = time.time()
    for i, key in enumerate(members):
        t0 = time.time()
        try:
            results[key] = screen_member(key)
            print("[%d/%d] %s: census %s [%ds]"
                  % (i + 1, len(members), key,
                     dict(results[key]['census']), time.time() - t0),
                  flush=True)
        except (CensusError, ValueError, AssertionError) as e:
            skipped.append((key, str(e)))
            print("[%d/%d] %s: SKIPPED (%s) [%ds]"
                  % (i + 1, len(members), key, e, time.time() - t0),
                  flush=True)
        sp.core.cache.clear_cache()
    print("censused %d members, skipped %d, total %dmin"
          % (len(results), len(skipped), (time.time() - t00)/60))

    # group by G1 census (G0 is contained in it)
    groups = {}
    for key, r in results.items():
        groups.setdefault(r['census'], []).append(key)
    print("\nG1 census groups:")
    tied_pairs = []
    for cen, keys in sorted(groups.items(), key=lambda kv: -len(kv[1])):
        print("  census %s: %d members" % (dict(cen), len(keys)))
        for k in keys:
            print("    %s" % (k,))
        # pairwise G2 within the group
        for i in range(len(keys)):
            for j in range(i + 1, len(keys)):
                a, b = keys[i], keys[j]
                if results[a]['g3d'].iso(results[b]['g3d']):
                    tied_pairs.append((a, b))
                    print("    G2 TIE: %s ~ %s" % (a, b))

    print("\n%d G0-G2-tied pair(s) found" % len(tied_pairs))
    for a, b in tied_pairs:
        print("  %s  ~  %s" % (a, b))
    if skipped:
        print("\nskipped members (engine assumption violated):")
        for k, e in skipped:
            print("  %s: %s" % (k, e))
    return 0


if __name__ == '__main__':
    sys.exit(main())
