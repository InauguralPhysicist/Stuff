"""Exact fiber count and escape times for the Alpoge Keller map F: R^3 -> R^3.

Replaces the resultant-based sampler, which loses roots to float conditioning
and discards the x1 = 0 sheet.

Lex Groebner elimination (x3 > x2 > x1) has shape-lemma form: x2 and x3 are each
degree 1 over x1, so real x1 roots <-> real preimages, bijectively.  The
univariate factor is the depressed cubic

    L(y) x1^3 + (4 - 3 y2 y3) x1 - 2 y3 = 0,
    L(y) = 27 y1^2 y3^2 - 18 y1 y2 y3 + 16 y1 + y2^3 y3 - y2^2.

Its discriminant factors as

    Delta(y) = -4 (27 y1 y3^2 - 9 y2 y3 + 8)^2 * L(y),

so sign(Delta) = -sign(L) and the real fiber count is decided by ONE polynomial:

    L(y) < 0  ->  n(y) = 3        L(y) > 0  ->  n(y) = 1
    L(y) = 0  ->  non-properness hypersurface; a branch is at infinity.

Consequences: n(y) is never 0 or 2, so C psi = sqrt(2) psi(F(x)) satisfies
1 <= C*C <= 3 with spec(C*C) = {1, 3} exactly -- a theorem, not a sample.

Along the P'_i flow, F(x(t)) = F(x0) + t e_i, so L restricted to the ray is a
quadratic in t.  If L(y0) < 0 (the n = 3 side) and y3 != 0, the roots have
negative product: one positive and one negative real root.  The flow therefore
escapes to infinity in FINITE time in both time directions, at rate
|x1| ~ |t - t*|^(-1/2).  Completeness fails, and it must: commuting complete
fields would force n(y) constant, hence n == 1, hence F injective.
"""
import numpy as np


def L(y):
    y1, y2, y3 = y
    return 27*y1**2*y3**2 - 18*y1*y2*y3 + 16*y1 + y2**3*y3 - y2**2


def fiber_count(y, tol=1e-13):
    """Real fiber count: 3 if L < 0, 1 if L > 0, None on the escape locus."""
    a = L(y)
    if abs(a) < tol:
        return None
    return 3 if a < 0 else 1


def fiber_roots(y):
    """The x1-coordinates of the real preimages."""
    a, b, c = L(y), 4 - 3*y[1]*y[2], -2*y[2]
    r = np.roots([a, 0.0, b, c])
    return sorted(z.real for z in r if abs(z.imag) < 1e-9*max(1.0, abs(z)))


def escape_times(y0, axis=0):
    """Finite times at which the P'_axis flow through F^-1(y0) blows up."""
    e = np.zeros(3); e[axis] = 1.0
    # L restricted to the ray is exactly quadratic in t; recover it from 3 points
    v0, v1, v2 = (L(y0 + k*e) for k in (0, 1, 2))
    a = (v2 - 2*v1 + v0)/2.0
    b = v1 - v0 - a
    coeffs = [a, b, v0] if abs(a) > 1e-14 else [b, v0]
    if all(abs(c) < 1e-14 for c in coeffs):
        return []
    return sorted(t.real for t in np.roots(coeffs) if abs(t.imag) < 1e-9)


if __name__ == "__main__":
    rng = np.random.default_rng(3)
    samples = [rng.uniform(-2, 2, 3) for _ in range(20)]
    samples += [np.array([-0.25, 0, 0]) + rng.normal(scale=0.08, size=3)
                for _ in range(8)]
    hist = {}
    for y in samples:
        n = fiber_count(y)
        hist[n] = hist.get(n, 0) + 1
    print("real fiber-count histogram (28 samples):", dict(sorted(hist.items())))
    print("  -> no 2 appears, and none can: the complex fiber has 3 simple")
    print("     points off {L=0}, conjugation-invariant, so n is odd.")

    print("\nfiber over (-1/4, 0, 0):", fiber_roots(np.array([-0.25, 0.0, 0.0])))
    print("  x1 in {-1, 0, 1}; full points (-1, 3/2, 13/2), (0, 0, -1/4), (1, -3/2, 13/2)")

    print("\nescape times along the P'_1 flow:")
    for y in samples[:6]:
        n = fiber_count(y)
        ts = [t for t in escape_times(y)]
        print(f"  y={np.round(y,3)} n={n}  t* = {[round(t,5) for t in ts] or 'none'}")
