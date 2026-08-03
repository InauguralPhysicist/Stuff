"""Verify the keystone claims of keller-map-operators.md and diagnose my errors."""
import sympy as sp
import random

x1, x2, x3, y1, y2, y3 = sp.symbols('x1 x2 x3 y1 y2 y3')
F1 = (1 + x1*x2)**3*x3 + x2**2*(1 + x1*x2)*(4 + 3*x1*x2)
F2 = x2 + 3*x1*(1 + x1*x2)**2*x3 + 3*x1*x2**2*(4 + 3*x1*x2)
F3 = 2*x1 - 3*x1**2*x2 - x1**3*x3

Lpoly = 27*y1**2*y3**2 - 18*y1*y2*y3 + 16*y1 + y2**3*y3 - y2**2
cubic = lambda a, b, c: sp.Poly(
    Lpoly.subs({y1: a, y2: b, y3: c})*x1**3
    + (4 - 3*b*c)*x1 - 2*c, x1)

# --- 1. discriminant factorization, symbolically over QQ ---
idy = sp.expand((4 - 3*y2*y3)**3 + 27*y3**2*Lpoly
                - (27*y1*y3**2 - 9*y2*y3 + 8)**2)
print("discriminant identity (4-3y2y3)^3 + 27y3^2 L = (27y1y3^2-9y2y3+8)^2 :",
      idy == 0)

# --- 2. Groebner shape + eliminant at the collision point and 5 random points ---
def gb_check(a, b, c):
    G = sp.groebner([F1 - a, F2 - b, F3 - c], x3, x2, x1, order='lex')
    uni = [g for g in G.exprs if g.free_symbols <= {x1}]
    ok_shape = all(max(sp.degree(g, x2), sp.degree(g, x3)) <= 1
                   for g in G.exprs if g not in uni)
    if len(uni) != 1:
        return False, ok_shape
    p = sp.Poly(uni[0], x1)
    q = cubic(a, b, c)
    ratio_ok = sp.simplify(p.as_expr()*q.LC() - q.as_expr()*p.LC()) == 0
    return ratio_ok, ok_shape

random.seed(2)
pts = [(sp.Rational(-1, 4), 0, 0)] + \
      [tuple(sp.Rational(random.randint(-9, 9), random.randint(1, 5))
             for _ in range(3)) for _ in range(5)]
res = [gb_check(*p) for p in pts]
print("eliminant matches L-cubic at collision + 5 random points:",
      all(r[0] for r in res), "| shape-lemma form:", all(r[1] for r in res))

# --- 3. my four old flow initial conditions: where did they live? ---
Fv = sp.lambdify((x1, x2, x3), sp.Matrix([F1, F2, F3]), 'sympy')
Lf = sp.lambdify((y1, y2, y3), Lpoly, 'sympy')
print("\nold initial conditions for the P'_1 flow test:")
for x0 in ([sp.Rational(7,10), sp.Rational(3,10), sp.Rational(1,2)],
           [1, sp.Rational(-4,5), sp.Rational(2,5)],
           [sp.Rational(-1,2), sp.Rational(9,10), sp.Rational(-11,10)],
           [sp.Rational(1,5), sp.Rational(1,10), sp.Rational(-3,10)]):
    y0 = [sp.nsimplify(v) for v in Fv(*x0)]
    Lv = sp.nsimplify(Lf(*y0))
    # L along the e1-ray is quadratic in t: a t^2 + b t + c
    aq = 27*y0[2]**2
    bq = 2*27*y0[2]**2*y0[0] + 16 - 18*y0[1]*y0[2]
    disc = sp.nsimplify(bq**2 - 4*aq*Lv)
    hits = "ray crosses {L=0}" if disc >= 0 else "ray NEVER crosses {L=0}"
    print(f"  L(F(x0)) = {sp.nsimplify(Lv)} = {float(Lv):+.4f}  ({hits})")

# --- 4. my n=2 sample: reproduce the seed-11 run, recount exactly ---
random.seed(11)
sample = [tuple(sp.Rational(random.randint(-16, 16), 8) for _ in range(3))
          for _ in range(12)]
sample += [(sp.Rational(-1, 4) + sp.Rational(random.randint(-2, 2), 16),
            sp.Rational(random.randint(-2, 2), 16),
            sp.Rational(random.randint(-2, 2), 16)) for _ in range(6)]
hist = {}
culprits = []
for p in sample:
    Lv = Lpoly.subs({y1: p[0], y2: p[1], y3: p[2]})
    if Lv == 0:
        n = 'on {L=0}'
    else:
        n = len(sp.real_roots(cubic(*p)))
    hist[n] = hist.get(n, 0) + 1
    if p[2] == 0:
        culprits.append((p, n))
print("\nexact recount of my 18 seed-11 samples:", dict(sorted(
    hist.items(), key=str)))
print("points with y3 = 0 (the sheet my resultant code discarded):")
for p, n in culprits:
    print("  y =", p, " true n =", n)

# --- 5. the empty fiber: y = (4/27, 4/3, 1) should not be in the image ---
G = sp.groebner([F1 - sp.Rational(4, 27), F2 - sp.Rational(4, 3), F3 - 1],
                x1, x2, x3, order='grevlex')
print("\nGroebner basis of <F - (4/27, 4/3, 1)> :", list(G.exprs),
      " -> fiber is EMPTY" if list(G.exprs) == [1] else "")
