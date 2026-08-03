import sympy as sp
import numpy as np

x1, x2, x3, y1, y2, y3 = sp.symbols('x1 x2 x3 y1 y2 y3')
F1 = (1 + x1*x2)**3*x3 + x2**2*(1 + x1*x2)*(4 + 3*x1*x2)
F2 = x2 + 3*x1*(1 + x1*x2)**2*x3 + 3*x1*x2**2*(4 + 3*x1*x2)
F3 = 2*x1 - 3*x1**2*x2 - x1**3*x3
fF = sp.lambdify((x1, x2, x3), sp.Matrix([F1, F2, F3]), 'numpy')
def Fn(v): return np.asarray(fF(*v), dtype=complex).ravel()

x3sol = (2*x1 - 3*x1**2*x2 - y3)/x1**3
S1 = sp.expand(sp.numer(sp.together((F1.subs(x3, x3sol) - y1)*x1**3)))
S2 = sp.expand(sp.numer(sp.together((F2.subs(x3, x3sol) - y2)*x1**3)))

def real_fiber_count(yv):
    sub = {y1: sp.nsimplify(yv[0], rational=True),
           y2: sp.nsimplify(yv[1], rational=True),
           y3: sp.nsimplify(yv[2], rational=True)}
    R = sp.Poly(sp.expand(sp.resultant(sp.Poly(S1.subs(sub), x2),
                                       sp.Poly(S2.subs(sub), x2), x2)), x1)
    yn = np.array(yv, dtype=complex)
    sols = []
    for r in np.roots([complex(c) for c in R.all_coeffs()]):
        if abs(r) < 1e-9:
            continue
        p1c = sp.Poly(S1.subs(sub).subs(x1, sp.Float(r.real, 15)+sp.I*sp.Float(r.imag, 15)), x2)
        for r2 in np.roots([complex(c) for c in p1c.all_coeffs()]):
            v3 = (2*r - 3*r**2*r2 - yn[2])/r**3
            v = np.array([r, r2, v3], dtype=complex)
            if np.max(np.abs(Fn(v)-yn)) < 1e-6 and \
               not any(np.max(np.abs(v-s)) < 1e-6 for s in sols):
                sols.append(v)
    # x1 = 0 sheet exists iff y3 = 0 (measure zero); random samples never hit it
    return sum(1 for s in sols if np.max(np.abs(s.imag)) < 1e-7)

rng = np.random.default_rng(3)
samples = [rng.uniform(-2, 2, 3) for _ in range(20)]
samples += [np.array([-0.25, 0, 0]) + rng.normal(scale=0.08, size=3) for _ in range(8)]
counts = {}
for yv in samples:
    n = real_fiber_count(list(yv))
    counts[n] = counts.get(n, 0) + 1
print("real fiber-count histogram over 28 sample points:", dict(sorted(counts.items())))
print("=> essential range of n(y) contains", sorted(k for k in counts if counts[k] > 1))

# ---- finite-time escape along the P'_1 vector field (row 1 of A) ----
q1, q2, q3 = sp.symbols('q1 q2 q3')
Fq = sp.Matrix([(1+q1*q2)**3*q3 + q2**2*(1+q1*q2)*(4+3*q1*q2),
                q2 + 3*q1*(1+q1*q2)**2*q3 + 3*q1*q2**2*(4+3*q1*q2),
                2*q1 - 3*q1**2*q2 - q1**3*q3])
A = -(Fq.jacobian([q1, q2, q3]).adjugate().T)/2
row1 = sp.lambdify((q1, q2, q3), sp.Matrix(A[0, :]).T, 'numpy')
def X(v): return np.asarray(row1(*v), dtype=float).ravel()

def rk4_escape(v0, h0=1e-4, tmax=50.0, cap=1e8):
    v, t, h = np.array(v0, float), 0.0, h0
    while t < tmax:
        nv = np.linalg.norm(v)
        if nv > cap:
            return t, nv
        h = min(h0, 0.1/max(1.0, np.linalg.norm(X(v))))  # adaptive
        k1 = X(v); k2 = X(v+h/2*k1); k3 = X(v+h/2*k2); k4 = X(v+h*k3)
        v = v + h/6*(k1+2*k2+2*k3+k4)
        t += h
    return None, np.linalg.norm(v)

for v0 in ([0.7, 0.3, 0.5], [1.0, -0.8, 0.4], [-0.5, 0.9, -1.1]):
    t_esc, nv = rk4_escape(v0)
    tag = f"|x| passed 1e8 at t ~ {t_esc:.4f}" if t_esc else f"no escape by t=50 (|x|={nv:.2e})"
    print(f"flow of P'_1 field from {v0}: {tag}")
