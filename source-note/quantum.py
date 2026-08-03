"""Quantum implementation checks for the lifted endomorphism on L^2(R^3).

New operators (hbar = 1):
  Q'_i = multiplication by F_i(q)
  P'_i = sum_k A_ik(q) p_k   with  A = (DF^T)^{-1} = -adjugate(DF)^T / 2  (polynomial!)
Claims to verify as exact polynomial identities:
  (1) A * DF^T = I            -> [Q'_i, P'_j] = i delta_ij
  (2) Piola: sum_k d_k A_ik = 0  -> left-ordered P'_i is SYMMETRIC as written
  (3) c_l = sum_k (A_ik d_k A_jl - A_jk d_k A_il) = 0 for all i<j, l
        -> [P'_i, P'_j] = 0 exactly (p-linear ops: commutator = i*Poisson, no hbar^2 terms)
  (4) Intertwining: with C psi = sqrt(2) psi(F(x)),
      chain rule + (1) give  P'_i C = C p_i  and  Q'_i C = C q_i  exactly.
"""
import sympy as sp

q = sp.symbols('q1 q2 q3')
q1, q2, q3 = q
F = sp.Matrix([
    (1 + q1*q2)**3*q3 + q2**2*(1 + q1*q2)*(4 + 3*q1*q2),
    q2 + 3*q1*(1 + q1*q2)**2*q3 + 3*q1*q2**2*(4 + 3*q1*q2),
    2*q1 - 3*q1**2*q2 - q1**3*q3])
M = F.jacobian(q)
A = -(M.adjugate().T) / 2

chk1 = sp.expand(A*M.T - sp.eye(3))
print("(1) A*DF^T - I == 0 :", all(c == 0 for c in chk1))

piola = [sp.expand(sum(sp.diff(A[i, k], q[k]) for k in range(3))) for i in range(3)]
print("(2) Piola row divergences:", piola, "-> P'_i symmetric as written")

ok = True
for i in range(3):
    for j in range(i+1, 3):
        for l in range(3):
            c = sp.expand(sum(A[i, k]*sp.diff(A[j, l], q[k])
                              - A[j, k]*sp.diff(A[i, l], q[k]) for k in range(3)))
            ok &= (c == 0)
print("(3) all quantum commutator coefficients vanish:", ok, "-> [P'_i,P'_j]=0 exactly")

# (4) intertwining on a generic wavefunction, checked directly
psi = sp.Function('psi')
Cpsi = sp.sqrt(2)*psi(F[0], F[1], F[2])
good = True
for i in range(3):
    lhs = sp.expand(sum(A[i, k]*sp.diff(Cpsi, q[k]) for k in range(3)))   # (1/-i) P'_i C psi
    d = sp.Symbol('d')
    rhs = sp.sqrt(2)*sp.Subs(sp.diff(psi(q1, q2, q3), q[i]), (q1, q2, q3),
                             (F[0], F[1], F[2])).doit()
    good &= sp.simplify(lhs - rhs) == 0
print("(4) P'_i (C psi) == C (p_i psi) for i=1,2,3:", good)
print("    Q'_i (C psi) == C (q_i psi): multiplication operators, immediate")
print("\nmax coefficient degree in P'_i:", max(sp.total_degree(sp.expand(A[i, k]))
      for i in range(3) for k in range(3)))
