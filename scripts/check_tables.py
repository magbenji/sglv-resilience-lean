#!/usr/bin/env python3
"""Numerical cross-check of Tables 1 and 2 of Phan, Ridenhour & Remien (2025).

Requires numpy and scipy. Run: python3 scripts/check_tables.py

What it checks (see "Numerical checks" in the README):
1. Table 1 is reproduced from the printed m1, m2 with the *correct* Jacobian of (3.1)
   (gamma11 = a1 - 2 b11 m1 + b12 m2, gamma22 = a2 + b21 m1 - 2 b22 m2), provided
   beta22 = 4/150 (~0.02667, printed as 0.027) and, in parameter set 4, beta12 = -0.015
   (the Figure 3 caption prints -0.03, but the text says set 4 halves beta12).
2. R_c = -alpha(S)/2 of Table 2 is reproduced from the Table 1 coefficients.
3. W(t) = E[Y^T Y], computed from (3.7)-(3.8), tends to a positive limit, so the average
   return rate R_ave(t) -> 0 like 1/t and R_inf = 0 (Lean: `rInf_eq_zero`). The printed
   R_inf values are values of R_ave at a finite time.
"""
import numpy as np
from scipy.integrate import solve_ivp

B22 = 4 / 150
# (alpha), (b11, b12, b21, b22), (t11, t12, t21, t22), Table 1 (m1, m2, Phi1, Phi2, g11, g12, g21, g22), Table 2 (Rc, Rinf)
SETS = {
    1: ((6, 4), (0.05, -0.03, -0.01, B22), (0.01, 0.015, 0.01, 0.02),
        (38.7470, 135.3518, 0.0813, 0.4263, -1.9353, -1.1624, -1.3535, -3.6062), (1.2635, 0.0047)),
    2: ((6, 4), (0.05, -0.03, -0.01, B22), (0.05, 0.075, 0.05, 0.1),
        (38.8413, 134.9853, 0.3254, 1.6171, -1.9337, -1.1652, -1.3499, -3.5876), (1.2539, 0.0031)),
    3: ((6, 4), (0.05, -0.015, -0.01, B22), (0.01, 0.015, 0.01, 0.02),
        (84.4804, 118.2069, 0.2431, 0.3562, -4.2211, -1.2672, -1.1821, -3.1492), (2.3488, 0.0048)),
    4: ((6, 4), (0.05, -0.015, -0.01, B22), (0.05, 0.075, 0.05, 0.1),
        (84.4508, 117.8869, 0.7731, 1.3958, -4.2134, -1.2668, -1.1789, -3.1318), (2.3307, 0.0032)),
}
U = np.array([10.0, 15.0])  # the pulse perturbation of Figures 4 and 5

for k, ((a1, a2), (b11, b12, b21, b22), (t11, t12, t21, t22), tab, (Rc_p, Rinf_p)) in SETS.items():
    m1, m2 = tab[0], tab[1]
    coeffs = np.array([
        m1 * (a1 - b11 * m1 + b12 * m2),            # Phi1
        m2 * (a2 + b21 * m1 - b22 * m2),            # Phi2
        a1 - 2 * b11 * m1 + b12 * m2,               # gamma11 (correct sign)
        b12 * m1,                                   # gamma12
        b21 * m2,                                   # gamma21
        a2 + b21 * m1 - 2 * b22 * m2,               # gamma22 (correct sign)
    ])
    err = np.abs(coeffs - np.array(tab[2:])).max()
    P1, P2, g11, g12, g21, g22 = tab[2:]
    A = np.array([[g11, g12], [g21, g22]])
    Th = np.array([P1, P2])
    m = np.array([m1, m2])
    Bs = [np.diag([t11, t21]), np.diag([t12, t22])]
    S = np.kron(np.eye(2), A) + np.kron(A, np.eye(2)) + sum(np.kron(B, B) for B in Bs)
    Rc = -0.5 * max(np.linalg.eigvals(S).real)

    def rhs(_t, y):
        M = y[:2]
        P = y[2:].reshape(2, 2, order="F")
        dM = A @ M + Th
        dP = (A @ P + P @ A.T + sum(B @ P @ B for B in Bs) + np.outer(Th, M) + np.outer(M, Th)
              + sum(B @ (np.outer(M, m) + np.outer(m, M) + np.outer(m, m)) @ B for B in Bs))
        return np.concatenate([dM, dP.flatten(order="F")])

    y0 = np.concatenate([U, np.outer(U, U).flatten(order="F")])
    sol = solve_ivp(rhs, (0, 4000), y0, dense_output=True, rtol=1e-10, atol=1e-12)
    W = lambda t: sol.sol(t)[2] + sol.sol(t)[5]
    Rave = lambda t: -np.log(W(t) / W(0)) / (2 * t)
    print(f"Set {k}: max |Table 1 - recomputed| = {err:.4f};  R_c = {Rc:.4f} (Table 2: {Rc_p});"
          f"  W(4000) = {W(4000):.4f} > 0;  R_ave(100), R_ave(1000), R_ave(4000) = "
          f"{Rave(100):.5f}, {Rave(1000):.5f}, {Rave(4000):.5f} -> 0 (Table 2 R_inf: {Rinf_p})")
