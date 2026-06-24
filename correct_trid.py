import numpy as np
from scipy.optimize import brentq

def d_trid(n, lam):
    """ClosedFormDet.d: d(0)=1, d(1)=lam, d(n+2)=lam*d(n+1)-lam*d(n)"""
    if n == 0: return 1.0
    if n == 1: return lam
    d0, d1 = 1.0, lam
    for _ in range(2, n+1):
        d0, d1 = d1, lam*d1 - lam*d0
    return d1

print("CORRECT tridiagonal equation: d(m+1, α) - δ·d(m, α) = 0")
print("=" * 70)

for m in range(1, 8):
    theta = np.pi / (m + 2)
    alpha_m = 4 * np.cos(theta)**2
    
    # Solve for psi(delta) at various delta
    deltas = np.linspace(0, 0.01, 200)
    alphas = np.zeros_like(deltas)
    alphas[0] = alpha_m
    
    for i, d in enumerate(deltas[1:], 1):
        def F(a):
            return d_trid(m+1, a) - d * d_trid(m, a)
        try:
            alphas[i] = brentq(F, alpha_m - 0.5, alpha_m + 2.0)
        except:
            alphas[i] = np.nan
    
    good = ~np.isnan(alphas)
    coeffs = np.polyfit(deltas[good], alphas[good] - alpha_m, 4)
    c1 = coeffs[-2]
    c2 = coeffs[-3]
    
    # Compare with second_order_coeff formula
    s, c = np.sin(theta), np.cos(theta)
    c2_formula = s**2 * (2*(m+1)*c**2 - 1) / (c**2 * (m+2)**2)
    
    print(f"m={m}: c1={c1:.8f}, c2(fit)={c2:.8f}, c2(formula)={c2_formula:.8f}, "
          f"match={'✓' if abs(c2 - c2_formula) < 0.001 else '✗'}")

