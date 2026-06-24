import numpy as np
from scipy.optimize import brentq

def d_trid(n, lam):
    if n == 0: return 1.0
    if n == 1: return lam
    d0, d1 = 1.0, lam
    for _ in range(2, n+1):
        d0, d1 = d1, lam*d1 - lam*d0
    return d1

def d_trid_deriv(n, lam, dx=1e-7):
    return (d_trid(n, lam+dx) - d_trid(n, lam-dx)) / (2*dx)

print("Lagrange h(α) = (α-α_m)·d(m,α)/d(m+1,α)")
print("c_1 = lim h(α) = d(m,α_m)/d'(m+1,α_m)")
print("c_2 = (1/2)·d/dα[h²]|_{α_m} = c_1·h'(α_m)")
print("=" * 70)

for m in range(1, 8):
    theta = np.pi / (m + 2)
    alpha_m = 4 * np.cos(theta)**2
    
    # c_1 from first_order_coeff
    dm = d_trid(m, alpha_m)
    ddm1 = d_trid_deriv(m+1, alpha_m)
    c1 = dm / ddm1
    
    # h(α) near α_m: removable singularity, h(α_m) = c_1
    def h_func(a):
        dm1 = d_trid(m+1, a)
        if abs(dm1) < 1e-15: return c1  # removable singularity
        return (a - alpha_m) * d_trid(m, a) / dm1
    
    # h'(α_m) via numerical derivative
    dx = 1e-6
    h_prime = (h_func(alpha_m + dx) - h_func(alpha_m - dx)) / (2*dx)
    
    # c_2 from Lagrange: c_2 = c_1 · h'(α_m)
    c2_lagrange = c1 * h_prime
    
    # c_2 from formula
    s, c = np.sin(theta), np.cos(theta)
    c2_formula = s**2 * (2*(m+1)*c**2 - 1) / (c**2 * (m+2)**2)
    
    print(f"m={m}: c1={c1:.6f}, h'(α_m)={h_prime:.6f}, "
          f"c2(Lagrange)={c2_lagrange:.6f}, c2(formula)={c2_formula:.6f}, "
          f"match={'✓' if abs(c2_lagrange - c2_formula) < 1e-4 else '✗'}")

# Now compute c_3 via Lagrange for m=2
print("\n--- c_3 computation for m=1,2,3 ---")
for m in range(1, 4):
    theta = np.pi / (m + 2)
    alpha_m = 4 * np.cos(theta)**2
    
    deltas = np.linspace(0, 0.005, 300)
    alphas = np.zeros_like(deltas)
    alphas[0] = alpha_m
    for i, d in enumerate(deltas[1:], 1):
        try:
            alphas[i] = brentq(lambda a: d_trid(m+1, a) - d*d_trid(m, a), 
                               alpha_m-0.5, alpha_m+2.0)
        except:
            alphas[i] = np.nan
    good = ~np.isnan(alphas)
    coeffs = np.polyfit(deltas[good], alphas[good] - alpha_m, 5)
    c1, c2, c3 = coeffs[-2], coeffs[-3], coeffs[-4]
    print(f"m={m}: c1={c1:.6f}, c2={c2:.6f}, c3={c3:.6f}")

