"""Optional exact symbolic checks for the manuscript; requires SymPy.

These identities do not check the analytic estimates.
"""
from pathlib import Path
import json
import sympy as sp

if not __debug__:
    raise RuntimeError('Run with assertions enabled.')

x, n, s, c, d = sp.symbols('x n s c d', positive=True)
H = sp.Function('H')(x)
p = sp.Function('p')(s)
v = x * (1-x)
w = x**(n-1)

def K(f):
    return sp.expand(sp.diff(w*v*v*f, x, 2)/w)

def L(f):
    return v*sp.diff(f,x,2)+(n+2-(n+5)*x)*sp.diff(f,x)

expanded = (v*v*sp.diff(H,x,2)
    +2*x*(1-x)*((n+1)-(n+3)*x)*sp.diff(H,x)
    +(n*(n+1)-2*(n+1)*(n+2)*x+(n+2)*(n+3)*x*x)*H)
assert sp.simplify(K(H)-expanded)==0
inner = -L(H)+2*(n+2)*H
assert sp.simplify(sp.diff(K(H),x,2)-(-L(inner)+(n+3)*inner))==0

def D(f):
    return sp.Rational(2,3)*s*sp.diff(f,s)

u=c*(p-d)
u=D(u)+n*u
u=D(u)+(n-1)*u
u=D(u)-u
rhs=-sp.Rational(8,27)*c*s**3*p/(1+p)
target=(sp.diff(p,s,3)+3*n/s*sp.diff(p,s,2)
    +(9*n*n-15*n+1)/(4*s*s)*sp.diff(p,s)
    -27*n*(n-1)/(8*s**3)*(p-d)+p/(1+p))
assert sp.simplify(sp.Rational(27,8)*(u-rhs)/(c*s**3)-target)==0

y = sp.symbols('y', positive=True)
G = sp.Function('G')(y)
h=(G-1)/y
flat_curvature=n*(n+1)*h+2*(n+1)*y*sp.diff(h,y)+y*y*sp.diff(h,y,2)
assert sp.simplify(flat_curvature-(y*sp.diff(G,y,2)+2*n*sp.diff(G,y)+n*(n-1)*(G-1)/y))==0
u,z=sp.symbols('u z')
assert sp.factor(1/(u+z)-1/u+z/u**2-z**2/(u**2*(u+z)))==0
result={
    'all_symbolic_identities_pass':True,
    'identities':['curvature expansion','auxiliary-sphere factorization',
                  'general-dimensional profile transformation',
                  'flat profile curvature','exact nonlinear reciprocal remainder'],
    'scope':'Exact algebra only; not a check of the parabolic or geometric proof.'
}
(Path(__file__).parent/'identity-checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
