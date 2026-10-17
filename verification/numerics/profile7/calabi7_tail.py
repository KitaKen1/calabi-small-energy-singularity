"""Exact rational algebra, root enclosures and half-line contraction bounds.
These checks are one component of a proof, not a whole shooting certificate.
"""
from fractions import Fraction as F
from pathlib import Path
import json,math

def add(a,b):return [ (a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b))) ]
def mul(a,b):
    c=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    return c
def smul(a,c):return [x*c for x in a]
def peval(a,x):
    y=F(0)
    for v in reversed(a):y=y*x+v
    return y
def deriv(a):return [i*a[i] for i in range(1,len(a))] or [F(0)]
def interval(a,x):
    lo=hi=F(0)
    for v in reversed(a):
        z=[lo*x[0],lo*x[1],hi*x[0],hi*x[1]];lo,hi=min(z)+v,max(z)+v
    return lo,hi
def absmax(v):return max(abs(v[0]),abs(v[1]))

def formal_tail(order=6):
    a=[[F(0)] for j in range(order+1)];b=[[F(0)] for j in range(order+1)];b[0]=[F(1)]
    a[1]=[F(0),-F(567,4)];b[1]=smul(a[1],-1)
    for j in range(2,order+1):
        v=-3*(j-1);L=F(v*(v-1)*(v-2)+21*v*(v-1))+F(337,4)*v-F(567,4)
        cross=[F(0)]
        for k in range(1,j):cross=add(cross,mul(a[k],b[j-k]))
        a[j]=add(smul(a[j-1],-L),smul(cross,-1));b[j]=add(smul(a[j],-1),smul(cross,-1))
    differential=[[F(0)] for j in range(order+2)];differential[1]=[F(0),F(567,4)]
    for j in range(1,order+1):
        v=-3*j;L=F(v*(v-1)*(v-2)+21*v*(v-1))+F(337,4)*v-F(567,4)
        differential[j+1]=smul(a[j],L)
    residual=[[F(0)] for j in range(2*order+2)]
    for j,v in enumerate(differential):
        residual[j]=add(residual[j],v)
        for k in range(1,order+1):residual[j+k]=add(residual[j+k],mul(v,a[k]))
    for j in range(1,order+1):residual[j]=add(residual[j],a[j])
    assert all(all(x==0 for x in residual[j]) for j in range(order+1))
    return a,residual

def exp_upper(x,N=80):
    terms=[F(1)]
    for j in range(1,N+2):terms.append(terms[-1]*x/j)
    return sum(terms[:-1])+terms[-1]/(1-x/(N+2))

def checks():
    # Every calculation below uses rational numbers, including exponential bounds.
    A=F(21);B=F(337,4);C=-F(567,4);S=56
    alpha=A/(2*S);beta=B/(2*S*S);gamma=1+C/(2*S**3)
    D=lambda x:x**3+alpha*x*x+beta*x+gamma
    rlo=F('1.061676856304');rhi=F('1.061676856305')
    assert alpha*alpha-3*beta<0 and D(-rhi)<0<D(-rlo)
    ulo=(rlo-alpha)/2;uhi=(rhi-alpha)/2
    vlo=F('.866302348759');vhi=F('.866302348762')
    assert vlo*vlo<beta+2*rlo*ulo-uhi*uhi
    assert vhi*vhi>beta+2*rhi*uhi-ulo*ulo
    Emin=(rlo+ulo)**2+vlo**2;emin=F('1.73')
    assert emin**2<Emin and uhi**2+vhi**2<F('.971')**2
    M=[rhi**i/(rlo*Emin)+F('.971')**i/(ulo*vlo*emin) for i in range(3)]
    assert max(M)<F('1.9')
    assert 1/(2*ulo*vlo*emin)<F('.8')
    L=F('1.9')*(A/(2*S)+B/(2*S*S)+abs(C)/(2*S**3)+F('.0021'))
    H=A/(2*S)*F('1.062')**2+B/(2*S*S)*F('1.062')+abs(C)/(2*S**3)+F('.0021')
    assert L<F('.39') and H<F('.23')
    # Uniform parameter neighborhood, much wider than the final shooting box.
    a,residual=formal_tail();drange=(F('.13429'),F('.13430'))
    Pmax=sum(absmax(interval(a[j],drange))/S**(3*j) for j in range(1,7))
    Emax=sum(absmax(interval(v,drange))/S**(3*j) for j,v in enumerate(residual) if j>6)/(1-Pmax)
    DP=sum(absmax(interval(deriv(a[j]),drange))/S**(3*j) for j in range(1,7))
    assert Pmax<F('.00011') and Emax<F('4e-22') and DP<F('.001')
    # Complex disks of the finite Taylor computation: h>=8, hs>=64.
    R=F('63.5');J=21/R+B/R**2+2*abs(C)/R**3+F(1,512)/F('.047')**2
    assert J<F('1.24') and 6*exp_upper(J/2)<32
    e=exp_upper(21/(2*R))
    H2=e*(F('.01')+(B/R**2*F('.04')+abs(C)/R**3*F('1.5')+F(1,512)*F('.953')/F('.047'))/2)/(1-e*B/(4*R**2))
    assert H2<F('.04')
    assert F('.04')/2+F('.04')/8<F('.03')
    assert F('.04')/8+F('.04')/128<F('.006')
    # Real partial transfer norm; reference margin is checked by the flow ledger.
    Jr=max(F(1),A/64+B/64**2+2*abs(C)/64**3+F(1,512)/F('.07')**2)
    assert exp_upper(Jr)<3
    # Origin Banach algebra: |k-k0|,|d-d0| <= .01, radius |r|<3.
    assert 3*F('.198364')+F('.2')<F('.796')
    assert 1/(F('1.12429')-F('.796'))<F('3.1')
    assert 9*(F('3.1')+1)/243<F('.2') and 9*F('3.1')**2/243<1
    assert 3*F('.198364')+9*(F('3.1')+1)/243<F('.75')
    out=dict(all_exact_checks_pass=True,root_real=[str(-rhi),str(-rlo)],root_imag=[str(vlo),str(vhi)],
       M_upper=[float(x) for x in M],tail_lipschitz_upper=float(L),tail_homogeneous_upper=float(H),
       tail_residual_upper=float(Emax),tail_abs_upper=float(Pmax),tail_parameter_derivative_upper=float(DP),
       complex_H2_upper=float(H2),complex_J_upper=float(J),real_partial_transfer_upper=3,
       warning='Necessary proof components only; finite shooting and geometric realization are separate.')
    (Path(__file__).resolve().parent/'calabi7_tail_checks.json').write_text(json.dumps(out,indent=2)+'\n');return out

if __name__=='__main__':print(json.dumps(checks(),indent=2))
