"""Exact interval transfer ledger for a saved finite shooting computation.
The binary cache is generated afresh by calabi7_verify.py in this directory.
Do not run this script on a cache from an untrusted source.
"""
from pathlib import Path
from fractions import Fraction as F
import json,pickle,sys,time
import calabi7_interval as q

P=Path(__file__).resolve().parent

def upper(x):return F(int(q.mag(x)),int(q.scale))
def norm(x):return F(int(q.norm(x)),int(q.scale))
def decimal(x):return q.decimal(x)
def sub(a,b):return q.plus(a,q.neg(b))
def divide(a,b):return q.mul(a,q.inv(b))
def sq(a):return q.mul(a,a)
def matrix_bounds():
    r=(decimal('1.061676856304')[0],decimal('1.061676856305')[1])
    u=q.divn(sub(r,decimal('.1875')),2)
    v=(decimal('.866302348759')[0],decimal('.866302348762')[1])
    E=q.plus(sq(q.plus(r,u)),sq(v))
    G=[[divide(q.plus(sq(u),sq(v)),E),divide(q.timesn(u,-2),E),q.inv(E)],
       [divide(q.mul(r,q.plus(r,q.timesn(u,2))),q.timesn(E,2)),divide(u,E),q.neg(q.divn(q.inv(E),2))],
       [divide(q.mul(r,sub(q.mul(u,q.plus(r,u)),sq(v))),q.timesn(q.mul(v,E),2)),
        q.neg(divide(sub(q.plus(sq(v),sq(r)),sq(u)),q.timesn(q.mul(v,E),2))),
        q.neg(divide(q.plus(r,u),q.timesn(q.mul(v,E),2)))]]
    L=[[decimal(x) for x in row] for row in [
        ['.314179536995','-.291705661194','.333691814294'],
        ['.342910231503','.145852830597','-.166845907147'],
        ['-.019504134458','-.324829825596','-.288655402867']]]
    eps=max(upper(sub(a,b)) for ar,br in zip(G,L) for a,b in zip(ar,br))
    assert eps<F('1e-10') and norm(G[:1])<F('.94') and norm(G[1:])<F('.66')
    return G,L,eps

def run(it):
    start=time.time();rec=json.loads((P/f'calabi7_newton_{it}.json').read_text())
    with (P/f'calabi7_flows_{it}.pickle').open('rb') as f:flows,mins,U,Z=pickle.load(f)
    # The decimal inverse is merely a chosen rational coordinate matrix.
    pre=[[decimal(x) for x in row] for row in rec['inverse_jacobian']]
    Z=q.mm(Z,pre)
    maxprod=maxD=maxK=maxZ=F(0)
    margin=min(F(int(r),int(q.scale)) for h,r in mins)
    assert margin>F('.07')
    for i in range(1,len(flows)+1):
        T=[[q.I if m==n else q.O for n in range(4)] for m in range(4)]
        D=F(0);K=0
        for j in reversed(range(i)):
            h,r=mins[j];dT=norm([row[:3] for row in T[:3]])
            D+=dT
            K+=int(q.norm([row[:3] for row in T[:3]])*q.scale**2//(h*r**3))+1
            T=q.mm(T,flows[j]);maxprod=max(maxprod,norm(T))
        maxD=max(maxD,D);maxK=max(maxK,K);maxZ=max(maxZ,norm(q.mm(T,Z)))
        if i%128==0:print('ledger',i,'/',len(flows),flush=True)
    G,L,eps=matrix_bounds();Y=q.mm(T,Z)[:3];LY=q.mm(L,Y)
    eye_error=norm([[sub(x,q.I if i==j else q.O) for j,x in enumerate(row)] for i,row in enumerate(LY[1:])])
    # Rational tail polynomial evaluation, using interval Horner in parameter d.
    from calabi7_tail import formal_tail
    a,_=formal_tail();d=decimal(rec['input']['d']);pa=[q.O,q.O,q.O]
    for j in range(1,7):
        aj=q.O
        for c in reversed(a[j]):aj=q.plus(q.mul(aj,d),q.rat(c.numerator,c.denominator))
        for i,factor in enumerate([1,-3*j,3*j*(3*j+1)]):pa[i]=q.plus(pa[i],q.divn(q.timesn(aj,factor),56**(3*j+i)))
    residual=[[sub(u,p)] for u,p in zip(U,pa)]
    out=dict(iteration=it,blocks=len(flows),degree=rec.get('degree',50),
        min_reference_margin=float(margin),max_product=float(maxprod),sum_products=float(maxD),weighted_sum=float(maxK),max_preconditioned_variation=float(maxZ),origin_variation_norm=float(norm(Z)),
        q_linear_row=float(norm(LY[:1])),unstable_linear_identity_error=float(eye_error),
        residual_jet=float(norm(residual)),projected_residual=float(norm(q.mm(L,residual))),
        parameter_matrix=[[str(F(x)) for x in row] for row in rec['inverse_jacobian']],
        parameter_d_row=float(norm(pre[1:])),projection_entry_error=float(eps),seconds=time.time()-start,
        exact_bounds={k:str(v) for k,v in dict(product=maxprod,sum_products=maxD,weighted_sum=maxK,variation=maxZ,origin_variation=norm(Z),margin=margin,q_linear=norm(LY[:1]),identity_error=eye_error,jet_residual=norm(residual),projected_residual=norm(q.mm(L,residual)),d_row=norm(pre[1:])).items()},
        exact_integer_computation=True,whole_proof_certified=False)
    (P/f'calabi7_ledger_{it}.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2),flush=True)
    return out

if __name__=='__main__':run(int(sys.argv[1]))
