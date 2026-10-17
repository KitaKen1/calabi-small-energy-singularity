# Adapted from OpenAI release family 352 (commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb).
# Dimension 7. Assertions concern interval arithmetic; analytic interpretation is separate.
from fractions import Fraction
import os
# interval recurrence
try:
    from gmpy2 import mpz
except ImportError:
    mpz=int
scale=mpz(2)**384
def pt(a): return (a*scale,a*scale)
O,I=pt(0),pt(1)
def neg(x):return (-x[1],-x[0])
def plus(x,y):return (x[0]+y[0],x[1]+y[1])
def timesn(x,n):
    return (n*x[0],n*x[1]) if n>=0 else (n*x[1],n*x[0])
def sums(L):
    a=b=0
    for x,y in L:a+=x;b+=y
    return (a,b)
def mul(x,y):
    p=x[0]*y[0];q=x[1]*y[0];r=x[0]*y[1];s=x[1]*y[1]
    return (min(p,q,r,s)//scale, -(min(-p,-q,-r,-s)//scale))
def inv(x):
    assert x[0]*x[1]>0
    return (scale*scale//x[1], -(-scale*scale//x[0]))
def divn(x,n):
    assert n>0
    return (x[0]//n,-(-x[1]//n))
def rat(a,b): return divn(pt(a),b)
def mag(x):return max(x[1],-x[0])
def mid(x):
    a=(x[0]+x[1])//2
    return (a,a)
def widen(x,z):
    a=z[1] # nonnegative
    return (x[0]-a,x[1]+a)
def width(x):return x[1]-x[0]
# p and linear P
A,B,C=pt(21),rat(337,4),rat(-567,4)
def decimal(v):
    f=Fraction(str(v));return rat(f.numerator,f.denominator)
k=decimal("-.18836367584965855")
d=decimal(".13429616579359704")
ks=[I,O];ds=[O,I]

def origin():
    # z stores series for W=1+p; return p,p',p'' at s=1 and variation cols
    z=[[plus(I,d)]+ds,[k]+ks]; b=[]
    for i in range(99):   # b_i coeff reciprocal W
        q=recip(z,b,i)
        den=pt(27*(i+1)*(i+8)*(i+9))
        z.append([mul(inv(den),timesn(plus(x,O if j or i else pt(-1)),8)) for j,x in enumerate(q)])
    ans=[]
    for a in range(3):
        ans.append([sums(divn(timesn(plus(v[j],O if i or j else pt(-1)),(4,6*i,3*i*(3*i-2))[a]),4) for i,v in enumerate(z))
                    for j in range(3)])
    assert max(width(v) for t in ans for v in t)*10**60<scale
    return [mid(x[0]) for x in ans], [[mid(y) for y in x[1:]] for x in ans]+[ds]

def recip(z,b,i):
    # z list 1+p and tangent cols; b reciprocal
    jlen=len(z[0]);f=inv(z[0][0])
    first=neg(mul(f,sums(mul(z[t][0],b[i-t][0]) for t in range(1,i+1)))) if i else f
    q=[first]
    q+= [neg(mul(f,sums([mul(z[t][j],(first if t==0 else b[i-t][0])) for t in range(i+1)]+
                        [mul(z[t][0],b[i-t][j]) for t in range(1,i+1)]))) for j in range(1,jlen)]
    b.append(q)
    return q

def horner(c):
    # step=1/8
    x=O
    for y in reversed(c): x=plus(y,divn(x,8))
    return x

degree=int(os.environ.get("CALABI_CERT_DEGREE","50"))
def evolve(V,T,R,h):
    # h positive integer inverse block length ell=1/h; current s h=R/8; theta=(s-sc)*h, z_j=coeff
    # V p,p_theta,p_thetatheta; T corresponding variations, 4 cols (vs scaled and d)
    assert all(x[0]>rat(-923,1000)[1] and x[1]<rat(4,10)[0] for x in V[:1]) and mag(V[1])*100<4*scale and mag(V[2])*1000<10*scale, (h,R,[(v[0]/scale,v[1]/scale) for v in V])
    assert max(mag(v) for t in T for v in t)<6*scale
    z=[([plus(x,I) if i==0 else x]+T[i]) if i!=2 else [divn(y,2) for y in [x]+T[i]] for i,x in enumerate(V)]
    E=[plus(d,I),O,O,O,I] # z variable = p+1, term C(z-(1+d)), tangent
    b=[]
    # ratio s/ell = R/8 (could exact integer); multiply equation by 4*(ratio+theta)^3:
    # 4 r^3 z''' +84 r^2 z'' +337 r z' -567 (z-E) = 4/h^3 * r^3(b-1)
    for i in range(degree-2):
        recip(z,b,i)
        new=[]
        for j in range(5):
            def F(t):
                return plus(b[t][j],pt(-1) if j==t==0 else O) if t>=0 else O
            # multiply equation terms by 8^3
            x=divn(sums(timesn(F(i-p),4*(1,24,192,512)[p]*R**(3-p)) for p in range(4)),h**3)
            # (R+8theta)^3, coefficients 3R²*8; etc
            x=sums([x,
                timesn(z[i+2][j],-((4*i*24+84*8)*R**2*(i+1)*(i+2))),
                timesn(z[i+1][j],-((4*i*(i-1)*3+84*i*2+337)*64*R*(i+1))),
                timesn(z[i][j],-512*(4*i*(i-1)*(i-2)+84*i*(i-1)+337*i-567)),
                timesn(E[j] if i==0 else O,-567*512)])
            new.append(divn(x,4*(i+1)*(i+2)*(i+3)*R**3))
        z.append(new)
    z[0][0]=plus(z[0][0],pt(-1))
    # Cauchy remainder derived for all coefficients of STATE at degree degree-2 (differentiate z twice)
    # assert analytic sup all state <32 on radius .5; ratio=.25; err ≤ 32*(4/3)*.25^(degree-1)
    err=rat(48,4**(degree-1))
    res=[]
    for a in range(3):
        res.append([widen(horner([timesn(z[i][j],(1,i,i*(i-1))[a]) for i in range(a,degree+1)]),err) for j in range(5)])
    return [x[0] for x in res], [x[1:] for x in res]

def makeflows():
    global arithmetic_stats
    arithmetic_stats={'max_state_width':0,'max_matrix_entry_width':0,'min_reference_margin':scale}
    U,Z=origin()
    hlist=sum(([h]*64 for h in (64,32,16)),[])+[8]*(8*(56-8))
    allm=[];mins=[]
    for index,h in enumerate(hlist):
        V=[divn(x,h**i) for i,x in enumerate(U)]
        T=[[I if i==j else O for j in range(4)] for i in range(3)]
        # scaled variations vs scaled input
        if index==0:s128=128
        R=(s128*h)//16; assert R*16==s128*h
        mini=2*scale
        for t in range(8):
            mini=min(mini,V[0][0]+scale-(scale*6//1000+1))  # variation across substep < .006 analytically
            V,T=evolve(V,T,R+t,h)
        V=[timesn(x,h**i) for i,x in enumerate(V)]
        arithmetic_stats['max_state_width']=max(arithmetic_stats['max_state_width'],max(map(width,V)))
        assert max(map(width,V))*10**19<scale
        U=[mid(x) for x in V]
        M=[[divn(timesn(x,h**i),h**j if j<3 else 1) for j,x in enumerate(row)] for i,row in enumerate(T)]+[[O,O,O,I]]
        arithmetic_stats['max_matrix_entry_width']=max(arithmetic_stats['max_matrix_entry_width'],max(width(x) for row in M for x in row))
        arithmetic_stats['min_reference_margin']=min(arithmetic_stats['min_reference_margin'],mini)
        assert max(width(x) for row in M for x in row)*10**15<scale
        allm.append([[mid(x) for x in row] for row in M])
        mins.append((h,mini));s128+=128//h
        if index%64==0:print("block",index,"/",len(hlist),flush=True)
    return allm,mins,U,Z

def mm(x,y):
 return [[sums(mul(w,z) for w,z in zip(t,c)) for c in zip(*y)] for t in x]
def norm(x):return max(sum(mag(z) for z in t) for t in x)
