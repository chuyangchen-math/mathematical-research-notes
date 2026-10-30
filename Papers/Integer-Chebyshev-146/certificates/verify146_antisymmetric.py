"""Exclude nonzero antisymmetric differences by exact finite enumeration.
Requires SymPy and NumPy. Float arithmetic only proposes pruning; every prune
is checked with exact fractions. Run without Python's -O option.
"""
import sys,pathlib,json,math,time,runpy
if not __debug__:raise RuntimeError('Verification requires assertions: do not run Python with -O.')
from fractions import Fraction as F
here=pathlib.Path(__file__).resolve().parent
if (here.parent/'work'/'python-packages').is_dir():sys.path.insert(0,str(here.parent/'work'/'python-packages'))
import sympy as s
import numpy as np
sys.set_int_max_str_digits(100000)
runpy.run_path(str(here/'verify146.py'))
data=json.loads((here/'candidate146_certificate.json').read_text())
proof=json.loads((here/'antisymmetric146_certificate.json').read_text())
assert data['interpolation_forcing']['final_exponents']==[44,44,14,4,1]
# Verify the integral decomposition q(x)=A(t)+x B(t), t=x(1-x),
# on every monomial of degree <=32. Thus B has degree <=15 and
# q(x)-q(1-x)=(2x-1)B(t), without any division by 2.
t,x=s.symbols('t x');aa,bb=s.Poly(1,t),s.Poly(0,t)
for k in range(33):
    assert aa.domain==s.ZZ and bb.domain==s.ZZ
    assert aa.degree()<=16 and bb.degree()<=15
    assert s.Poly((aa.as_expr()+x*bb.as_expr()).subs(t,x*(1-x))-x**k,x).is_zero
    aa,bb=s.Poly(-t*bb.as_expr(),t),aa+bb
print('PASS: integral symmetric/antisymmetric decomposition through degree 32.',flush=True)
U=2*F(data['norm_upper']);N=16;L=proof['x_denominator'];D=L*L;T=proof['basis_rows']
assert len(T)==N and all(len(r)==N and all(isinstance(v,int) for v in r) for r in T)
assert abs(s.Matrix(T).det())==1
K=F(L*D**72)*U
def vec(m):
    assert 0<=m<=L//2
    n=m*(L-m)
    w=(2*m-L)*n**44*(D-4*n)**7*(D-5*n)**4*(29*n*n-11*n*D+D*D)
    return [w*n**j*D**(15-j) for j in range(N)]
def evals(n):
    v=vec(n)
    return [sum(c*a for c,a in zip(row,v)) for row in T]
ns=proof['gram_points_numerators'];weights=proof['gram_weights']
assert len(ns)==len(weights)>0 and all(isinstance(w,int) and w>0 for w in weights)
vs=[evals(n) for n in ns];den=sum(weights)*K*K
G=[[F(sum(w*v[i]*v[j] for w,v in zip(weights,vs)))/den for j in range(N)] for i in range(N)]
S=proof['quadratic_scale'];Q=proof['quadratic_integer_matrix']
assert S>0 and len(Q)==N and all(len(r)==N for r in Q)
assert all(Q[i][j]==Q[j][i] for i in range(N) for j in range(N))
E=[[G[i][j]-F(Q[i][j],S) for j in range(N)] for i in range(N)]
# Symmetric diagonally dominant with nonnegative diagonal => positive semidefinite.
assert all(E[i][i]>=sum(abs(E[i][j]) for j in range(N) if j!=i) for i in range(N))
mu=[[F(0) for j in range(N)] for i in range(N)];hs=[]
for i in range(N):
    for j in range(i):mu[i][j]=(F(Q[i][j],S)-sum(mu[i][k]*mu[j][k]*hs[k] for k in range(j)))/hs[j]
    hs.append(F(Q[i][i],S)-sum(mu[i][k]**2*hs[k] for k in range(i)))
    assert hs[-1]>0
inv=s.Matrix(Q).inv();Z=[]
for i in range(N):
    r=F(inv[i,i])*S;Z.append(math.isqrt(r.numerator//r.denominator))
assert Z==proof['coordinate_bounds']
CS=proof['constraint_scale'];B=proof['constraint_integer_rows'];pts=proof['constraint_points_numerators']
assert CS>0 and len(B)==len(pts)>0
for row,n in zip(B,pts):
    assert len(row)==N and all(isinstance(a,int) for a in row)
    av=evals(n)
    assert all(abs(F(a)*CS/K-b)<=F(1,2) for a,b in zip(av,row))
H=F(CS)+F(sum(Z),2)
print('PASS: unimodular basis, necessary rational ellipsoid, coordinate bounds,',len(B),'rounded point constraints.',flush=True)
# Transform linear constraints to Gram-Schmidt coordinates y = mu^T z,
# with a unit diagonal understood in mu.
C=[];sigma=[]
for row in B:
    c=[];sig=[];v=F(0)
    for i in range(N):
        c.append(F(row[i])-sum(c[j]*mu[i][j] for j in range(i)))
        v+=c[-1]**2/hs[i];sig.append(v)
    C.append(c);sigma.append(sig)
CF=np.array([[float(v/H) for v in row] for row in C])
SF=np.array([[float(v/(H*H)) for v in row] for row in sigma])
z=[0]*N;y=[F(0)]*N;nodes=0;pruned=0;leaves=[];start=time.time();last=start
def walk(k,remaining):
    global nodes,pruned,last
    nodes+=1
    if nodes%10000==0 and time.time()-last>20:
        print('SEARCH nodes',nodes,'exact prunes',pruned,'surviving leaves',len(leaves),'seconds',round(time.time()-start,1),flush=True);last=time.time()
    if k<N-1:
        fixed=CF[:,k+1:]@np.array([float(v) for v in y[k+1:]])
        radius=np.sqrt(np.maximum(0,float(remaining)*SF[:,k])) if k>=0 else np.zeros(len(B))
        margin=np.abs(fixed)-radius-1
        # Float values have no authority: a proposed prune must pass this exact test.
        for j in np.argsort(margin)[-3:][::-1]:
            if margin[j]<=1e-10:break
            exact=abs(sum(C[j][i]*y[i] for i in range(k+1,N)))
            variance=sigma[j][k] if k>=0 else F(0)
            if exact>H and (exact-H)**2>remaining*variance:
                pruned+=1;return
    if k<0:
        # Check every weakened point constraint exactly, even if floating screening missed it.
        if any(abs(sum(b*v for b,v in zip(row,z)))>H for row in B):pruned+=1;return
        leaves.append(z.copy());print('LEAF',z,flush=True);return
    center=-sum(mu[i][k]*z[i] for i in range(k+1,N));r=remaining/hs[k]
    assert r>=0
    rootceil=math.isqrt(r.numerator//r.denominator)+1
    floor=center.numerator//center.denominator
    lo=max(-Z[k],floor-rootceil-1);hi=min(Z[k],floor+rootceil+2)
    for v in range(lo,hi+1):
        yy=F(v)-center;cost=hs[k]*yy*yy
        if cost>remaining:continue
        z[k]=v;y[k]=yy;walk(k-1,remaining-cost)
    z[k]=0;y[k]=F(0)
walk(N-1,F(1))
assert leaves==[[0]*N]
result={'nodes':nodes,'pruned':pruned,'leaves':leaves,'only_zero':True,'elapsed_seconds':time.time()-start,'scope':'No degree-145 optimality result is used. Strong factors plus this exclusion force reflection symmetry.'}
(here/'antisymmetric146_result.json').write_text(json.dumps(result,indent=2))
print('PASS: only S=0 satisfies the necessary conditions. All competitors below U are symmetric, without any degree-145 optimality theorem.',flush=True)
print('ANTISYMMETRIC COMPLETE nodes',nodes,'seconds',time.time()-start,flush=True)
