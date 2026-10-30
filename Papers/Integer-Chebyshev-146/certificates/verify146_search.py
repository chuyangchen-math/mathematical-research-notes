"""Verify the search reduction and exhaustively enumerate its integer points.
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
anti=runpy.run_path(str(here/'verify146_antisymmetric.py'))
assert anti['result']['only_zero'] is True
data=json.loads((here/'candidate146_certificate.json').read_text())
proof=json.loads((here/'search146_certificate.json').read_text())
assert data['interpolation_forcing']['final_exponents']==[44,44,14,4,1]
U=F(data['norm_upper']);N=17;D=proof['denominator'];T=proof['basis_rows']
assert len(T)==N and all(len(r)==N and all(isinstance(v,int) for v in r) for r in T)
assert abs(s.Matrix(T).det())==1
K=F(D**73)*U
def vec(n):
    assert 0<=n<=D//4
    w=n**44*(D-4*n)**7*(D-5*n)**4*(29*n*n-11*n*D+D*D)
    return [w*n**j*D**(16-j) for j in range(N)]
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
t=s.symbols('t')
candidate=s.Poly(t**2*(1-4*t)*(1-5*t)**2*(29*t*t-11*t+1)**2*(-169*t**3+94*t*t-17*t+1)*(961*t**4-712*t**3+194*t*t-23*t+1),t)
coeff=s.Matrix([candidate.nth(i) for i in range(N)])
zc=s.Matrix(T).T.inv()*coeff
assert all(v.q==1 for v in zc)
expected={tuple([0]*N),tuple(map(int,zc)),tuple(-int(v) for v in zc)}
actual=set(map(tuple,leaves))
result={'nodes':nodes,'pruned':pruned,'leaves':leaves,'candidate_coordinates':list(map(int,zc)),'only_zero_and_signed_candidate':actual==expected,'elapsed_seconds':time.time()-start,'scope':'Self-contained symmetry reduction via exact antisymmetric exclusion; no degree-145 optimality theorem used.'}
(here/'search146_result.json').write_text(json.dumps(result,indent=2))
print('COMPLETE nodes',nodes,'leaves',len(leaves),'seconds',time.time()-start,flush=True)
print('Only zero and signed INITIAL candidate:',actual==expected,'(the other pair is compared by verify146_complete.py)',flush=True)
