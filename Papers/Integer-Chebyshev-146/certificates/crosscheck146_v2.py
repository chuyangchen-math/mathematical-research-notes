"""Recheck BOTH finite searches without any early point-constraint pruning.
Runs the complete verifier first. Requires SymPy and NumPy; do not use -O.
"""
import sys,pathlib,json,math,time,runpy
from fractions import Fraction as F
if not __debug__:raise RuntimeError('Do not run verification with -O.')
here=pathlib.Path(__file__).resolve().parent
if (here.parent/'work'/'python-packages').is_dir():sys.path.insert(0,str(here.parent/'work'/'python-packages'))
import numpy as np
runpy.run_path(str(here/'verify146_complete.py'))
def check(prefix):
    p=json.loads((here/(prefix+'_certificate.json')).read_text())
    Q=p['quadratic_integer_matrix'];N=len(Q);S=p['quadratic_scale'];Z=p['coordinate_bounds']
    mu=[[F(0) for j in range(N)] for i in range(N)];hs=[]
    for i in range(N):
        for j in range(i):mu[i][j]=(F(Q[i][j],S)-sum(mu[i][k]*mu[j][k]*hs[k] for k in range(j)))/hs[j]
        hs.append(F(Q[i][i],S)-sum(mu[i][k]**2*hs[k] for k in range(i)));assert hs[-1]>0
    B=np.array(p['constraint_integer_rows'],dtype=np.int64);H2=2*p['constraint_scale']+sum(Z)
    assert all(2*sum(abs(b)*z for b,z in zip(row,Z))<2**63 for row in p['constraint_integer_rows'])
    z=[0]*N;nodes=0;sphereleaves=0;survivors=[];start=time.time();last=start
    def walk(k,rem):
        nonlocal nodes,sphereleaves,last
        nodes+=1
        if nodes%100000==0 and time.time()-last>20:
            print(prefix,'CROSSCHECK',nodes,'ellipsoid points',sphereleaves,'seconds',round(time.time()-start,1),flush=True);last=time.time()
        if k<0:
            sphereleaves+=1
            if np.all(2*np.abs(B@np.array(z,dtype=np.int64))<=H2):survivors.append(z.copy())
            return
        center=-sum(mu[i][k]*z[i] for i in range(k+1,N));r=rem/hs[k]
        assert r>=0
        root=math.isqrt(r.numerator//r.denominator)+1;fl=center.numerator//center.denominator
        for v in range(max(-Z[k],fl-root-1),min(Z[k],fl+root+2)+1):
            cost=hs[k]*(v-center)**2
            if cost<=rem:z[k]=v;walk(k-1,rem-cost)
        z[k]=0
    walk(N-1,F(1))
    expected=json.loads((here/(prefix+'_result.json')).read_text())['leaves']
    assert set(map(tuple,survivors))==set(map(tuple,expected))
    out={'method':'Exact rational ellipsoid enumeration without early point-constraint pruning; integer point tests at every ellipsoid leaf.','nodes':nodes,'ellipsoid_integer_points':sphereleaves,'survivors':survivors,'matches_pruned_search':True,'elapsed_seconds':time.time()-start}
    (here/(prefix+'_crosscheck.json')).write_text(json.dumps(out,indent=2))
    print(prefix,'COMPLETE',out,flush=True)
check('antisymmetric146')
check('search146')
print('PASS: both independent enumeration paths agree for both symmetry and minimization.',flush=True)
