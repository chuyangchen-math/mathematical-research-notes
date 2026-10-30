"""Exact certificate verification. Requires Python 3 and SymPy.
Run: python verify146.py
This certifies an upper bound and forced factors, NOT global optimality.
"""
import json, math, pathlib, sys
if not __debug__:raise RuntimeError('Verification requires assertions: do not run Python with -O.')
from fractions import Fraction as R
here=pathlib.Path(__file__).resolve().parent
local=here.parent/'work'/'python-packages'
if local.is_dir():sys.path.insert(0,str(local))
import sympy as s
sys.set_int_max_str_digits(100000)
data=json.loads((here/'candidate146_certificate.json').read_text())
t,x=s.symbols('t x')
def poly(cs,v):return s.Poly.from_list(list(reversed(cs)),v)
def mul(a,b):
    vs=[u*v for u in a for v in b]
    return min(vs),max(vs)
def ev(f,ab):
    v=(R(0),R(0))
    for c in f.all_coeffs():
        a,b=mul(v,ab);v=a+int(c),b+int(c)
    return v
active=[(poly(cs,t),e) for cs,e in zip(data['factors_ascending'],data['exponents']) if e]
assert all(isinstance(e,int) and e>0 for f,e in active)
assert sum(f.degree()*e for f,e in active)==73
product=s.prod(f.as_expr() for f,e in active)
D=s.Poly(sum(e*f.diff().as_expr()*s.cancel(product/f.as_expr()) for f,e in active),t).primitive()[1]
assert D==poly(data['critical_polynomial_ascending'],t)
def qabs(ab):
    lo=hi=R(1)
    for f,e in active:
        a,b=ev(f,ab)
        lower=0 if a<=0<=b else min(abs(a),abs(b))
        lo*=lower**e;hi*=max(abs(a),abs(b))**e
    return lo,hi
vals=[];previous=R(0)
for rec in data['critical_roots']:
    a,b=map(R,rec['root_interval'])
    assert previous<a<=b<R(1,4)
    assert D.count_roots(s.Rational(a.numerator,a.denominator),s.Rational(b.numerator,b.denominator))==1
    previous=b;vals.append(qabs((a,b)))
assert len(vals)==D.count_roots(0,s.Rational(1,4))
winner=data['maximizer_index_zero_based'];lo,hi=vals[winner]
assert all(v[1]<lo for i,v in enumerate(vals) if i!=winner)
assert all(qabs((z,z))[1]<lo for z in [R(0),R(1,4)])
L,U=R(data['norm_lower']),R(data['norm_upper'])
assert 0<L<lo<=hi<U
print('PASS: degree 146, all critical points covered, unique maximizing t, strict rational norm bounds.')
# Initial forced factors from the Markov brothers inequality and integer resultants.
Cs=[R(1)]
for k in range(1,147):Cs.append(Cs[-1]*R(2*(146**2-(k-1)**2),k*(2*k-1)))
initial=[]
for rec in data['markov_forced_factors']:
    name=rec['factor'];degree=rec['degree'];a=rec['leading_coefficient_abs']
    if name.startswith('h'):
        f=poly(data['factors_ascending'][int(name[1:])-1],t)
        f=s.Poly(f.as_expr().subs(t,x*(1-x)),x)
    else:f=s.Poly({'x':x,'x-1':x-1,'2x-1':2*x-1}[name],x)
    assert f.is_primitive and f.is_irreducible
    assert f.degree()==degree and abs(f.LC())==a and f.count_roots(0,1)==degree
    assert all(a**(146-k)*(U*Cs[k])**degree<1 for k in range(rec['multiplicity']))
    initial.append((f,rec['multiplicity']))
print('PASS: initial Markov/resultant forced factors.')
cert=data.get('interpolation_forcing')
if cert:
    fs=[poly(cs,x) for cs in cert['factors_ascending']]
    es=cert['initial_exponents'].copy()
    assert len(fs)==len(es)==len(initial)
    assert all(f==g and e==a for f,e,(g,a) in zip(fs,es,initial))
    roots=[]
    for f,rs in zip(fs,cert['root_intervals']):
        intervals=[tuple(map(R,v)) for v in rs]
        assert f.is_primitive and f.is_irreducible and len(intervals)==f.degree()
        for a,b in intervals:
            assert 0<=a<=b<=1
            assert f.count_roots(s.Rational(a.numerator,a.denominator),s.Rational(b.numerator,b.denominator))==1
        assert all(intervals[i][1]<intervals[i+1][0] for i in range(len(intervals)-1))
        roots.append(intervals)
    for num,step in enumerate(cert['steps']):
        assert es==step['exponents_before']
        d=146-sum(f.degree()*e for f,e in zip(fs,es))
        nodes=[R(v,step['nodes_denominator']) for v in step['nodes_numerators']]
        assert len(nodes)==d+1 and len(set(nodes))==d+1 and all(0<=z<=1 for z in nodes)
        weights=[]
        for i,z in enumerate(nodes):
            den=math.prod(z-w for k,w in enumerate(nodes) if k!=i)
            fz=math.prod(ev(f,(z,z))[0]**e for f,e in zip(fs,es))
            assert fz
            weights.append(1/abs(den*fz))
        j=step['target_index'];bounds=[]
        for a,b in roots[j]:
            bound=sum(weights[i]*math.prod(max(abs(a-z),abs(b-z)) for k,z in enumerate(nodes) if k!=i) for i in range(len(nodes)))
            bounds.append(U*bound)
        if step.get('reflect_root_bounds'):
            assert es[0]==es[1]
            for f in fs[2:]:assert s.Poly(f.as_expr().subs(x,1-x),x) in [f,-f]
            assert s.Poly(fs[j].as_expr().subs(x,1-x),x) in [fs[j],-fs[j]]
            bounds=[min(bounds[k],bounds[-1-k]) for k in range(len(bounds))]
        assert abs(int(fs[j].LC()))**d*math.prod(bounds)<1
        if step.get('reflection_also'):
            assert j in [0,1] and fs[0]==s.Poly(x,x) and fs[1]==s.Poly(x-1,x) and es[0]==es[1]
            for f in fs[2:]:assert s.Poly(f.as_expr().subs(x,1-x),x) in [f,-f]
            es[1-j]+=1
        es[j]+=1
    assert es==cert['final_exponents']
    residual=146-sum(f.degree()*e for f,e in zip(fs,es))
    assert residual==cert['residual_degree']
    print('PASS:',len(cert['steps']),'exact interpolation/resultant steps; final exponents',es,'residual degree',residual)
print('STAGE 1 ONLY: upper bound and reduction verified; global optimality is handled by verify146_complete.py.')
