"""Complete computer-assisted proof, with symmetry established by an exact
antisymmetric exclusion; no degree-145 optimality theorem is used.
Run: python verify146_complete.py  (requires SymPy and NumPy; do not use -O).
"""
import sys,pathlib,json,runpy,math
if not __debug__:raise RuntimeError('Verification requires assertions: do not run Python with -O.')
from fractions import Fraction as F
here=pathlib.Path(__file__).resolve().parent
if (here.parent/'work'/'python-packages').is_dir():sys.path.insert(0,str(here.parent/'work'/'python-packages'))
import sympy as s
sys.set_int_max_str_digits(100000)
# This reruns the entire finite search, rather than trusting a stored result.
runpy.run_path(str(here/'verify146_search.py'))
base=json.loads((here/'candidate146_certificate.json').read_text())
proof=json.loads((here/'search146_certificate.json').read_text())
search=json.loads((here/'search146_result.json').read_text())
cert=json.loads((here/'finalists146_certificate.json').read_text())
T=proof['basis_rows'];t=s.symbols('t')
W=t**44*(1-4*t)**7*(1-5*t)**4*(29*t*t-11*t+1)
def poly(cs):return s.Poly.from_list(list(reversed(cs)),t)
def mul(a,b):
    vs=[x*y for x in a for y in b];return min(vs),max(vs)
def ev(f,ab):
    v=(F(0),F(0))
    for c in f.all_coeffs():
        a,b=mul(v,ab);v=a+int(c),b+int(c)
    return v
covered={tuple([0]*17)};bounds=[]
for item in cert['finalists']:
    z=item['coordinates'];assert len(z)==17 and any(z)
    assert tuple(z) not in covered and tuple(-v for v in z) not in covered
    covered.add(tuple(z));covered.add(tuple(-v for v in z))
    R=s.Poly(sum(sum(z[i]*T[i][j] for i in range(17))*t**j for j in range(17)),t)
    assert R==poly(item['residual_coefficients_ascending'])
    fs=[poly(cs) for cs in item['factors_ascending']];es=item['exponents'];c=item['factor_constant']
    assert len(fs)==len(es) and c and all(isinstance(e,int) and e>0 for e in es)
    Q=s.Poly(c*s.prod(f.as_expr()**e for f,e in zip(fs,es)),t)
    assert Q==s.Poly(W*R.as_expr(),t) and Q.degree()==73
    product=s.prod(f.as_expr() for f in fs)
    D=s.Poly(sum(e*f.diff().as_expr()*s.cancel(product/f.as_expr()) for f,e in zip(fs,es)),t).primitive()[1]
    assert D==poly(item['critical_polynomial_ascending'])
    def norm_interval(ab):
        lo=hi=abs(c)
        for f,e in zip(fs,es):
            a,b=ev(f,ab);lower=0 if a<=0<=b else min(abs(a),abs(b))
            lo*=lower**e;hi*=max(abs(a),abs(b))**e
        return lo,hi
    vals=[];previous=F(0)
    for rec in item['critical_roots']:
        a,b=map(F,rec['root_interval']);assert previous<a<=b<F(1,4)
        assert D.count_roots(s.Rational(a.numerator,a.denominator),s.Rational(b.numerator,b.denominator))==1
        vals.append(norm_interval((a,b)));previous=b
    assert len(vals)==D.count_roots(0,s.Rational(1,4))
    win=item['maximizer_index_zero_based'];lo,hi=vals[win]
    assert all(v[1]<lo for j,v in enumerate(vals) if j!=win)
    assert all(norm_interval((v,v))[1]<lo for v in [F(0),F(1,4)])
    L,U=F(item['norm_lower']),F(item['norm_upper'])
    assert 0<L<lo<=hi<U
    bounds.append((L,U))
assert covered==set(map(tuple,search['leaves']))
winner=cert['winner_index'];L,U=bounds[winner]
assert all(U<a for j,(a,b) in enumerate(bounds) if j!=winner)
assert U<F(base['norm_upper'])
w=cert['finalists'][winner]
D=poly(w['critical_polynomial_ascending'])
a,b=s.Rational(1393840441137,10**13),s.Rational(1393840441138,10**13)
assert D.count_roots(a,b)==1
assert all(poly(cs).count_roots(a,b)==0 for cs in w['factors_ascending'])
root=w['critical_roots'][w['maximizer_index_zero_based']]['root_interval']
assert a<s.Rational(root[0])<=s.Rational(root[1])<b
print('PASS: every nonzero surviving vector is covered by a certified norm comparison.',flush=True)
print('PROVED: m_146 is the norm of finalist',winner,'and its only minimizers are this polynomial and its negative.',flush=True)
print('Exact value: |Q(alpha)|, with Q and the isolated maximizing root alpha specified in finalists146_certificate.json.',flush=True)
print('Norm strictly between',L,'and',U,flush=True)
print('Symmetry proved by exact antisymmetric exclusion; NO degree-145 optimality theorem used.',flush=True)
