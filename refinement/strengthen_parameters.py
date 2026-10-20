"""Tighten only rational proof bounds in the existing ternary parameter module.

All numerical checking uses fractions, including rigorous atanh remainder bounds.
The resulting Lean module follows the original proof skeleton. It still requires
Lean rebuilding; this script is an independent rational arithmetic check only.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse
import json
import re

SCRIPT_DIR = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--source', type=Path, default=SCRIPT_DIR.parent/'three_sum_source',
                    help='Pristine checkout of source commit 4a4a98e6eca4fc16817f0d2074026fdaece52efd.')
parser.add_argument('--output', type=Path, default=SCRIPT_DIR,
                    help='Directory for candidate source and exact rational certificate.')
args = parser.parse_args()
SOURCE = args.source.resolve() / 'Submission/ThreeSum/TernaryParameters.lean'
OUT = args.output.resolve()

N = 16
LOG_SCALE = 10**12
ENTROPY_SCALE = 10**11

def floor_q(x, scale):
    return F(x.numerator * scale // x.denominator, scale)

def ceil_q(x, scale):
    return -floor_q(-x, scale)

def round_bounds(b, scale):
    return floor_q(b[0], scale), ceil_q(b[1], scale)

def log_series(x):
    """Symmetric certified interval from N terms of 2 atanh((x-1)/(x+1))."""
    t = (x-1)/(x+1)
    assert abs(t) < 1
    s = 2 * sum((t**(2*k+1) / (2*k+1) for k in range(N)), F(0))
    # This is the exact (slightly coarser) remainder supplied by Mathlib's
    # Real.sum_range_sub_log_div_le after multiplying its half-log bound by 2.
    # The sharper analytic remainder could divide by 2*N+1, but doing so here
    # would not directly certify the unchanged Lean linarith proof skeleton.
    e = 2 * abs(t)**(2*N+1) / (1-t*t)
    return s-e, s+e

def plus(a, b):
    return a[0]+b[0], a[1]+b[1]

def times(c, a):
    return (c*a[0], c*a[1]) if c >= 0 else (c*a[1], c*a[0])

def ratio_positive(a, b):
    assert a[0] >= 0 and b[0] > 0
    return a[0]/b[1], a[1]/b[0]

pi = [F(81204903,10**8), F(317207,2*10**6), F(2934747,10**8)]
alpha = [F(90113327,10**8),F(1113553,12500000),F(978249,10**8)]
y=F(3632479,2*10**7)
z=F(7523953,10**8)
deficit=F(268969,2*10**7)
mean=pi[1]+2*pi[2]
values = {**{f'pi{i}':v for i,v in enumerate(pi)},
          **{f'alpha{i}':v for i,v in enumerate(alpha)},
          'three':F(3),'y':y,'bankArg':1+y+y*y,'z':z,
          'queryArg1':1+z,'queryArg2':1+z+z*z}
exponents={'pi0':1,'pi1':3,'pi2':6,'alpha0':1,'alpha1':4,'alpha2':7,
           'three':-1,'y':3,'z':4}
log_bounds={'two':round_bounds(log_series(F(2)),LOG_SCALE)}
for name,v in values.items():
    if name in exponents:
        e=exponents[name]
        normalized=round_bounds(log_series(v*F(2)**e),LOG_SCALE)
        log_bounds['normalized_'+name]=normalized
        log_bounds[name]=round_bounds(plus(normalized,times(-e,log_bounds['two'])),LOG_SCALE)
    else:
        log_bounds[name]=round_bounds(log_series(v),LOG_SCALE)

# Explicit sums preserve independent interval endpoints.
def isum(xs):
    out=(F(0),F(0))
    for x in xs:out=plus(out,x)
    return out

entropy_numerators={
    'Hpi':isum(times(-v,log_bounds[f'pi{i}']) for i,v in enumerate(pi)),
    'Halpha':isum(times(-v,log_bounds[f'alpha{i}']) for i,v in enumerate(alpha)),
    'partitionEntropy':plus(times(pi[1],log_bounds['two']),times(pi[2],log_bounds['three'])),
    'bankEntropy':plus(log_bounds['bankArg'],times(-(mean-deficit),log_bounds['y'])),
    'queryEntropy':isum([times(pi[1],log_bounds['queryArg1']),times(pi[2],log_bounds['queryArg2']),times(-deficit,log_bounds['z'])]),
}
entropy_bounds={name:round_bounds(ratio_positive(num,log_bounds['two']),ENTROPY_SCALE)
                for name,num in entropy_numerators.items()}

def frac(x):
    if x.denominator == 1:return str(x.numerator)
    return f'{x.numerator} / {x.denominator}'

text=SOURCE.read_text()
# More series terms make the smaller rational intervals straightforward to prove.
text=text.replace(') 8\n',') 16\n')
for name,b in log_bounds.items():
    theorem='log_'+name+'_bounds'
    pattern=r'((?:private )?theorem '+re.escape(theorem)+r'\s*:\s*).*?( := by)'
    var = '2' if name=='two' else name
    statement=f'({frac(b[0])} : ℝ) ≤ Real.log {var} ∧ Real.log {var} ≤ ({frac(b[1])} : ℝ)'
    text,count=re.subn(pattern,lambda m:m.group(1)+statement+m.group(2),text,count=1,flags=re.S)
    assert count==1,(theorem,count)
for name,b in entropy_bounds.items():
    theorem=name+'_bounds'
    pattern=r'(theorem '+re.escape(theorem)+r'\s*:\s*).*?( := by)'
    statement=f'({frac(b[0])} : ℝ) ≤ {name} ∧ {name} ≤ ({frac(b[1])} : ℝ)'
    text,count=re.subn(pattern,lambda m:m.group(1)+statement+m.group(2),text,count=1,flags=re.S)
    assert count==1,(theorem,count)

certificate=F(3840559,2000000) # 1.9202795
target=F(48007,25000)         # 1.92028
text=text.replace('def certificateExponent : ℝ := 192029 / 100000',
                  f'def certificateExponent : ℝ := {frac(certificate)}')
text=text.replace('def targetExponent : ℝ := 19203 / 10000',
                  f'def targetExponent : ℝ := {frac(target)}')
text=text.replace('targetExponent - certificateExponent = (1 / 100000 : ℝ)',
                  f'targetExponent - certificateExponent = ({frac(target-certificate)} : ℝ)')

H,Ha,G,B,Q=[entropy_bounds[n] for n in ['Hpi','Halpha','partitionEntropy','bankEntropy','queryEntropy']]
# Independent interval envelope, in exactly the directions used by the source proof.
ledger_upper=[2*B[1]/H[0],2-G[0]/H[1]+2*Q[1]/H[0],2*Ha[1]/H[0],1+G[1]/H[0],2-G[0]/H[1],F(1)]
assert all(v<certificate for v in ledger_upper)
# Check the linarith cross-multiplied proof, which treats H in the query numerator
# and denominator as one variable and moves (2-certificate) H to the left.
cross_slack=[certificate*H[0]-2*B[1],
             G[0]-2*Q[1]-(2-certificate)*H[1],
             certificate*H[0]-2*Ha[1],
             (certificate-1)*H[0]-G[1],
             G[0]-(2-certificate)*H[1]]
assert all(s>0 for s in cross_slack)

OUT.mkdir(parents=True, exist_ok=True)
(OUT/'TernaryParameters.lean').write_text(text)
report={
    'method':'Exact rational atanh series with absolute geometric remainder, N=16',
    'status':'Rational arithmetic independently checked. Lean compilation still required.',
    'source_commit':'4a4a98e6eca4fc16817f0d2074026fdaece52efd',
    'log_bounds':{k:[str(v[0]),str(v[1])] for k,v in log_bounds.items()},
    'entropy_bounds':{k:[str(v[0]),str(v[1])] for k,v in entropy_bounds.items()},
    'certificate':str(certificate),'target':str(target),
    'ledger_upper':[str(v) for v in ledger_upper],
    'ledger_upper_decimal':[float(v) for v in ledger_upper],
    'cross_multiplication_slack':[str(v) for v in cross_slack],
}
(OUT/'rational_certificate.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:report[k] for k in ['status','entropy_bounds','certificate','target','ledger_upper_decimal']},indent=2))
