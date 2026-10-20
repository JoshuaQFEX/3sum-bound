"""Prepare changed source files for an exact 1.92028 target, without touching baseline."""
from fractions import Fraction as F
from pathlib import Path
import argparse
import difflib
import hashlib
import json
import re
import runpy

SCRIPT_DIR=Path(__file__).resolve().parent
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--source',type=Path,default=SCRIPT_DIR.parent/'three_sum_source',
                    help='Pristine checkout of source commit 4a4a98e6eca4fc16817f0d2074026fdaece52efd.')
parser.add_argument('--output',type=Path,default=SCRIPT_DIR,
                    help='Directory for candidate source, patch, and exact rational certificate.')
args=parser.parse_args()
HERE=args.output.resolve()
SOURCE=args.source.resolve()
CANDIDATE=HERE/'candidate'
runpy.run_path(str(SCRIPT_DIR/'strengthen_parameters.py'))

def edit(path, replacements):
    old=(SOURCE/path).read_text()
    new=old
    for a,b in replacements:
        assert a in new,(path,a)
        new=new.replace(a,b)
    assert new!=old,path
    return old,new

changes={}
path='Submission/ThreeSum/TernaryParameters.lean'
changes[path]=((SOURCE/path).read_text(),(HERE/'TernaryParameters.lean').read_text())

changes['Submission/ThreeSum/TernaryOversizeRates.lean']=edit('Submission/ThreeSum/TernaryOversizeRates.lean',[
    ('def softCertificate : ℝ := 1920291/1000000','def softCertificate : ℝ := 19202797/10000000'),
    ('(1/1000000 : ℝ)','(1/5000000 : ℝ)'),
    ('targetExponent-softCertificate=(9/1000000 : ℝ)','targetExponent-softCertificate=(3/10000000 : ℝ)'),
])
changes['Submission/ThreeSum/TernaryOversizeOverhead.lean']=edit('Submission/ThreeSum/TernaryOversizeOverhead.lean',[
    ('microAllowance K < (1/1000000 : ℝ)','microAllowance K < (1/100000000 : ℝ)'),
])
changes['Submission/ThreeSum/TernaryCountFrontendBudget.lean']=edit('Submission/ThreeSum/TernaryCountFrontendBudget.lean',[
    ('def frontendExponent : ℝ :=1920293/1000000','def frontendExponent : ℝ :=19202798/10000000'),
    ('targetExponent-frontendExponent=(7/1000000 : ℝ)','targetExponent-frontendExponent=(1/5000000 : ℝ)'),
    ('microAllowance K<(1/1000000 : ℝ)','microAllowance K<(1/100000000 : ℝ)'),
])
changes['Submission/ThreeSum/TernaryActualPrefixRuntime.lean']=edit('Submission/ThreeSum/TernaryActualPrefixRuntime.lean',[
    ('microAllowance K<(1/1000000:ℝ)','microAllowance K<(1/100000000:ℝ)'),
])
changes['Submission/ThreeSum/TernaryActualRuntimeParameters.lean']=edit('Submission/ThreeSum/TernaryActualRuntimeParameters.lean',[
    ('(1/1000000:ℝ)','(1/100000000:ℝ)'),
])
changes['Submission/ThreeSum/TernaryActualColoredRuntime.lean']=edit('Submission/ThreeSum/TernaryActualColoredRuntime.lean',[
    ('def exponent : ℝ :=1920295/1000000','def exponent : ℝ :=19202799/10000000'),
    ('microAllowance K<(1/1000000:ℝ)','microAllowance K<(1/100000000:ℝ)'),
])
for path in ['Submission/ThreeSum/TernaryProfileRuntime.lean','Submission/ThreeSum/TernarySolverEndBridge.lean']:
    changes[path]=edit(path,[('19203/10000','48007/25000')])
changes['Submission/ThreeSum/TernaryFinalSolver.lean']=edit('Submission/ThreeSum/TernaryFinalSolver.lean',[
    ('exponent19203/10000','exponent 48007/25000'),
    ('solvedInTime_19203_10000','solvedInTime_48007_25000'),
    ('19203/10000','48007/25000'),
])
changes['Submission.lean']=edit('Submission.lean',[
    ('((19203 : Rat) / 10000)','((48007 : Rat) / 25000)'),
    ('ThreeSum.solvedInTime_19203_10000','ThreeSum.solvedInTime_48007_25000'),
])

# Arithmetic obligations used by all changed margin lemmas.
cert=F(3840559,2000000)
soft=F(19202797,10000000)
frontend=F(19202798,10000000)
color=F(19202799,10000000)
target=F(48007,25000)
Kmin=10**8
mu=F(1,100*Kmin**2)
micro_bound=F(1,10**8)
assert F(8,Kmin) < soft-cert
assert F(10,Kmin) < soft-cert
assert soft-cert==F(1,5000000)
assert target-cert==F(1,2000000)
assert target-soft==F(3,10000000)
assert target-frontend==F(1,5000000)
assert mu < micro_bound
assert soft+micro_bound < frontend
assert frontend+micro_bound < color
assert frontend+2*micro_bound < target
assert color < target

diff=[]
manifest=[]
for path,(old,new) in changes.items():
    out=CANDIDATE/path
    out.parent.mkdir(parents=True,exist_ok=True)
    out.write_text(new)
    diff.extend(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
    manifest.append({'path':path,'baseline_sha256':hashlib.sha256(old.encode()).hexdigest(),'candidate_sha256':hashlib.sha256(new.encode()).hexdigest()})
(HERE/'target_192028.patch').write_text(''.join(diff))
(HERE/'candidate_manifest.json').write_text(json.dumps({'baseline':'4a4a98e6eca4fc16817f0d2074026fdaece52efd','files':manifest},indent=2)+'\n')

print(f'Prepared {len(changes)} changed Lean files at {CANDIDATE}; exact rational margin checks passed.')
