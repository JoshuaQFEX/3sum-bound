"""Refine the already prepared 1.92028 proof to the exact target 1.9202796.

This changes only certified rational bounds, maintaining the baseline schedule
and K >= 10^8. The source remains a candidate until the complete Lean rebuild.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse
import difflib
import hashlib
import json

SCRIPT_DIR=Path(__file__).resolve().parent
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--source',type=Path,default=SCRIPT_DIR.parent/'three_sum_source',
                    help='Pristine checkout of source commit 4a4a98e6eca4fc16817f0d2074026fdaece52efd.')
parser.add_argument('--output',type=Path,default=SCRIPT_DIR,
                    help='Directory containing the first candidate, where refined output is written.')
args=parser.parse_args()
HERE=args.output.resolve()
SOURCE=args.source.resolve()
CANDIDATE=HERE/'candidate_refined'
base=HERE/'candidate'
manifest=json.loads((HERE/'candidate_manifest.json').read_text())
report=json.loads((HERE/'rational_certificate.json').read_text())

cert=F(96013973,50000000)
soft=F(192027957,100000000)
frontend=F(96013979,50000000)
color=F(192027959,100000000)
target=F(4800699,2500000)
Kmin=10**8
mu=F(1,100*Kmin**2)
micro_bound=F(1,10**8)
assert F(8,Kmin) < soft-cert
assert F(10,Kmin) < soft-cert
assert soft-cert==F(11,100000000)
assert target-cert==F(7,50000000)
assert target-soft==F(3,100000000)
assert target-frontend==F(1,50000000)
assert mu < micro_bound
# The strict actual micro inequality suffices when these closed gaps equal it.
assert soft+micro_bound <= frontend
assert frontend+micro_bound <= color
assert frontend+2*micro_bound <= target
assert color < target

entropy={k:tuple(map(F,v)) for k,v in report['entropy_bounds'].items()}
H,Ha,G,B,Q=[entropy[n] for n in ['Hpi','Halpha','partitionEntropy','bankEntropy','queryEntropy']]
ledger=list(map(F,report['ledger_upper']))
assert all(v<cert for v in ledger)
cross_slack=[cert*H[0]-2*B[1],G[0]-2*Q[1]-(2-cert)*H[1],
             cert*H[0]-2*Ha[1],(cert-1)*H[0]-G[1],G[0]-(2-cert)*H[1]]
assert all(s>0 for s in cross_slack)

replacement={
 'Submission/ThreeSum/TernaryParameters.lean':[
  ('def certificateExponent : ℝ := 3840559 / 2000000','def certificateExponent : ℝ := 96013973 / 50000000'),
  ('def targetExponent : ℝ := 48007 / 25000','def targetExponent : ℝ := 4800699 / 2500000'),
  ('targetExponent - certificateExponent = (1 / 2000000 : ℝ)','targetExponent - certificateExponent = (7 / 50000000 : ℝ)'),
 ],
 'Submission/ThreeSum/TernaryOversizeRates.lean':[
  ('def softCertificate : ℝ := 19202797/10000000','def softCertificate : ℝ := 192027957/100000000'),
  ('(1/5000000 : ℝ)','(11/100000000 : ℝ)'),
  ('targetExponent-softCertificate=(3/10000000 : ℝ)','targetExponent-softCertificate=(3/100000000 : ℝ)'),
 ],
 'Submission/ThreeSum/TernaryCountFrontendBudget.lean':[
  ('def frontendExponent : ℝ :=19202798/10000000','def frontendExponent : ℝ :=96013979/50000000'),
  ('targetExponent-frontendExponent=(1/5000000 : ℝ)','targetExponent-frontendExponent=(1/50000000 : ℝ)'),
 ],
 'Submission/ThreeSum/TernaryActualColoredRuntime.lean':[
  ('def exponent : ℝ :=19202799/10000000','def exponent : ℝ :=192027959/100000000'),
 ],
 'Submission/ThreeSum/TernaryProfileRuntime.lean':[
  ('48007/25000','4800699/2500000'),
 ],
 'Submission/ThreeSum/TernarySolverEndBridge.lean':[
  ('48007/25000','4800699/2500000'),
 ],
 'Submission/ThreeSum/TernaryFinalSolver.lean':[
  ('solvedInTime_48007_25000','solvedInTime_4800699_2500000'),
  ('48007/25000','4800699/2500000'),
 ],
 'Submission.lean':[
  ('((48007 : Rat) / 25000)','((4800699 : Rat) / 2500000)'),
  ('ThreeSum.solvedInTime_48007_25000','ThreeSum.solvedInTime_4800699_2500000'),
 ],
}
diff=[]
files=[]
for item in manifest['files']:
 path=item['path']; old=(SOURCE/path).read_text(); new=(base/path).read_text()
 for a,b in replacement.get(path,[]):
  assert a in new,(path,a)
  new=new.replace(a,b)
 out=CANDIDATE/path
 out.parent.mkdir(parents=True,exist_ok=True)
 out.write_text(new)
 diff.extend(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
 files.append({'path':path,'baseline_sha256':hashlib.sha256(old.encode()).hexdigest(),'candidate_sha256':hashlib.sha256(new.encode()).hexdigest()})
(HERE/'target_19202796.patch').write_text(''.join(diff))
(HERE/'candidate_refined_manifest.json').write_text(json.dumps({'baseline':manifest['baseline'],'files':files},indent=2)+'\n')
report['certificate']=str(cert)
report['target']=str(target)
report['cross_multiplication_slack']=[str(s) for s in cross_slack]
report['runtime_margins']={
 'soft':str(soft),'frontend':str(frontend),'colored':str(color),
 'K_min':Kmin,'micro_max':str(mu),'micro_bound':str(micro_bound),
 'soft_minus_certificate':str(soft-cert),'target_minus_certificate':str(target-cert),
 'target_minus_soft':str(target-soft),'target_minus_frontend':str(target-frontend),
 'target_minus_colored':str(target-color),
 'largest_ledger_to_certificate_gap':str(cert-max(ledger)),
}
(HERE/'rational_certificate_refined.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'files':len(files),'certificate':str(cert),'target':str(target),
                  'ledger_max_upper':float(max(ledger)),'certificate_gap':float(cert-max(ledger)),
                  'runtime_margins':report['runtime_margins']},indent=2))
