# Deterministic 3SUM: refined exponent 1.9202796

This repository refines the numerical certificates in the published ternary
3SUM formalization to export the exact rational target
**4800699/2500000 = 1.9202796**, below the predecessor's **1.9203** bound.
The construction, probability profile, machine model, and original formalization
are inherited. The change tightens logarithm and entropy estimates and the
strict margins in the existing runtime proof.

The entry point in [Submission.lean](Submission.lean) is:

```lean
theorem Race.bound :
    EndStatement.ThreeSum.SolvedInTime ((4800699 : Rat) / 2500000) := by
  exact ThreeSum.solvedInTime_4800699_2500000
```

**Verification status: the independent exact-arithmetic checks and the early
Lean check of the numerical parameter module passed. The complete frozen-source
Lean build and subsequent full-source axiom audit are still pending.** The
publication's final verification records will establish their outcomes. This
repository does not yet claim a new successful full Lean check or official
leaderboard acceptance.

## Result and scope

The [benchmark statement](Submission/EndStatement.lean) asks whether three
distinct input positions have values summing to zero. Equal values at different
positions are allowed. For each fixed polynomial magnitude bound on the input
integers, the theorem supplies a single finite deterministic word-RAM program,
independent of input size and admissible word width, with the required
correctness and asymptotic running-time bound. The intended conclusion is
`O(n^1.9202796)` in that model.

This is an asymptotic refinement. It does not provide a practical crossover
size or a measured implementation speedup. The exponent decreases by exactly
0.0000204 from 1.9203.

The full proof is in
[TernaryFinalSolver.lean](Submission/ThreeSum/TernaryFinalSolver.lean).
The [proof note](docs/three_sum_bound_note.tex) explains the exact inequalities,
the retained runtime margins, and the scope of the result. The
[numerical certificate](refinement/rational_certificate_refined.json) records
exact rational endpoints and positive residuals.

## What changes

The source starts at
[`fringewidth/three-sum-lean`, commit `4a4a98e6eca4fc16817f0d2074026fdaece52efd`](https://github.com/fringewidth/three-sum-lean/tree/4a4a98e6eca4fc16817f0d2074026fdaece52efd).
Eleven Lean files change; the complete diff is
[target_19202796.patch](refinement/target_19202796.patch), with before-and-after
hashes in the [change manifest](refinement/candidate_refined_manifest.json).

The logarithm estimates use 16 rational series terms with the exact remainder
available from Mathlib's `Real.sum_range_sub_log_div_le`. They imply these
inclusive entropy intervals:

| Quantity in `TernaryParameters` | Lower endpoint | Upper endpoint |
|---|---:|---:|
| `Hpi` | 0.81463563795 | 0.81463563796 |
| `Halpha` | 0.51142981001 | 0.51142981003 |
| `partitionEntropy` | 0.20511813944 | 0.20511813945 |
| `bankEntropy` | 0.78216403986 | 0.78216403988 |
| `queryEntropy` | 0.07008744368 | 0.07008744369 |

The largest certified principal cost is the bank term, bounded above by
`156432807976/81463563795`, which is strictly below 1.92027946. The proof then
uses the following successive exponents:

| Stage | Exact exponent |
|---|---:|
| Principal cost certificate | 1.92027946 |
| Finite-block certificate | 1.92027957 |
| Frontend budget | 1.92027958 |
| Executed colored solver | 1.92027959 |
| Exported benchmark target | 1.92027960 |

The existing choice `K >= 10^8` gives `10/K <= 10^-7`, strictly smaller than
the first gap of `1.1 * 10^-7`. The separate allowance `1/(100 K^2)` is at
most `10^-18`, below the later `10^-8` gaps. The final strict gap absorbs the
arbitrarily small positive slack permitted by the existing `PowerBound`
runtime statement.

## Reproduction

Use **Lean `leanprover/lean4:v4.33.1`** and **Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`**, as recorded in the unchanged
`lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`. Python 3 is required
for the verification helpers; the rational checker uses only the standard
library.

Run the following commands from the repository root after installing the
pinned Lean toolchain:

```bash
python3 - <<'PY'
from pathlib import Path
import subprocess
roots = Path('scripts/mathlib-cache-roots.txt').read_text().split()
subprocess.run(['lake', 'exe', 'cache', 'get', *roots], check=True)
PY

python3 refinement/verify_certificate.py \
  --certificate refinement/rational_certificate_refined.json \
  --parameters Submission/ThreeSum/TernaryParameters.lean \
  --runtime-root .

python3 refinement/build_parallel.py --aggregate --threads 4
python3 scripts/audit_axioms.py
```

The exact-arithmetic checker reads the actual Lean declarations and separately
checks 13 direct logarithm enclosures, nine normalized-log identities and
bounds, five entropy intervals, all six principal costs, the cross-multiplication
residuals, and the runtime margin chain. **It does not check the full Lean
proof.**

The full-build helper checks every submitted module against the explicit
source plan, records input hashes, and rejects source changes during checking.
The audit then examines all submitted declarations, rejects submitted axioms,
and permits only `propext`, `Classical.choice`, and `Quot.sound` as transitive
axioms. Both helpers write fresh local records under `verification/builds/`.
Full Lean checking and an official hosted verification are separate checks.

The [refinement instructions](refinement/README.md) also explain how to
regenerate the patch and certificates from the pristine upstream revision.

## Files and verification history

| Path | Purpose |
|---|---|
| `Submission.lean`, `Submission/` | Complete Lean source and exported theorem |
| `refinement/` | Exact certificate, independent checker, generation scripts, patch, and changed-file hashes |
| `docs/three_sum_bound_note.tex` | Mathematical note for the refined exponent |
| `docs/UPSTREAM_README.md` | Predecessor README, preserved verbatim |
| `scripts/` | Inherited full-source build plan and axiom-audit tools |
| `.github/workflows/verify.yml` | Pinned CI workflow for the full source build, axiom audit, and retained logs |
| `verification/receipts/lean-1.921-20261015/` | Preserved historical verification records for the earlier 1.921 source |
| `docs/upstream-workflows/` | Historical CI workflow, kept as an inactive reference |

The inherited `VERIFICATION.md`, `REPRODUCTION.md`, `SOURCE_MANIFEST.json`, and
historical receipt directory describe earlier revisions. They are retained for
provenance; their hashes and success claims do not certify this refinement.
The current changed-file manifest is under `refinement/`. Final current-source
build and audit receipts will be added after those checks finish.

The [verification workflow](.github/workflows/verify.yml) runs on source changes
and supports manual dispatch. It checks all 1,198 planned modules, runs the
full-source axiom audit, and retains the actual outcomes, receipts, and logs as
a GitHub Actions artifact. It restores the pinned Mathlib cache and compiles
the submitted project from source. The predecessor's workflow is preserved
separately under [`docs/upstream-workflows/`](docs/upstream-workflows/README.md).

## Attribution and license

The algorithmic construction and original full formalization are due to
[c0ldzy17](https://github.com/c0ldzy17/three-sum-lean) and the authors credited
in [METHOD.md](METHOD.md) and [NOTICE](NOTICE). Hrishik Sai Bojnal
([fringewidth](https://github.com/fringewidth/three-sum-lean)) published the
preceding exponent-margin refinement to 1.9203. This repository contributes
the tighter numerical certificates, margin adjustments, and accompanying
checks described above.

The inherited work credits Josh Alman and Virginia Vassilevska Williams;
Björklund, Husfeldt, Kaski, and Koivisto; and Swapnil Jain. The benchmark
statement, word-RAM program logic, and compiler originate in Anthropic's
formalization through the source lineage recorded in `NOTICE`. Lean, Mathlib,
and their dependencies provide the proof infrastructure. Existing copyright
notices, [LICENSE](LICENSE), and [NOTICE](NOTICE) are preserved.

Problem and leaderboard: [Big O Speedrun — 3SUM](https://bigospeedrun.com/3sum).
