# Numerical refinement and reproduction

The current target is the exact rational `4800699/2500000 = 1.9202796`.
The full Lean source at the repository root already includes this refinement.
These files make its eleven-file change and numerical certificates reviewable.

| File | Purpose |
|---|---|
| `rational_certificate_refined.json` | Exact logarithm and entropy endpoints, cost bounds, and runtime margins |
| `verify_certificate.py` | Independent exact-arithmetic checker reading actual Lean declarations |
| `target_19202796.patch` | Complete patch against upstream commit `4a4a98e6eca4fc16817f0d2074026fdaece52efd` |
| `candidate_refined_manifest.json` | SHA-256 hashes of the eleven original and modified Lean files |
| `strengthen_parameters.py` | Derives outward-rounded bounds using rational series enclosures |
| `build_candidate.py` | Constructs the intermediate 1.92028 candidate from pristine upstream source |
| `build_refined_candidate.py` | Tightens that intermediate candidate to the final 1.9202796 target |
| `build_parallel.py` | Runs the pinned full-source build with an explicit worker count and immutable-source checks |

## Check the included source

Run from the repository root:

```bash
python3 refinement/verify_certificate.py \
  --certificate refinement/rational_certificate_refined.json \
  --parameters Submission/ThreeSum/TernaryParameters.lean \
  --runtime-root .
```

The checker uses Python's `Fraction` for every pass/fail comparison, checks the
coarser remainder supplied by the actual Mathlib theorem, and does not import
the generation scripts. Its JSON output records the actual files it read.
Exact arithmetic passing does not check the full Lean proof. Full build and
axiom-audit commands are in the repository's root README.

## Regenerate from pristine upstream

Use a separate checkout of the pinned predecessor. Do not apply the generator
to the already refined source at this repository's root. From this repository's
root, with writable sibling directories available:

```bash
git clone https://github.com/fringewidth/three-sum-lean.git ../three-sum-upstream
git -C ../three-sum-upstream checkout --detach 4a4a98e6eca4fc16817f0d2074026fdaece52efd

python3 refinement/build_candidate.py \
  --source ../three-sum-upstream \
  --output ../three-sum-generated

python3 refinement/build_refined_candidate.py \
  --source ../three-sum-upstream \
  --output ../three-sum-generated

python3 refinement/verify_certificate.py \
  --certificate ../three-sum-generated/rational_certificate_refined.json \
  --parameters ../three-sum-generated/candidate_refined/Submission/ThreeSum/TernaryParameters.lean \
  --runtime-root ../three-sum-generated/candidate_refined
```

`build_candidate.py` calls `strengthen_parameters.py` and produces the first
candidate plus its metadata. `build_refined_candidate.py` consumes those files
and writes the final patch, manifest, certificate, and eleven modified source
files under `candidate_refined/`. Both commands leave the pristine input
checkout unchanged. The intermediate 1.92028 files are generation inputs, not
the final target distributed here.

The JSON certificate's generation-time status describes the scope of the
generator. The outcome of the full Lean check belongs to the corresponding
source-hashed build and audit receipts, not to this arithmetic certificate.
