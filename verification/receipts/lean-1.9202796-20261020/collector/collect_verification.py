#!/usr/bin/env python3
"""Collect successful 3SUM verification evidence without running Lean.

By default this performs a read-only check and prints proposed verification.json.
--stage additionally copies the two successful receipt sets and a fresh rational
check into the destination, then writes verification.json. No output is staged
unless every gate passes. Existing verification.json or receipt directories
are never replaced. This checks recorded evidence and file hashes; it does not
compile Lean, authenticate CI, or establish hosted benchmark acceptance.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import tempfile

BASE_COMMIT = "4a4a98e6eca4fc16817f0d2074026fdaece52efd"
BASE_REPOSITORY = "https://github.com/fringewidth/three-sum-lean"
TARGET_NUMERATOR = 4800699
TARGET_DENOMINATOR = 2500000
MODULE_COUNT = 1198
ALLOWED_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
PINS = {
    "lean-toolchain": "3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71",
    "lakefile.toml": "5ad072c0aca3c7ab777a99938f583ef92bc121101917b7818b5f53f1a384b08c",
    "lake-manifest.json": "484af05025301c3920dfeb644f6dbb7f02b05f596bf48831c9324e383694db25",
    "scripts/source-chains.json": "ee97a6c83f9dddcd5e63af28cfdf4f808b0db34db39d57fd374d492620841837",
}
AUDIT_BODY = """open Lean Elab Command

set_option maxHeartbeats 0

run_cmd do
  let env := (← getEnv).setExporting false
  let moduleNames := env.header.moduleNames
  let allowed : Array Name := #[\u0060propext, \u0060Classical.choice, \u0060Quot.sound]
  let mut submitted : Array Name := #[]
  for (decl, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? decl | continue
    let origin := moduleNames[idx]!
    if (\u0060Submission).isPrefixOf origin then
      match info with
      | .axiomInfo _ => throwError "Submitted axiom declaration: {decl}"
      | _ => pure ()
      submitted := submitted.push decl
  if submitted.isEmpty then
    throwError "No submitted declarations were audited"
  for decl in submitted do
    let axioms ← collectAxioms decl
    let forbidden := axioms.filter fun ax => !allowed.contains ax
    unless forbidden.isEmpty do
      throwError "Forbidden transitive axioms in {decl}: {forbidden}"
  let some bound := env.find? \u0060Race.bound | throwError "Missing Race.bound"
  let boundAxioms ← collectAxioms \u0060Race.bound
  logInfo m!"RACE_BOUND_TYPE {bound.type}"
  logInfo m!"RACE_BOUND_AXIOMS {boundAxioms}"
  logInfo m!"FULL_SOURCE_AXIOM_AUDIT PASS {submitted.size} declarations"
"""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical(data: object) -> bytes:
    return json.dumps(data, sort_keys=True, separators=(",", ":")).encode("utf-8")


def regular_bytes(path: Path) -> bytes:
    require(path.is_file() and not path.is_symlink(), f"Missing or non-regular file: {path}")
    return path.read_bytes()


def record_at(path: Path) -> tuple[dict, bytes]:
    raw = regular_bytes(path)
    data = json.loads(raw)
    require(isinstance(data, dict), f"Record is not an object: {path}")
    require(data.get("status") == "succeeded", f"Record has not succeeded: {path}")
    require(type(data.get("exit_code")) is int and data["exit_code"] == 0,
            f"Record has no successful exit code: {path}")
    require(data.get("provisional") is False, f"Record is provisional or unspecified: {path}")
    require(type(data.get("toolchain_exit_code")) is int and data["toolchain_exit_code"] == 0,
            f"Toolchain check did not succeed: {path}")
    require(re.search(r"\bLean \(version 4\.33\.1[, )]", data.get("toolchain_output", "")) is not None,
            f"Record does not report Lean 4.33.1: {path}")
    require(type(data.get("module_count")) is int and data["module_count"] == MODULE_COUNT,
            f"Record does not cover {MODULE_COUNT} modules: {path}")
    require(isinstance(data.get("source_sha256"), dict), f"Missing source hashes: {path}")
    return data, raw


def stamp(value: str) -> datetime:
    require(isinstance(value, str), "Missing verification timestamp")
    if re.fullmatch(r"\d{8}T\d{6}\.\d+Z", value):
        return datetime.strptime(value, "%Y%m%dT%H%M%S.%fZ").replace(tzinfo=timezone.utc)
    result = datetime.fromisoformat(value.replace("Z", "+00:00"))
    require(result.tzinfo is not None, "Verification timestamp has no timezone")
    return result


def source_snapshot(root: Path) -> dict[str, str]:
    require((root / "Submission").is_dir(), f"Missing Submission directory: {root}")
    files = sorted((root / "Submission").rglob("*.lean")) + [root / "Submission.lean"]
    result = {}
    for path in files:
        name = path.relative_to(root).as_posix()
        require(re.fullmatch(r"Submission(?:/[A-Za-z_][A-Za-z_0-9]*)*\.lean", name) is not None,
                f"Unexpected submitted module path: {name}")
        result[name] = sha256(regular_bytes(path))
    require(len(result) == MODULE_COUNT, f"Expected {MODULE_COUNT} submitted modules in {root}")
    return dict(sorted(result.items()))


def safe_log_path(parent: Path, name: str) -> Path:
    require(isinstance(name, str) and name not in ("", ".", ".."), "Invalid receipt filename")
    require(PurePosixPath(name).name == name and "/" not in name and "\\" not in name,
            f"Receipt log path is not a plain filename: {name!r}")
    return parent / name


def git_commit_matches(root: Path, commit: str, names: list[str]) -> None:
    require(re.fullmatch(r"[0-9a-f]{40}", commit) is not None, "Verified commit must be a full 40-digit SHA")
    run = subprocess.run(["git", "-C", str(root), "ls-tree", "-r", "-z", "--full-tree", commit],
                         capture_output=True, check=False)
    require(run.returncode == 0, "Cannot read the supplied verified commit from source-root")
    entries = {}
    for row in run.stdout.split(b"\0"):
        if not row:
            continue
        prefix, path = row.split(b"\t", 1)
        mode, kind, blob = prefix.split()
        entries[path.decode("utf-8")] = (mode.decode(), kind.decode(), blob.decode())
    for name in names:
        content = regular_bytes(root / name)
        expected = hashlib.sha1(b"blob " + str(len(content)).encode() + b"\0" + content).hexdigest()
        require(name in entries and entries[name][1:] == ("blob", expected),
                f"Verified commit does not contain the checked bytes: {name}")


def collect(args: argparse.Namespace) -> tuple[dict, dict[str, bytes], str]:
    source = args.source_root.resolve()
    destination = args.destination_root.resolve()
    receipt_origin = getattr(args, "receipt_origin", "local")
    require(receipt_origin in ("local", "ci"), "Receipt origin must be local or ci")
    collector_path = Path(__file__).resolve()
    collector_raw = regular_bytes(collector_path)
    require(source.is_dir() and destination.is_dir(), "Source and destination roots must exist")
    require(not (source / "lakefile.lean").exists() and not (destination / "lakefile.lean").exists(),
            "Unexpected lakefile.lean alongside pinned lakefile.toml")
    build_path = args.build_record.resolve()
    audit_path = args.audit_record.resolve()
    build, build_raw = record_at(build_path)
    audit, audit_raw = record_at(audit_path)

    for key in ("all_chains_built_in_this_invocation", "all_modules_built_in_this_invocation",
                "source_inputs_unchanged_at_finish"):
        require(build.get(key) is True, f"Build does not certify {key}")
    require(type(build.get("start_at")) is int and build["start_at"] == 0,
            "Build skips part of the source plan")
    require(build.get("required_sha256") == PINS and build.get("observed_sha256") == PINS,
            "Build's required/observed dependency pins differ from the reviewed pins")
    for name, expected in PINS.items():
        require(sha256(regular_bytes(source / name)) == expected, f"Source pin mismatch: {name}")
        require(sha256(regular_bytes(destination / name)) == expected, f"Publication pin mismatch: {name}")

    source_hashes = source_snapshot(source)
    require(build["source_sha256"] == source_hashes, "Build source hashes differ from current source")
    require(audit["source_sha256"] == source_hashes, "Audit source hashes differ from current source")
    require(source_snapshot(destination) == source_hashes, "Publication source differs from checked source")
    source_digest = sha256(canonical(source_hashes))
    chains = json.loads(regular_bytes(source / "scripts/source-chains.json"))
    require(isinstance(chains, list) and all(isinstance(c, list) and c for c in chains),
            "Invalid source plan")
    modules = [m for c in chains for m in c]
    require(len(modules) == len(set(modules)) == MODULE_COUNT,
            "Source plan contains missing or duplicate modules")
    planned_paths = {m.replace(".", "/") + ".lean" for m in modules}
    require(planned_paths == set(source_hashes), "Source plan and submitted files differ")
    require(build.get("chain_count") == len(chains), "Build chain count differs from the plan")
    require(type(build.get("lean_num_threads")) is int and build["lean_num_threads"] > 0,
            "Build does not record a positive worker count")
    invocations = build.get("chains")
    require(isinstance(invocations, list) and invocations, "Build has no invocation records")
    mode = build.get("validation_method")
    if mode == "aggregate_explicit_modules":
        expected_commands = [["lake", "build", *["+" + m for m in modules]]]
    elif mode == "serial_chain_endpoints":
        expected_commands = [["lake", "build", c[-1]] for c in chains]
    else:
        raise ValueError("Unsupported or missing full-source build validation method")
    require([x.get("command") for x in invocations] == expected_commands,
            "Recorded build commands do not cover the reviewed complete plan")

    build_start = stamp(build.get("started_utc"))
    build_finish = stamp(build.get("finished_utc"))
    audit_start = stamp(audit.get("started_utc"))
    audit_finish = stamp(audit.get("finished_utc"))
    require(build_start <= build_finish <= audit_start <= audit_finish,
            "Full-source audit did not run after the successful complete build")
    receipts = {"build/results.json": build_raw, "audit/results.json": audit_raw}
    for category, record, path in (("build", build, build_path), ("audit", audit, audit_path)):
        toolchain = regular_bytes(path.parent / "toolchain.log")
        require(toolchain.decode("utf-8").strip() == record.get("toolchain_output", "").strip(),
                f"{category} toolchain log differs from the record")
        receipts[f"{category}/toolchain.log"] = toolchain
    for item in invocations:
        require(item.get("status") == "succeeded" and type(item.get("exit_code")) is int
                and item["exit_code"] == 0, "A recorded build invocation did not succeed")
        path = safe_log_path(build_path.parent, item.get("log"))
        content = regular_bytes(path)
        require(sha256(content) == item.get("log_sha256"), f"Build log hash mismatch: {path.name}")
        require(f"build/{path.name}" not in receipts, "Repeated build log filename")
        receipts[f"build/{path.name}"] = content

    audit_source = regular_bytes(audit_path.parent / "FullSourceAxioms.lean")
    ordered_modules = [".".join(Path(p).with_suffix("").parts)
                       for p in sorted(source_hashes) if p != "Submission.lean"] + ["Submission"]
    expected_audit = ("\n".join("import " + m for m in ordered_modules) + "\nimport Lean\n\n"
                      + AUDIT_BODY).encode("utf-8")
    require(audit_source == expected_audit, "Generated audit source differs from the full-source axiom policy")
    require(sha256(audit_source) == audit.get("audit_source_sha256"), "Audit source hash mismatch")
    require(isinstance(audit.get("command"), list) and audit["command"][:-1]
            == ["lake", "env", "lean", "-j1", "-DautoImplicit=false"],
            "Audit command does not use the reviewed single-threaded collector")
    require(Path(audit["command"][-1]).name == "FullSourceAxioms.lean", "Unexpected audit command target")
    audit_log = regular_bytes(audit_path.parent / "audit.log")
    require(sha256(audit_log) == audit.get("log_sha256"), "Audit log hash mismatch")
    log = audit_log.decode("utf-8")
    types = re.findall(r"RACE_BOUND_TYPE\s+([^\r\n]+)", log)
    require(len(types) == 1 and re.fullmatch(
        r"EndStatement\.ThreeSum\.SolvedInTime\s+\(\s*4800699\s*/\s*2500000\s*\)", types[0].strip()),
        "Audit did not report the exact refined theorem type")
    axiom_reports = re.findall(r"RACE_BOUND_AXIOMS\s+\[([^\]]*)\]", log)
    require(len(axiom_reports) == 1, "Missing or ambiguous exported-theorem axiom report")
    axioms = [x.strip() for x in axiom_reports[0].split(",") if x.strip()]
    require(len(axioms) == len(set(axioms)) and set(axioms) == set(ALLOWED_AXIOMS),
            "Exported theorem has unexpected axioms")
    counts = re.findall(r"FULL_SOURCE_AXIOM_AUDIT PASS (\d+) declarations", log)
    require(len(counts) == 1 and int(counts[0]) > 0, "Missing full-source audit pass marker")
    require("sorryAx" not in log, "Audit log mentions sorryAx")
    receipts["audit/FullSourceAxioms.lean"] = audit_source
    receipts["audit/audit.log"] = audit_log

    manifest_path = destination / "refinement/candidate_refined_manifest.json"
    manifest_raw = regular_bytes(manifest_path)
    manifest = json.loads(manifest_raw)
    require(manifest.get("baseline") == BASE_COMMIT and len(manifest.get("files", [])) == 11,
            "Unexpected baseline or changed-file manifest")
    changed_paths = []
    for item in manifest["files"]:
        path = item.get("path")
        require(path in source_hashes and source_hashes[path] == item.get("candidate_sha256"),
                f"Refined changed-file hash mismatch: {path}")
        changed_paths.append(path)
    require(len(set(changed_paths)) == 11, "Changed-file manifest repeats a path")

    certificate_path = destination / "refinement/rational_certificate_refined.json"
    certificate_raw = regular_bytes(certificate_path)
    certificate = json.loads(certificate_raw)
    require(certificate.get("target") == "4800699/2500000", "Numerical certificate has a different target")
    checker = destination / "refinement/verify_certificate.py"
    checker_raw = regular_bytes(checker)
    check_command = [sys.executable, "refinement/verify_certificate.py",
                     "--certificate", "refinement/rational_certificate_refined.json",
                     "--parameters", "Submission/ThreeSum/TernaryParameters.lean", "--runtime-root", "."]
    checked = subprocess.run(check_command, cwd=destination, capture_output=True, text=True, check=False)
    require(checked.returncode == 0, "Independent rational checker did not pass: " + checked.stderr.strip())
    arithmetic = json.loads(checked.stdout)
    require(arithmetic.get("status") == "pass" and arithmetic.get("final_target") == "4800699/2500000",
            "Independent rational checker returned an unexpected result")
    require(arithmetic.get("certificate_sha256") == sha256(certificate_raw),
            "Independent checker examined a different certificate")
    expected_arithmetic_sources = {str((destination / name).resolve()): source_hashes[name]
                                   for name in changed_paths}
    require(arithmetic.get("source_sha256") == expected_arithmetic_sources,
            "Independent checker did not examine the exact eleven reviewed source files")
    receipts["arithmetic/independent_validation.json"] = checked.stdout.encode("utf-8")
    receipts["collector/collect_verification.py"] = collector_raw

    if args.verified_commit:
        git_commit_matches(source, args.verified_commit, sorted(source_hashes) + sorted(PINS))
    for name in ("LICENSE", "NOTICE"):
        require(regular_bytes(source / name) == regular_bytes(destination / name),
                f"Publication changes inherited {name}")
    require(source_snapshot(source) == source_hashes and source_snapshot(destination) == source_hashes,
            "Source bytes changed during evidence collection")

    name = args.receipt_name or ("lean-1.9202796-" + source_digest[:12])
    require(re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9._-]*", name) is not None,
            "Receipt name must be a plain safe directory name")
    receipt_prefix = "verification/receipts/" + name
    artifact_bytes = {
        "refinement/rational_certificate_refined.json": certificate_raw,
        "refinement/candidate_refined_manifest.json": manifest_raw,
        "refinement/verify_certificate.py": checker_raw,
        "refinement/target_19202796.patch": regular_bytes(destination / "refinement/target_19202796.patch"),
        "refinement/build_parallel.py": regular_bytes(destination / "refinement/build_parallel.py"),
        "scripts/audit_axioms.py": regular_bytes(destination / "scripts/audit_axioms.py"),
        "LICENSE": regular_bytes(destination / "LICENSE"),
        "NOTICE": regular_bytes(destination / "NOTICE"),
    }
    artifact_hashes = {name: sha256(raw) for name, raw in artifact_bytes.items()}
    for name, raw in artifact_bytes.items():
        require(regular_bytes(destination / name) == raw,
                f"Publication verification artifact changed during collection: {name}")
    for name, expected in PINS.items():
        require(sha256(regular_bytes(source / name)) == expected
                and sha256(regular_bytes(destination / name)) == expected,
                f"Pinned input changed during evidence collection: {name}")
    require(regular_bytes(collector_path) == collector_raw,
            "Evidence collector changed while it was running")
    metadata = {
        "schema_version": 1,
        "status": "local_checks_passed" if receipt_origin == "local" else "ci_receipts_checked",
        "verification_basis": {"receipt_origin": receipt_origin,
                               "origin_is_user_supplied": True,
                               "ci_provider_authentication": "not_performed",
                               "ci_run_url_establishes_success": False},
        "problem": "3sum",
        "entry_point": "Race.bound",
        "theorem": "EndStatement.ThreeSum.SolvedInTime ((4800699 : Rat) / 2500000)",
        "exponent": {"numerator": TARGET_NUMERATOR, "denominator": TARGET_DENOMINATOR,
                     "decimal": "1.9202796"},
        "scope": "Successful complete Lean source build, full-source permitted-axiom audit, and exact rational checks. Hosted benchmark and independent Nanoda acceptance are not established.",
        "collected_utc": datetime.now(timezone.utc).isoformat(),
        "upstream": {"repository": BASE_REPOSITORY, "commit": BASE_COMMIT,
                     "construction_credit": "c0ldzy17 and authors in METHOD.md and NOTICE",
                     "prior_margin_refinement_credit": "Hrishik Sai Bojnal (fringewidth)"},
        "source_snapshot": {"module_count": MODULE_COUNT, "manifest_sha256": source_digest,
                            "manifest_encoding": "UTF-8 JSON of the path-to-SHA256 map, sorted keys, separators comma and colon",
                            "manifest_record": receipt_prefix + "/build/results.json",
                            "verified_git_commit": args.verified_commit,
                            "publication_sources_equal_checked_sources": True},
        "toolchain": {"lean": "leanprover/lean4:v4.33.1",
                      "mathlib_commit": "0df444a360eaa60ab8c11dca51a86af692955474",
                      "pinned_input_sha256": PINS},
        "build": {"status": "succeeded", "exit_code": 0, "mode": mode,
                  "worker_count": build.get("lean_num_threads"),
                  "module_count": MODULE_COUNT, "source_inputs_unchanged": True,
                  "started_utc": build["started_utc"], "finished_utc": build["finished_utc"],
                  "record": receipt_prefix + "/build/results.json"},
        "axiom_audit": {"status": "succeeded", "exit_code": 0,
                        "audited_declarations": int(counts[0]), "permitted_axioms": ALLOWED_AXIOMS,
                        "exported_theorem_axioms": axioms,
                        "started_utc": audit["started_utc"], "finished_utc": audit["finished_utc"],
                        "record": receipt_prefix + "/audit/results.json"},
        "exact_arithmetic": {"status": "pass", "scope": arithmetic.get("scope"),
                             "checker_sha256": sha256(checker_raw),
                             "certificate_sha256": sha256(certificate_raw),
                             "record": receipt_prefix + "/arithmetic/independent_validation.json"},
        "external_verification": {"github_actions_run_url": args.ci_run_url,
                                  "run_url_is_user_supplied": bool(args.ci_run_url),
                                  "big_o_speedrun": "not_established",
                                  "independent_nanoda": "not_established"},
        "artifact_sha256": artifact_hashes,
        "receipt_sha256": {receipt_prefix + "/" + path: sha256(raw)
                           for path, raw in sorted(receipts.items())},
        "collector": {"sha256": sha256(collector_raw),
                      "record": receipt_prefix + "/collector/collect_verification.py",
                      "scope": "Validates existing records and source hashes; does not run Lean or authenticate a CI provider."},
    }
    return metadata, receipts, receipt_prefix


def stage(destination: Path, metadata: dict, receipts: dict[str, bytes], prefix: str) -> None:
    destination = destination.resolve()
    final_receipts = destination / prefix
    final_metadata = destination / "verification.json"
    require(not final_metadata.exists(), "Refusing to replace existing verification.json")
    require(not final_receipts.exists(), "Refusing to replace an existing receipt directory")
    final_receipts.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="verification-staging-", dir=destination) as temporary:
        root = Path(temporary)
        staged_receipts = root / "receipts"
        staged_receipts.mkdir()
        for name, raw in receipts.items():
            path = staged_receipts / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(raw)
        staged_metadata = root / "verification.json"
        staged_metadata.write_text(json.dumps(metadata, indent=2) + "\n")
        require(not final_metadata.exists() and not final_receipts.exists(),
                "Publication evidence destination appeared during staging")
        staged_receipts.rename(final_receipts)
        # Hard-link creation is atomic and refuses to replace an existing file.
        os.link(staged_metadata, final_metadata)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", type=Path, required=True)
    parser.add_argument("--destination-root", type=Path, required=True)
    parser.add_argument("--build-record", type=Path, required=True,
                        help="Successful full build's results.json")
    parser.add_argument("--audit-record", type=Path, required=True,
                        help="Successful full-source axiom audit's results.json")
    parser.add_argument("--receipt-name",
                        help="New directory name under verification/receipts; defaults to target and source digest")
    parser.add_argument("--verified-commit",
                        help="Optional complete commit SHA; all source and pinned bytes must match that local Git tree")
    parser.add_argument("--ci-run-url",
                        help="Optional descriptive CI run URL; not independently authenticated by this script")
    parser.add_argument("--receipt-origin", choices=("local", "ci"), default="local",
                        help="Label the supplied receipts' origin; CI origin is descriptive, not authenticated")
    parser.add_argument("--stage", action="store_true",
                        help="Copy validated receipts and write verification.json after every check passes")
    args = parser.parse_args()
    try:
        metadata, receipts, prefix = collect(args)
        if args.stage:
            stage(args.destination_root, metadata, receipts, prefix)
        print(json.dumps({"validation": "pass", "staged": args.stage, "verification": metadata}, indent=2))
        return 0
    except (ValueError, OSError, json.JSONDecodeError, KeyError, TypeError, AttributeError) as error:
        print(json.dumps({"validation": "failed", "error": str(error),
                          "verified_status_written": False}, indent=2), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
