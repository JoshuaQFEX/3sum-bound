#!/usr/bin/env python3
"""Independently check the candidate's rational numerical certificate.

Uses only Python's standard library and exact Fraction arithmetic. Reads the
actual Lean bound declarations and the accompanying JSON; it neither imports
the certificate generator nor runs Lean. A successful result establishes the
listed numerical checks, not correctness of the algorithm or a Lean build.

Typical use from the adjacent package:
    python3 verify_certificate.py
    python3 verify_certificate.py --certificate rational_certificate_refined.json \
        --parameters candidate_refined/Submission/ThreeSum/TernaryParameters.lean

The runtime modules are found beneath the same candidate root as the parameter
module. Override that root with --runtime-root when using a different layout.
JSON is written to stdout. Exit status is zero only if every check passes.
Informational decimal approximations in the input JSON are deliberately ignored.
"""

from __future__ import annotations

import argparse
import ast
from dataclasses import dataclass
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re
import sys
from typing import Callable


Q = Fraction
BASE = Path(__file__).resolve().parent
SCOPE = "Exact arithmetic checks; this script does not check the full Lean proof."
RAT = r"-?\d+(?:\s*/\s*\d+)?"
NEXT_DECL = re.compile(r"^(?:private\s+)?(?:def|theorem|namespace|end)\b", re.M)


class CheckFailure(Exception):
    """A missing input, unsupported declaration, or failed numerical check."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise CheckFailure(message)


def rational(value: object) -> Q:
    require(isinstance(value, (str, int)) and not isinstance(value, bool),
            "Rational inputs must be integers or rational strings.")
    try:
        return Q(re.sub(r"\s+", "", str(value)))
    except (ValueError, ZeroDivisionError) as exc:
        raise CheckFailure(f"Invalid rational value: {value!r}") from exc


def without_comments(text: str) -> str:
    """Remove Lean line and nested block comments while retaining newlines."""
    out: list[str] = []
    i = depth = 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            out.extend("  ")
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            out.extend("  ")
            i += 2
        elif depth:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            if j == -1:
                break
            out.extend(" " * (j - i))
            i = j
        else:
            out.append(text[i])
            i += 1
    require(depth == 0, "Unterminated Lean block comment.")
    return "".join(out)


def declaration_body(source: str, name: str) -> str:
    pattern = re.compile(r"^(?:private\s+)?def\s+" + re.escape(name) +
                         r"\b[^\n]*?:=\s*", re.M)
    matches = list(pattern.finditer(source))
    require(len(matches) == 1, f"Expected one definition of {name}.")
    start = matches[0].end()
    end = NEXT_DECL.search(source, start)
    return source[start:end.start() if end else len(source)].strip()


def python_expression(text: str) -> str:
    text = re.sub(r":\s*(?:ℝ|ℚ|Rat|Real)(?!\w)", "", text)
    text = re.sub(r"Real\.log\s+([A-Za-z_]\w*|\d+)",
                  lambda m: "LOG_" + ("two" if m[1] == "2" else m[1]), text)
    return text.replace("^", "**").strip()


@dataclass(frozen=True)
class Interval:
    lo: Q
    hi: Q

    def __post_init__(self) -> None:
        require(self.lo <= self.hi, "Reversed interval.")

    @classmethod
    def point(cls, x: Q | int) -> "Interval":
        return cls(Q(x), Q(x))

    def __add__(self, other: "Interval") -> "Interval":
        return Interval(self.lo + other.lo, self.hi + other.hi)

    def __neg__(self) -> "Interval":
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other: "Interval") -> "Interval":
        return self + (-other)

    def __mul__(self, other: "Interval") -> "Interval":
        products = [x * y for x in (self.lo, self.hi)
                    for y in (other.lo, other.hi)]
        return Interval(min(products), max(products))

    def __truediv__(self, other: "Interval") -> "Interval":
        require(not other.lo <= 0 <= other.hi, "Interval division crosses zero.")
        return self * Interval(min(1 / other.lo, 1 / other.hi),
                               max(1 / other.lo, 1 / other.hi))

    def power(self, exponent: int) -> "Interval":
        require(0 <= exponent <= 2048, "Unsupported exponent in numerical expression.")
        if exponent == 0:
            return Interval.point(1)
        endpoints = [self.lo ** exponent, self.hi ** exponent]
        lower = 0 if exponent % 2 == 0 and self.lo <= 0 <= self.hi else min(endpoints)
        return Interval(Q(lower), max(endpoints))

    def contains(self, other: "Interval") -> bool:
        return self.lo <= other.lo <= other.hi <= self.hi

    def strings(self) -> list[str]:
        return [str(self.lo), str(self.hi)]


def evaluate(text: str, names: dict[str, Interval],
             scalar: Callable[[str], Q]) -> Interval | list[Interval]:
    """Small AST evaluator; no eval, calls, attributes, or floating arithmetic."""
    try:
        tree = ast.parse(python_expression(text), mode="eval")
    except SyntaxError as exc:
        raise CheckFailure(f"Unsupported numerical expression: {text!r}") from exc

    def walk(node: ast.AST) -> Interval | list[Interval]:
        if isinstance(node, ast.Constant):
            require(type(node.value) is int, "Only integer numeric literals are allowed.")
            return Interval.point(node.value)
        if isinstance(node, ast.Name):
            return names[node.id] if node.id in names else Interval.point(scalar(node.id))
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.UAdd, ast.USub)):
            value = walk(node.operand)
            require(isinstance(value, Interval), "Unary operation on a list.")
            return -value if isinstance(node.op, ast.USub) else value
        if isinstance(node, ast.BinOp):
            left, right = walk(node.left), walk(node.right)
            require(isinstance(left, Interval) and isinstance(right, Interval),
                    "Arithmetic operation on a list.")
            if isinstance(node.op, ast.Add):
                return left + right
            if isinstance(node.op, ast.Sub):
                return left - right
            if isinstance(node.op, ast.Mult):
                return left * right
            if isinstance(node.op, ast.Div):
                return left / right
            if isinstance(node.op, ast.Pow):
                require(right.lo == right.hi and right.lo.denominator == 1,
                        "Exponent is not an exact integer.")
                return left.power(right.lo.numerator)
        if isinstance(node, ast.List):
            values = [walk(item) for item in node.elts]
            require(all(isinstance(x, Interval) for x in values), "Nested list.")
            return values
        raise CheckFailure(f"Unsupported AST node: {type(node).__name__}")

    return walk(tree.body)


class Scalars:
    def __init__(self, source: str):
        self.source = source
        self.cache: dict[str, Q] = {}
        self.active: set[str] = set()

    def __call__(self, name: str) -> Q:
        if name.isdigit():
            return Q(name)
        if name in self.cache:
            return self.cache[name]
        require(name not in self.active, f"Recursive scalar definition: {name}")
        self.active.add(name)
        result = evaluate(declaration_body(self.source, name), {}, self)
        require(isinstance(result, Interval) and result.lo == result.hi,
                f"Definition {name} is not an exact scalar.")
        self.active.remove(name)
        self.cache[name] = result.lo
        return result.lo


@dataclass(frozen=True)
class LogDeclaration:
    name: str
    argument: str
    bounds: Interval
    body: str


def logarithm_declarations(source: str) -> dict[str, LogDeclaration]:
    pattern = re.compile(
        r"^(?:private\s+)?theorem\s+log_(\w+)_bounds\s*:\s*"
        r"\((" + RAT + r")\s*:\s*ℝ\)\s*≤\s*Real\.log\s+(\w+)\s*∧\s*"
        r"Real\.log\s+\3\s*≤\s*\((" + RAT + r")\s*:\s*ℝ\)\s*:=\s*by", re.M)
    found: dict[str, LogDeclaration] = {}
    for match in pattern.finditer(source):
        name, lower, argument, upper = match.groups()
        require(name not in found, f"Duplicate logarithm bound: {name}")
        end = NEXT_DECL.search(source, match.end())
        body = source[match.end():end.start() if end else len(source)]
        found[name] = LogDeclaration(name, argument,
                                    Interval(rational(lower), rational(upper)), body)
    return found


def stated_interval(source: str, name: str) -> Interval:
    pattern = (r"^theorem\s+" + re.escape(name) + r"_bounds\s*:\s*"
               r"\((" + RAT + r")\s*:\s*ℝ\)\s*≤\s*" + re.escape(name) +
               r"\s*∧\s*" + re.escape(name) + r"\s*≤\s*\((" + RAT + r")\s*:\s*ℝ\)")
    matches = list(re.finditer(pattern, source, re.M))
    require(len(matches) == 1, f"Expected one interval declaration for {name}.")
    return Interval(rational(matches[0][1]), rational(matches[0][2]))


def json_interval(value: object) -> Interval:
    require(isinstance(value, list) and len(value) == 2, "Expected a pair of rational bounds.")
    return Interval(rational(value[0]), rational(value[1]))


def main_check(certificate_path: Path, parameters_path: Path,
               runtime_root: Path) -> dict[str, object]:
    hashes: dict[str, str] = {}

    def read_source(path: Path) -> str:
        data = path.read_bytes()
        hashes[str(path.resolve())] = hashlib.sha256(data).hexdigest()
        return without_comments(data.decode("utf-8"))

    certificate_bytes = certificate_path.read_bytes()
    # Decimal display approximations are not used in any acceptance decision.
    certificate = json.loads(certificate_bytes, parse_float=str)
    source = read_source(parameters_path)
    scalars = Scalars(source)
    logs = logarithm_declarations(source)
    require(set(logs) == set(certificate["log_bounds"]) and len(logs) == 22,
            "Source and JSON must contain exactly the same 22 logarithm intervals.")
    for name, declaration in logs.items():
        require(declaration.bounds == json_interval(certificate["log_bounds"][name]),
                f"JSON/source mismatch for log {name}.")
        expected_arg = "2" if name == "two" else name
        require(declaration.argument == expected_arg, f"Unexpected argument in log {name}.")

    direct: set[str] = set()
    direct_slacks: list[Q] = []
    errors: list[Q] = []
    series_terms: set[int] = set()
    for name, declaration in logs.items():
        if "Real.sum_range_sub_log_div_le" not in declaration.body:
            continue
        pattern = (r"\|\s*\(\s*\(\s*(" + RAT + r")\s*:\s*ℝ\s*\)\s*:\s*ℝ\s*\)"
                   r"\s*\|\s*<\s*1\s*\)\s*(\d+)")
        matches = list(re.finditer(pattern, declaration.body))
        require(len(matches) == 1, f"Cannot parse series parameter/count in log {name}.")
        t, count = rational(matches[0][1]), int(matches[0][2])
        require(0 < count <= 1024 and abs(t) < 1, f"Invalid atanh parameters for {name}.")
        require((1 + t) / (1 - t) == scalars(declaration.argument),
                f"Atanh argument identity fails for {name}.")
        center = 2 * sum((t ** (2 * j + 1) / (2 * j + 1)
                          for j in range(count)), Q(0))
        # EXACT Mathlib coarse remainder after doubling the half-log theorem.
        # Deliberately no division by 2*count+1.
        error = 2 * abs(t) ** (2 * count + 1) / (1 - t * t)
        enclosure = Interval(center - error, center + error)
        require(declaration.bounds.contains(enclosure),
                f"Declared log {name} interval fails the coarse Mathlib remainder check.")
        direct.add(name)
        direct_slacks.extend([enclosure.lo - declaration.bounds.lo,
                              declaration.bounds.hi - enclosure.hi])
        errors.append(error)
        series_terms.add(count)
    require(len(direct) == 13, "Expected 13 direct logarithm proofs.")

    derived = set(logs) - direct
    require(len(derived) == 9, "Expected nine logarithms derived by powers of two.")
    for name in sorted(derived):
        declaration = logs[name]
        pattern = (r"have\s+heq\s*:\s*" + re.escape(declaration.argument) +
                   r"\s*=\s*(normalized_\w+)\s*([/*])\s*\(\s*2\s*:\s*ℝ\s*\)"
                   r"\s*\^\s*(\d+)\s*:=")
        match = re.search(pattern, declaration.body)
        require(match is not None, f"Missing normalization identity for {name}.")
        normalized, operator, power_text = match.groups()
        require(normalized in direct, f"Normalization for {name} is not directly bounded.")
        power = int(power_text) * (1 if operator == "*" else -1)
        require(scalars(declaration.argument) == scalars(normalized) * Q(2) ** power,
                f"Power-of-two identity fails for {name}.")
        enclosure = logs[normalized].bounds + Interval.point(power) * logs["two"].bounds
        require(declaration.bounds.contains(enclosure),
                f"Normalized logarithm enclosure fails for {name}.")

    entropy_names = ["Hpi", "Halpha", "partitionEntropy", "bankEntropy", "queryEntropy"]
    require(set(certificate["entropy_bounds"]) == set(entropy_names),
            "Unexpected entropy entries in JSON.")
    environment = {"LOG_" + name: declaration.bounds for name, declaration in logs.items()}
    entropies: dict[str, Interval] = {}
    for name in entropy_names:
        declared = stated_interval(source, name)
        require(declared == json_interval(certificate["entropy_bounds"][name]),
                f"JSON/source entropy mismatch for {name}.")
        computed = evaluate(declaration_body(source, name), environment, scalars)
        require(isinstance(computed, Interval) and declared.contains(computed),
                f"The declared entropy interval does not follow by interval arithmetic: {name}.")
        entropies[name] = declared

    principal, target = scalars("certificateExponent"), scalars("targetExponent")
    require(principal == rational(certificate["certificate"]) and
            target == rational(certificate["target"]), "Certificate or target differs from source.")
    ledger = evaluate(declaration_body(source, "costLedger"), entropies, scalars)
    require(isinstance(ledger, list) and len(ledger) == 6, "Expected six actual cost-ledger terms.")
    ledger_upper = [term.hi for term in ledger]
    require(ledger_upper == [rational(x) for x in certificate["ledger_upper"]],
            "The JSON ledger upper bounds differ from actual source interval arithmetic.")
    require(all(x < principal for x in ledger_upper), "A ledger term reaches the certificate.")
    H, A, G, B, R = (entropies[name] for name in entropy_names)
    cross_slacks = [principal * H.lo - 2 * B.hi,
                    G.lo - 2 * R.hi - (2 - principal) * H.hi,
                    principal * H.lo - 2 * A.hi,
                    (principal - 1) * H.lo - G.hi,
                    G.lo - (2 - principal) * H.hi]
    require(cross_slacks == [rational(x) for x in certificate["cross_multiplication_slack"]],
            "Cross-multiplication slack values differ from JSON.")
    require(all(x > 0 for x in cross_slacks), "Nonpositive cross-multiplication slack.")
    require(G.lo / H.hi > Q(2517, 10000) and H.lo > Q(4, 5) and
            G.hi / H.lo < Q(63, 250), "A fixed downstream entropy comparison fails.")

    module_dir = runtime_root / "Submission" / "ThreeSum"
    module_names = ["TernaryOversizeRates", "TernaryOversizeOverhead",
                    "TernaryCountFrontendBudget", "TernaryActualPrefixRuntime",
                    "TernaryActualRuntimeParameters", "TernaryActualColoredRuntime",
                    "TernaryProfileRuntime", "TernarySolverEndBridge", "TernaryFinalSolver"]
    modules = {name: read_source(module_dir / (name + ".lean")) for name in module_names}
    entry = read_source(runtime_root / "Submission.lean")
    margins = certificate["runtime_margins"]
    soft = Scalars(modules["TernaryOversizeRates"])("softCertificate")
    frontend = Scalars(modules["TernaryCountFrontendBudget"])("frontendExponent")
    colored = Scalars(modules["TernaryActualColoredRuntime"])("exponent")
    for name, value in [("soft", soft), ("frontend", frontend), ("colored", colored)]:
        require(value == rational(margins[name]), f"Runtime scalar {name} differs from JSON.")

    K_min = margins["K_min"]
    require(type(K_min) is int and K_min > 0, "Invalid K lower bound.")
    for module, theorem in [("TernaryOversizeRates", "goodBlock_eventually"),
                            ("TernaryActualRuntimeParameters", "runtime_margin"),
                            ("TernaryActualColoredRuntime", "selected_room")]:
        pattern = r"theorem\s+" + theorem + r"[^\n]*?\(hK\s*:\s*(\d+)\s*≤\s*K\)"
        match = re.search(pattern, modules[module])
        require(match is not None and int(match[1]) == K_min,
                f"K lower bound mismatch in {module}.{theorem}.")
    micro_expression = declaration_body(modules["TernaryOversizeOverhead"], "microAllowance")
    actual_ast = ast.dump(ast.parse(python_expression(micro_expression), mode="eval"))
    expected_ast = ast.dump(ast.parse("1/(100*K**2)", mode="eval"))
    require(actual_ast == expected_ast, "Unexpected microAllowance formula; monotonicity not established.")
    micro = Q(1, 100 * K_min ** 2)
    allowance = rational(margins["micro_bound"])
    require(micro == rational(margins["micro_max"]) and 0 < micro < allowance,
            "The micro-allowance maximum or bound is incorrect.")
    for module in ["TernaryOversizeOverhead", "TernaryCountFrontendBudget",
                   "TernaryActualPrefixRuntime", "TernaryActualRuntimeParameters",
                   "TernaryActualColoredRuntime"]:
        bounds = re.findall(r"have\s+\S+\s*:\s*microAllowance K\s*<\s*\((" + RAT +
                            r")\s*:\s*ℝ\)", modules[module])
        require(bounds and all(rational(x) == allowance for x in bounds),
                f"Auxiliary micro bound mismatch in {module}.")
    additions = re.findall(r"fullExponent K[^\n]*\+microAllowance K\+\((" + RAT +
                           r")\s*:\s*ℝ\)<", modules["TernaryActualRuntimeParameters"])
    require(len(additions) == 2 and all(rational(x) == allowance for x in additions),
            "Unexpected additive slack in actual runtime parameter statements.")
    for constant in [8, 10]:
        match = re.search(r"have\s+h" + str(constant) + r"\s*:\s*" + str(constant) +
                          r"/\(K\s*:\s*ℝ\)\s*<\s*\((" + RAT + r")\s*:\s*ℝ\)",
                          modules["TernaryOversizeRates"])
        require(match is not None and rational(match[1]) == soft - principal,
                f"Oversize-rate allowance mismatch for {constant}/K.")
        require(Q(constant, K_min) < soft - principal,
                f"Insufficient finite-K margin for {constant}/K.")
    require(soft + allowance <= frontend, "Micro bound does not fit frontend margin.")
    require(frontend + allowance <= colored, "Micro bound does not fit colored margin.")
    require(frontend + 2 * allowance <= target,
            "The source runtime_margin proof lacks enough auxiliary slack.")
    require(soft + micro < frontend and frontend + micro < colored and
            frontend + micro + allowance < target and colored < target,
            "Actual runtime margin chain fails.")
    differences = {"soft_minus_certificate": soft - principal,
                   "target_minus_certificate": target - principal,
                   "target_minus_soft": target - soft,
                   "target_minus_frontend": target - frontend,
                   "target_minus_colored": target - colored,
                   "largest_ledger_to_certificate_gap": principal - max(ledger_upper)}
    for name, value in differences.items():
        require(value == rational(margins[name]), f"Runtime difference {name} differs from JSON.")
    for module, theorem, actual in [(source, "certificate_margin", target - principal),
                                    (modules["TernaryOversizeRates"], "soft_certificate_margin", target - soft),
                                    (modules["TernaryCountFrontendBudget"], "frontend_margin", target - frontend)]:
        match = re.search(r"theorem\s+" + theorem + r"[^\n]*?=\s*\((" + RAT +
                          r")\s*:\s*ℝ\)", module)
        require(match is not None and rational(match[1]) == actual,
                f"Exact margin identity fails: {theorem}.")
    bridge = Scalars(modules["TernarySolverEndBridge"])
    require(bridge("target") == bridge("targetExponent") == target,
            "Final bridge target differs from numerical target.")
    for name, module in [("TernaryFinalSolver", modules["TernaryFinalSolver"]),
                         ("Submission", entry)]:
        match = re.search(r"EndStatement\.ThreeSum\.SolvedInTime\s*(\([^\n]+\))\s*:=", module)
        require(match is not None, f"Cannot identify exported target in {name}.")
        exported = evaluate(match[1], {}, scalars)
        require(exported == Interval.point(target), f"Exported target mismatch in {name}.")

    return {
        "status": "pass",
        "scope": SCOPE,
        "certificate_file": str(certificate_path.resolve()),
        "certificate_sha256": hashlib.sha256(certificate_bytes).hexdigest(),
        "source_sha256": hashes,
        "checks": {
            "direct_logarithms_with_coarse_mathlib_remainder": len(direct),
            "derived_logarithms_via_exact_power_of_two_identities": len(derived),
            "entropy_enclosures_from_actual_definitions": len(entropies),
            "actual_cost_ledger_terms_strictly_below_certificate": len(ledger),
            "positive_cross_multiplication_slacks": len(cross_slacks),
            "fixed_downstream_entropy_comparisons": 3,
            "runtime_margins_and_source_constants": "pass",
            "final_exported_rational_target": "pass",
        },
        "series_terms": sorted(series_terms),
        "largest_coarse_log_remainder": str(max(errors)),
        "smallest_direct_log_endpoint_slack": str(min(direct_slacks)),
        "principal_certificate": str(principal),
        "final_target": str(target),
        "ledger_upper_bounds": [str(x) for x in ledger_upper],
        "smallest_ledger_certificate_gap": str(principal - max(ledger_upper)),
        "runtime": {
            "K_min": K_min, "micro_max": str(micro), "auxiliary_allowance": str(allowance),
            "soft": str(soft), "frontend": str(frontend), "colored": str(colored),
            "target": str(target),
            "uniformity_reason": "8/K, 10/K and 1/(100*K^2) decrease for positive K.",
        },
        "limitations": [
            "Checks exact numerical enclosures and the supported source declarations only.",
            "Does not execute Lean, validate proof terms, or establish algorithm correctness.",
            "Does not replace an unchanged-source Lean build and transitive axiom audit.",
            "Informational JSON decimal approximations are ignored in all checks.",
        ],
    }


def first_existing(paths: list[Path]) -> Path:
    return next((path for path in paths if path.is_file()), paths[0])


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--certificate", type=Path, default=first_existing([
        BASE / "rational_certificate_refined.json", BASE / "rational_certificate.json"]))
    parser.add_argument("--parameters", "--source", dest="parameters", type=Path,
                        default=first_existing([
                            BASE / "candidate_refined/Submission/ThreeSum/TernaryParameters.lean",
                            BASE / "source/Submission/ThreeSum/TernaryParameters.lean",
                            BASE / "Submission/ThreeSum/TernaryParameters.lean",
                            BASE / "candidate/Submission/ThreeSum/TernaryParameters.lean"]))
    parser.add_argument("--runtime-root", type=Path,
                        help="Candidate root containing Submission.lean and Submission/ThreeSum/.")
    args = parser.parse_args()
    try:
        runtime_root = args.runtime_root or args.parameters.resolve().parents[2]
        result = main_check(args.certificate, args.parameters, runtime_root)
    except (CheckFailure, OSError, ValueError, KeyError, TypeError, SyntaxError) as exc:
        print(json.dumps({"status": "fail", "scope": SCOPE, "error": str(exc)}, indent=2))
        return 1
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
