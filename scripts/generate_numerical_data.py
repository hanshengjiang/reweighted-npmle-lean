#!/usr/bin/env python3
"""Generate the Lean certificate from committed numerical-study outputs."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
from fractions import Fraction
from pathlib import Path


FORMALIZATION = Path(__file__).resolve().parents[1]
ROOT = FORMALIZATION / "data"
SOURCES = [
    ROOT / "results" / "monte_carlo_1d.csv",
    ROOT / "results" / "monte_carlo_2d.csv",
]
PATH_SOURCE = ROOT / "results" / "path_results.csv"
KEY_FINDINGS_SOURCE = ROOT / "results" / "key_findings.json"
MULTISTART_SOURCE = ROOT / "results" / "multistart_stability.json"
TABLE_SOURCE = ROOT / "results" / "numerical_summary.tex"
OUTPUT = FORMALIZATION / "ReweightedNPMLE" / "GeneratedNumericalData.lean"
REGRESSION_OUTPUT = FORMALIZATION / "ReweightedNPMLE" / "GeneratedNumericalRegressionData.lean"
SUMMARY_OUTPUT = FORMALIZATION / "ReweightedNPMLE" / "GeneratedNumericalSummarySamples.lean"


def key(row: dict[str, str]) -> tuple[str, int, int, int]:
    return (
        row["scenario"],
        int(row["dimension"]),
        int(row["n"]),
        int(row["replication"]),
    )


def lean_rat(value: Fraction) -> str:
    return f"({value.numerator} : ℚ) / ({value.denominator} : ℚ)"


def mean(values: list[Fraction]) -> Fraction:
    return sum(values, Fraction()) / len(values)


def logarithm_certificate(q: Fraction) -> tuple[Fraction, bool, int, Fraction, Fraction]:
    """Outward decimal endpoints from exact rational 12-term log enclosures."""
    if q <= 0:
        raise ValueError(f"nonpositive logarithm argument: {q}")
    inverse = q < 1
    adjusted = 1 / q if inverse else q
    exponent = 0
    while Fraction(2) ** (exponent + 1) <= adjusted:
        exponent += 1

    def unit_bounds(value: Fraction) -> tuple[Fraction, Fraction]:
        y = (value - 1) / (value + 1)
        lower = 2 * sum((y ** (2 * i + 1) / (2 * i + 1) for i in range(12)), Fraction())
        error = 2 * y**25 / (1 - y**2)
        return lower, error

    two_lower, two_error = unit_bounds(Fraction(2))
    unit_lower, unit_error = unit_bounds(adjusted / 2**exponent)
    lower = exponent * two_lower + unit_lower
    upper = lower + exponent * two_error + unit_error
    if inverse:
        lower, upper = -upper, -lower
    scale = 100_000_000
    lower = Fraction((lower * scale).__floor__(), scale)
    upper = Fraction((upper * scale).__ceil__(), scale)
    return q, inverse, exponent, lower, upper


def path_certificates(path_rows: list[dict[str, str]]) -> tuple[list, list]:
    """Raw path samples, sorting permutations and displayed quantile bins."""
    targets = {
        "BB-scale": Fraction(1),
        "balanced": Fraction(path_rows[0]["balanced_alpha"]),
        "tiny": Fraction(500**3),
    }
    reports = [
        ("balanced", "hellinger_to_ordinary", 1, 2, "4.40e-5", "5e-8"),
        ("balanced", "ordinary_loglik_gap", 1, 2, "0.0453", "0.00005"),
        ("balanced", "hellinger_to_truth", 1, 2, "0.002664", "0.0000005"),
        ("balanced", "wasserstein_to_ordinary", 1, 2, "0.0308", "0.00005"),
        ("balanced", "support", 1, 2, "3", "0"),
        ("tiny", "hellinger_to_ordinary", 1, 2, "1.52e-11", "5e-14"),
        ("tiny", "ordinary_loglik_gap", 1, 2, "1.65e-8", "5e-11"),
        ("tiny", "hellinger_to_truth", 1, 2, "0.002662", "0.0000005"),
        ("tiny", "support", 1, 2, "3", "0"),
        ("BB-scale", "hellinger_to_ordinary", 1, 2, "1.95e-3", "5e-6"),
        ("BB-scale", "ordinary_loglik_gap", 1, 2, "2.03", "0.005"),
        ("BB-scale", "support", 9, 10, "4", "0"),
    ]
    samples, certificates = [], []
    for regime, column, quantile_num, quantile_den, printed, tolerance in reports:
        subset = [row for row in path_rows if Fraction(row["alpha"]) == targets[regime]]
        if len(subset) != 30 or {int(row["draw"]) for row in subset} != set(range(30)):
            raise ValueError(f"unexpected path draws for {regime}: {len(subset)}")
        values = [Fraction(row[column]) for row in subset]
        permutation = sorted(range(30), key=values.__getitem__)
        label = f"{regime} {column} q={quantile_num}/{quantile_den}"
        samples.append((label, values))
        certificates.append((label, permutation, [values[i] for i in permutation],
                             quantile_num, quantile_den, Fraction(printed), Fraction(tolerance)))
    return samples, certificates


def regression_certificate(path_rows: list[dict[str, str]], hashes: list[tuple[str, str]]) -> tuple[str, list]:
    """Raw medians and exact interval evaluations of the four OLS slopes."""
    alphas = sorted({Fraction(row["alpha"]) for row in path_rows if Fraction(row["alpha"]) >= 10})
    if len(alphas) != 14:
        raise ValueError(f"unexpected regression alpha count: {len(alphas)}")

    def log_record(certificate: tuple) -> str:
        q, inverse, exponent, lower, upper = certificate
        return f"⟨{lean_rat(q)}, {str(inverse).lower()}, {exponent}, {lean_rat(lower)}, {lean_rat(upper)}⟩"

    def add(left: tuple, right: tuple) -> tuple:
        return left[0] + right[0], left[1] + right[1]

    def subtract(left: tuple, right: tuple) -> tuple:
        return left[0] - right[1], left[1] - right[0]

    def multiply(left: tuple, right: tuple) -> tuple:
        products = [x * y for x in left for y in right]
        return min(products), max(products)

    def interval_sum(intervals: list[tuple]) -> tuple:
        total = Fraction(), Fraction()
        for interval in intervals:
            total = add(total, interval)
        return total

    lines = [
        "/- This file is generated by scripts/generate_numerical_data.py. -/",
        "import ReweightedNPMLE.NumericalRegressionArithmetic", "",
        "namespace ReweightedNPMLE.NumericalStudy.RegressionData", "",
        "set_option maxRecDepth 100000", "set_option maxHeartbeats 10000000", "",
    ]
    for filename, digest in hashes:
        if filename in {PATH_SOURCE.name, KEY_FINDINGS_SOURCE.name}:
            stem = Path(filename).stem.replace("_", " ").title().replace(" ", "")
            lines.append(f'def sha256{stem} : String := "{digest}"')
    lines.extend(["", "def eligibleAlphas : List ℚ := ["])
    lines.extend(f"  {lean_rat(alpha)}," for alpha in alphas)
    lines.append("]")
    x_certificates = [logarithm_certificate(alpha) for alpha in alphas]
    dataset_names, audits = [], []
    metrics = [("weight_max_deviation", "-0.503"), ("hellinger_to_ordinary", "-1.016"),
               ("ordinary_loglik_gap", "-1.016"), ("logfit_sq_sum", "-1.012")]
    for dataset_index, (metric, printed) in enumerate(metrics):
        point_names, y_certificates = [], []
        for index, alpha in enumerate(alphas):
            subset = [row for row in path_rows if Fraction(row["alpha"]) == alpha]
            if len(subset) != 30 or [int(row["draw"]) for row in subset] != list(range(30)):
                raise ValueError(f"unexpected regression draws for alpha {alpha}")
            values = [Fraction(row[metric]) for row in subset]
            permutation = sorted(range(30), key=values.__getitem__)
            sorted_values = [values[i] for i in permutation]
            median = (sorted_values[14] + sorted_values[15]) / 2
            y_certificate = logarithm_certificate(median)
            y_certificates.append(y_certificate)
            point_name = f"regressionPoint{dataset_index}_{index}"
            point_names.append(point_name)
            lines.extend(["", f"@[simp] private def {point_name} : NumericalRegressionPoint :=",
                          f"  ⟨{lean_rat(alpha)}, ["])
            lines.extend(f"    {lean_rat(value)}," for value in values)
            indices = ", ".join(str(i) for i in permutation)
            lines.append(f"  ], [{indices}], [")
            lines.extend(f"    {lean_rat(value)}," for value in sorted_values)
            lines.append(f"  ], {log_record(x_certificates[index])}, {log_record(y_certificate)}⟩")
        xs = [(c[3], c[4]) for c in x_certificates]
        ys = [(c[3], c[4]) for c in y_certificates]
        count = Fraction(14), Fraction(14)
        sx, sy = interval_sum(xs), interval_sum(ys)
        sxy = interval_sum([multiply(x, y) for x, y in zip(xs, ys)])
        sxx = interval_sum([multiply(x, x) for x in xs])
        numerator = subtract(multiply(count, sxy), multiply(sx, sy))
        denominator = subtract(multiply(count, sxx), multiply(sx, sx))
        if denominator[0] <= 0:
            raise ValueError(f"regression denominator not certified positive: {metric}")
        enclosure = multiply(numerator, (1 / denominator[1], 1 / denominator[0]))
        dataset_name = f"regressionDataset{dataset_index}"
        dataset_names.append(dataset_name)
        lines.extend([
            "", f"@[simp] private def {dataset_name} : NumericalRegressionDataset :=",
            f"  ⟨{json.dumps(metric)}, [{', '.join(point_names)}], {lean_rat(Fraction(printed))},",
            f"    ⟨{lean_rat(enclosure[0])}, {lean_rat(enclosure[1])}⟩⟩",
        ])
        audits.append((metric, enclosure, Fraction(printed)))
    lines.extend(["", "def datasets : List NumericalRegressionDataset :=",
                  f"  [{', '.join(dataset_names)}]", "",
                  "end ReweightedNPMLE.NumericalStudy.RegressionData", ""])
    return "\n".join(lines), audits


def summary_samples(
    by_summary_cell: dict[tuple[str, int, int], dict[str, list[dict[str, str]]]],
    hashes: list[tuple[str, str]],
) -> str:
    """Every raw draw used by the 11-cell means, risk ratios and support pairs."""
    lines = [
        "/- This file is generated by scripts/generate_numerical_data.py. -/",
        "import ReweightedNPMLE.NumericalSummaryArithmetic", "",
        "namespace ReweightedNPMLE.NumericalStudy.SummaryData", "",
        "set_option maxRecDepth 100000", "set_option maxHeartbeats 10000000", "",
    ]
    for filename, digest in hashes:
        if filename in {source.name for source in SOURCES}:
            stem = Path(filename).stem.replace("_", " ").title().replace(" ", "")
            lines.append(f'def sha256{stem} : String := "{digest}"')
    fields = [
        ("ordinaryRisk", "Ordinary", "hellinger_to_truth", False),
        ("balancedRisk", "RR-balanced", "hellinger_to_truth", False),
        ("tinyRisk", "RR-tiny", "hellinger_to_truth", False),
        ("bbRisk", "BB", "hellinger_to_truth", False),
        ("ordinarySupport", "Ordinary", "support", True),
        ("balancedSupport", "RR-balanced", "support", True),
        ("tinySupport", "RR-tiny", "support", True),
        ("bbSupport", "BB", "support", True),
        ("balancedHellinger", "RR-balanced", "hellinger_to_ordinary", False),
        ("tinyHellinger", "RR-tiny", "hellinger_to_ordinary", False),
        ("balancedGap", "RR-balanced", "ordinary_loglik_gap", False),
        ("bbGap", "BB", "ordinary_loglik_gap", False),
        ("balancedLogfit", "RR-balanced", "logfit_sq_sum", False),
    ]
    names = []
    for index, ((scenario, dimension, sample_size), methods) in enumerate(sorted(by_summary_cell.items())):
        count = len(methods["Ordinary"])
        methods = {method: sorted(method_rows, key=lambda row: int(row["replication"]))
                   for method, method_rows in methods.items()}
        for method, method_rows in methods.items():
            if [int(row["replication"]) for row in method_rows] != list(range(count)):
                raise ValueError(f"unexpected summary replication order: {scenario}, {sample_size}, {method}")
        name = f"summaryCell{index}"
        names.append(name)
        lines.extend(["", f"@[simp] private def {name} : NumericalSummaryCell where",
                      f"  scenario := {json.dumps(scenario)}", f"  dimension := {dimension}",
                      f"  sampleSize := {sample_size}",
                      f"  replications := [{', '.join(str(i) for i in range(count))}]"])
        for field, method, column, integer in fields:
            values = [Fraction(row[column]) for row in methods[method]]
            lines.append(f"  {field} := [")
            for value in values:
                if integer and (value.denominator != 1 or value < 0):
                    raise ValueError(f"invalid recorded support: {value}")
                lines.append(f"    {value.numerator if integer else lean_rat(value)},")
            lines.append("  ]")
    lines.extend(["", "def cells : List NumericalSummaryCell :=",
                  f"  [{', '.join(names)}]", "",
                  "end ReweightedNPMLE.NumericalStudy.SummaryData", ""])
    return "\n".join(lines)


def table_certificates(
    by_summary_cell: dict[tuple[str, int, int], dict[str, list[dict[str, str]]]],
) -> tuple[list[tuple[str, Fraction, Fraction, Fraction]],
           list[tuple[str, Fraction, Fraction, Fraction]],
           list[tuple[str, list[Fraction]]]]:
    """Exact means and squared standard errors with the table's precision bins."""
    means, standard_errors, raw_samples = [], [], []
    scenarios = {
        "Three-point": ("three_point_1d", 1),
        "Uniform mixing": ("uniform_1d", 1),
        "Four-point square": ("square_2d", 2),
    }
    methods = {"Ordinary": "Ordinary", "Balanced": "RR-balanced", "Tiny": "RR-tiny", "BB-scale": "BB"}
    columns = ["support", "hellinger_to_truth", "hellinger_to_ordinary", "ordinary_loglik_gap"]
    number = re.compile(r"^\$([0-9.]+)(?:\\,\(([0-9.]+)\))?(?:\\times 10\^\{(-?\d+)\})?\$$")
    current_cell = None
    row_count = 0
    for line in TABLE_SOURCE.read_text(encoding="utf-8").splitlines():
        if not re.search(r" & (Ordinary|Balanced|Tiny|BB-scale) & ", line):
            continue
        fields = [field.strip() for field in line.removesuffix(r"\\").split("&")]
        if len(fields) != 6:
            raise ValueError(f"unexpected numerical table row: {line}")
        if fields[0]:
            prefix = next(name for name in scenarios if fields[0].startswith(name))
            scenario, dimension = scenarios[prefix]
            sample_size = int(re.search(r"\((\d+)\)", fields[0]).group(1))
            current_cell = (scenario, dimension, sample_size)
        method = methods[fields[1]]
        rows = by_summary_cell[current_cell][method]
        row_count += 1
        for column, displayed in zip(columns, fields[2:]):
            match = number.fullmatch(displayed)
            if match is None:
                raise ValueError(f"unexpected numerical table cell: {displayed}")
            mean_digits, se_digits, exponent = match.groups()
            scale = Fraction(10) ** int(exponent or 0)
            precision = lambda digits: scale / (2 * 10 ** len(digits.partition(".")[2]))
            values = [Fraction(row[column]) for row in rows]
            actual_mean = mean(values)
            printed_mean = Fraction(mean_digits) * scale
            mean_tolerance = precision(mean_digits) if se_digits is not None else Fraction(0)
            label = f"{current_cell[0]} n={current_cell[2]} {method} {column}"
            means.append((label, actual_mean, printed_mean, mean_tolerance))
            raw_samples.append((label, values))
            if se_digits is not None:
                count = len(values)
                actual_se_sq = sum((value - actual_mean) ** 2 for value in values) / (count * (count - 1))
                printed_se = Fraction(se_digits) * scale
                se_tolerance = precision(se_digits)
                if printed_se < se_tolerance:
                    raise ValueError(f"negative standard-error precision bin: {label}")
                standard_errors.append((label, actual_se_sq, printed_se, se_tolerance))
    if row_count != 12 or len(means) != 48 or len(standard_errors) != 42:
        raise ValueError(f"unexpected table certificate sizes: {row_count}, {len(means)}, {len(standard_errors)}")
    return means, standard_errors, raw_samples


def main(*, check: bool = False, audit: bool = False) -> None:
    rows: list[dict[str, str]] = []
    hashes: list[tuple[str, str]] = []
    for source in SOURCES:
        raw = source.read_bytes()
        hashes.append((source.name, hashlib.sha256(raw).hexdigest()))
        with source.open(newline="", encoding="utf-8") as handle:
            rows.extend(csv.DictReader(handle))

    path_raw = PATH_SOURCE.read_bytes()
    hashes.append((PATH_SOURCE.name, hashlib.sha256(path_raw).hexdigest()))
    with PATH_SOURCE.open(newline="", encoding="utf-8") as handle:
        path_rows = list(csv.DictReader(handle))

    for source in [KEY_FINDINGS_SOURCE, MULTISTART_SOURCE]:
        hashes.append((source.name, hashlib.sha256(source.read_bytes()).hexdigest()))
    key_findings = json.loads(KEY_FINDINGS_SOURCE.read_text(encoding="utf-8"))
    multistart_rows = json.loads(MULTISTART_SOURCE.read_text(encoding="utf-8"))
    hashes.append((TABLE_SOURCE.name, hashlib.sha256(TABLE_SOURCE.read_bytes()).hexdigest()))

    by_cell: dict[tuple[str, int, int, int], dict[str, int]] = {}
    for row in rows:
        by_cell.setdefault(key(row), {})[row["method"]] = int(float(row["support"]))

    triples: list[tuple[int, int, int]] = []
    expected = {"Ordinary", "RR-balanced", "RR-tiny", "BB"}
    for cell in sorted(by_cell):
        methods = by_cell[cell]
        if set(methods) != expected:
            raise ValueError(f"unexpected methods for {cell}: {sorted(methods)}")
        triples.append((methods["Ordinary"], methods["RR-balanced"], methods["RR-tiny"]))

    if len(rows) != 3680 or len(triples) != 920:
        raise ValueError(f"unexpected sizes: {len(rows)} rows, {len(triples)} pairs")

    all_rows = rows + path_rows
    diagnostic_flags = [
        (
            float(row["converged"]) == 1.0,
            Fraction(row["kkt_gap"]) < Fraction(1, 500_000),
            Fraction(row["ordinary_loglik_gap_raw"]) >= Fraction(-1, 10_000),
        )
        for row in all_rows
    ]
    one_dimensional_kkt_flags = [
        Fraction(row["kkt_gap"]) < Fraction(1, 2_000_000)
        for row in rows
        if int(row["dimension"]) == 1
    ] + [Fraction(row["kkt_gap"]) < Fraction(1, 2_000_000) for row in path_rows]

    multistart_diagnostics = [
        (
            int(row["support"]) == int(row["reference_support"]),
            Fraction(str(row["hellinger_to_reference"])),
            Fraction(str(row["kkt_gap"])),
        )
        for row in multistart_rows
    ]
    slope_order = [
        "weight_max_deviation",
        "hellinger_to_ordinary",
        "ordinary_loglik_gap",
        "logfit_sq_sum",
    ]
    path_slopes = [
        Fraction(str(key_findings["path_slopes_on_medians_alpha_ge_10"][name]))
        for name in slope_order
    ]

    by_summary_cell: dict[tuple[str, int, int], dict[str, list[dict[str, str]]]] = {}
    for row in rows:
        cell = (row["scenario"], int(row["dimension"]), int(row["n"]))
        by_summary_cell.setdefault(cell, {}).setdefault(row["method"], []).append(row)

    balanced_risk_ratios: list[Fraction] = []
    tiny_risk_ratios: list[Fraction] = []
    bb_risk_ratios: list[Fraction] = []
    balanced_support_differences: list[Fraction] = []
    balanced_hellinger_means: list[Fraction] = []
    tiny_hellinger_means: list[Fraction] = []
    balanced_gap_means: list[Fraction] = []
    bb_gap_means: list[Fraction] = []
    balanced_logfit_means: list[Fraction] = []
    for cell in sorted(by_summary_cell):
        methods = by_summary_cell[cell]
        ordinary_risk = mean([
            Fraction(row["hellinger_to_truth"]) for row in methods["Ordinary"]
        ])
        for method, target in [
            ("RR-balanced", balanced_risk_ratios),
            ("RR-tiny", tiny_risk_ratios),
            ("BB", bb_risk_ratios),
        ]:
            target.append(mean([
                Fraction(row["hellinger_to_truth"]) for row in methods[method]
            ]) / ordinary_risk)
        balanced_support_differences.append(mean([
            Fraction(row["support"]) for row in methods["RR-balanced"]
        ]) - mean([
            Fraction(row["support"]) for row in methods["Ordinary"]
        ]))
        balanced_hellinger_means.append(mean([
            Fraction(row["hellinger_to_ordinary"]) for row in methods["RR-balanced"]
        ]))
        tiny_hellinger_means.append(mean([
            Fraction(row["hellinger_to_ordinary"]) for row in methods["RR-tiny"]
        ]))
        balanced_gap_means.append(mean([
            Fraction(row["ordinary_loglik_gap"]) for row in methods["RR-balanced"]
        ]))
        bb_gap_means.append(mean([
            Fraction(row["ordinary_loglik_gap"]) for row in methods["BB"]
        ]))
        balanced_logfit_means.append(mean([
            Fraction(row["logfit_sq_sum"]) for row in methods["RR-balanced"]
        ]))

    table_means, table_standard_errors, table_raw_samples = table_certificates(by_summary_cell)
    path_samples, path_reports = path_certificates(path_rows)
    design_counts = [
        (scenario, dimension, sample_size, len(methods["Ordinary"]))
        for (scenario, dimension, sample_size), methods in sorted(by_summary_cell.items())
    ]
    path_draw_groups = {}
    for row in path_rows:
        path_draw_groups.setdefault(Fraction(row["alpha"]), []).append(int(row["draw"]))
    if any(int(row["n"]) != 500 for row in path_rows):
        raise ValueError("unexpected path sample size")
    if any(Fraction(row["ordinary_hellinger_to_truth"]) !=
           Fraction(path_rows[0]["ordinary_hellinger_to_truth"]) for row in path_rows):
        raise ValueError("inconsistent fixed path baseline")
    sample_size_log_certificates = [logarithm_certificate(Fraction(n))
        for n in sorted({cell[2] for cell in by_summary_cell})]

    printed_ranges = [
        ("balanced risk ratio", "balancedRiskRatios", balanced_risk_ratios, "1.001", "1.020", ".0005", ".0005"),
        ("tiny risk ratio", "tinyRiskRatios", tiny_risk_ratios, "0.999985", "1.000018", ".0000005", ".0000005"),
        ("BB risk ratio", "bbRiskRatios", bb_risk_ratios, "1.60", "2.19", ".005", ".005"),
        ("balanced H2 to ordinary", "balancedMeanHellingerToOrdinary", balanced_hellinger_means, "8.31e-6", "1.76e-4", "5e-9", "5e-7"),
        ("tiny H2 to ordinary", "tinyMeanHellingerToOrdinary", tiny_hellinger_means, "1.43e-13", "9.60e-10", "5e-16", "5e-13"),
        ("balanced likelihood loss", "balancedMeanOrdinaryLoglikGap", balanced_gap_means, "0.0345", "0.0964", ".00005", ".00005"),
        ("BB likelihood loss", "bbMeanOrdinaryLoglikGap", bb_gap_means, "2.14", "7.86", ".005", ".005"),
        ("balanced support difference", "balancedMeanSupportDifferences", balanced_support_differences, "-0.125", "0.025", "0", "0"),
    ]

    if audit:
        # Exact rational comparisons, not floating-point tests of the bounds.
        for name, _, values, low, high, _, _ in printed_ranges:
            actual_low, actual_high = min(values), max(values)
            valid = Fraction(low) <= actual_low and actual_high <= Fraction(high)
            print(f"{name}: printed [{low}, {high}], "
                  f"actual extrema approximately [{float(actual_low):.17g}, {float(actual_high):.17g}], "
                  f"literal bounds {'PASS' if valid else 'FAIL'}")
        for label, _, values, qnum, qden, printed, tolerance in path_reports:
            scaled = (len(values) - 1) * qnum
            index, remainder = divmod(scaled, qden)
            fraction = Fraction(remainder, qden)
            actual = (1 - fraction) * values[index] + fraction * values[index + 1]
            print(f"path {label}: actual approximately {float(actual):.17g}, "
                  f"printed {float(printed):.17g}, precision "
                  f"{'PASS' if abs(actual - printed) <= tolerance else 'FAIL'}")
        log_bounds = {int(q): (lower, upper)
            for q, _, _, lower, upper in sample_size_log_certificates}
        for name, means in [("likelihood", balanced_gap_means), ("logfit", balanced_logfit_means)]:
            intervals = [(value * log_bounds[cell[2]][0], value * log_bounds[cell[2]][1])
                for cell, value in zip(sorted(by_summary_cell), means)]
            low_index = min(range(len(intervals)), key=lambda i: intervals[i][0])
            high_index = max(range(len(intervals)), key=lambda i: intervals[i][1])
            print(f"scaled {name}: minimum index {low_index}, enclosure "
                  f"[{float(intervals[low_index][0]):.17g}, {float(intervals[low_index][1]):.17g}]; "
                  f"maximum index {high_index}, enclosure "
                  f"[{float(intervals[high_index][0]):.17g}, {float(intervals[high_index][1]):.17g}]")

    lines = [
        "/- This file is generated by scripts/generate_numerical_data.py. -/",
        "import Mathlib.Data.Rat.Lemmas",
        "import Mathlib.Data.List.Basic",
        "import ReweightedNPMLE.NumericalLogBounds",
        "",
        "namespace ReweightedNPMLE.NumericalStudy",
        "",
        "set_option maxRecDepth 100000",
        "set_option maxHeartbeats 10000000",
        "",
    ]
    for filename, digest in hashes:
        stem = Path(filename).stem.replace("_", " ").title().replace(" ", "")
        lines.append(f'def sha256{stem} : String := "{digest}"')
    lines.extend([
        "",
        "/-- `(ordinary, balanced, tiny)` resolved supports for every paired replication. -/",
        "def supportTriples : List (Nat × Nat × Nat) := [",
    ])
    lines.extend(f"  ({ordinary}, {balanced}, {tiny})," for ordinary, balanced, tiny in triples)
    lines.extend([
        "]",
        "",
        "/-- Per-fit flags `(converged, KKT gap < 2e-6, raw ordinary gap >= -1e-4)`. -/",
        "def diagnosticFlags : List (Bool × Bool × Bool) := [",
    ])
    lines.extend(
        f"  ({str(converged).lower()}, {str(kkt).lower()}, {str(gap).lower()}),"
        for converged, kkt, gap in diagnostic_flags
    )
    lines.extend([
        "]",
        "",
        "/-- KKT flags for the 3,680 one-dimensional Monte Carlo/path fits. -/",
        "def oneDimensionalKktFlags : List Bool := [",
    ])
    lines.extend(f"  {str(flag).lower()}," for flag in one_dimensional_kkt_flags)
    lines.extend([
        "]",
        "",
        "/-- `(same support, H² to reference, KKT gap)` for 20 dispersed starts. -/",
        "def multistartDiagnostics : List (Bool × ℚ × ℚ) := [",
    ])
    lines.extend(
        f"  ({str(same).lower()}, {lean_rat(hellinger)}, {lean_rat(kkt)}),"
        for same, hellinger, kkt in multistart_diagnostics
    )
    lines.extend([
        "]",
        "",
        "/-- Reported log-log slopes in the order weight, H², likelihood, log-fit². -/",
        "def pathMedianLogLogSlopes : List ℚ := [",
    ])
    lines.extend(f"  {lean_rat(value)}," for value in path_slopes)
    for name, values in [
        ("balancedRiskRatios", balanced_risk_ratios),
        ("tinyRiskRatios", tiny_risk_ratios),
        ("bbRiskRatios", bb_risk_ratios),
        ("balancedMeanSupportDifferences", balanced_support_differences),
        ("balancedMeanHellingerToOrdinary", balanced_hellinger_means),
        ("tinyMeanHellingerToOrdinary", tiny_hellinger_means),
        ("balancedMeanOrdinaryLoglikGap", balanced_gap_means),
        ("bbMeanOrdinaryLoglikGap", bb_gap_means),
        ("balancedMeanLogfitSqSum", balanced_logfit_means),
    ]:
        lines.extend(["]", "", f"def {name} : List ℚ := ["])
        lines.extend(f"  {lean_rat(value)}," for value in values)
    lines.append("]")
    lines.extend([
        "", "def numericalSampleSizeLogCertificates : List NumericalLogCertificate := [",
    ])
    for q, inverse, exponent, lower, upper in sample_size_log_certificates:
        lines.append(f"  ⟨{lean_rat(q)}, {str(inverse).lower()}, {exponent}, "
                     f"{lean_rat(lower)}, {lean_rat(upper)}⟩,")
    lines.extend([
        "]", "", "/-- `(sample size, balanced mean likelihood loss, balanced mean log-fit²)`. -/",
        "def numericalScaledCells : List (Nat × ℚ × ℚ) := [",
    ])
    for (_, _, n), gap, logfit in zip(sorted(by_summary_cell), balanced_gap_means, balanced_logfit_means):
        lines.append(f"  ({n}, {lean_rat(gap)}, {lean_rat(logfit)}),")
    lines.append("]")
    for name, values in [("tableMeanCertificates", table_means),
                         ("tableStandardErrorSqCertificates", table_standard_errors)]:
        lines.extend(["", f"def {name} : List (String × ℚ × ℚ × ℚ) := ["])
        lines.extend(f"  ({json.dumps(label)}, {lean_rat(actual)}, {lean_rat(low)}, {lean_rat(high)}),"
                     for label, actual, low, high in values)
        lines.append("]")
    lines.extend(["", "def tableRawSamples : List (String × List ℚ) := ["])
    for label, values in table_raw_samples:
        lines.append(f"  ({json.dumps(label)}, [")
        lines.extend(f"    {lean_rat(value)}," for value in values)
        lines.append("  ]),")
    lines.append("]")
    lines.extend([
        "", "structure NumericalRangeReport where",
        "  label : String", "  samples : List ℚ",
        "  lower : ℚ", "  upper : ℚ", "  lowerTolerance : ℚ", "  upperTolerance : ℚ",
        "", "def numericalRangeReports : List NumericalRangeReport := [",
    ])
    for name, definition, _, low, high, low_tolerance, high_tolerance in printed_ranges:
        fields = [json.dumps(name), definition] + [lean_rat(Fraction(value))
            for value in (low, high, low_tolerance, high_tolerance)]
        lines.append(f"  ⟨{', '.join(fields)}⟩,")
    lines.append("]")
    lines.extend(["", "def pathRawSamples : List (String × List ℚ) := ["])
    for label, values in path_samples:
        lines.append(f"  ({json.dumps(label)}, [")
        lines.extend(f"    {lean_rat(value)}," for value in values)
        lines.append("  ]),")
    lines.extend([
        "]", "", "structure NumericalPathReport where",
        "  label : String", "  permutation : List Nat", "  sortedSamples : List ℚ",
        "  quantileNumerator : Nat", "  quantileDenominator : Nat",
        "  printed : ℚ", "  tolerance : ℚ",
        "", "def numericalPathReports : List NumericalPathReport := [",
    ])
    for label, permutation, values, qnum, qden, printed, tolerance in path_reports:
        indices = ", ".join(str(i) for i in permutation)
        lines.append(f"  ⟨{json.dumps(label)}, [{indices}], [")
        lines.extend(f"    {lean_rat(value)}," for value in values)
        lines.append(f"  ], {qnum}, {qden}, {lean_rat(printed)}, {lean_rat(tolerance)}⟩,")
    lines.append("]")
    lines.extend(["", "def numericalDesignCounts : List (String × Nat × Nat × Nat) := ["])
    lines.extend(f"  ({json.dumps(scenario)}, {dimension}, {sample_size}, {count}),"
                 for scenario, dimension, sample_size, count in design_counts)
    lines.extend([
        "]", "", "def numericalPathDrawGroups : List (ℚ × List Nat) := [",
    ])
    for alpha, draws in sorted(path_draw_groups.items()):
        indices = ", ".join(str(draw) for draw in draws)
        lines.append(f"  ({lean_rat(alpha)}, [{indices}]),")
    lines.extend([
        "]", "", f"def numericalPathOrdinaryRisk : ℚ := {lean_rat(Fraction(path_rows[0]['ordinary_hellinger_to_truth']))}",
        f"def numericalPathBalancedAlpha : ℚ := {lean_rat(Fraction(path_rows[0]['balanced_alpha']))}",
    ])
    batch_names = []
    for start in range(0, len(all_rows), 50):
        name = f"numericalRawFitDiagnosticsBatch{start // 50}"
        batch_names.append(name)
        lines.extend(["", f"@[simp] private def {name} : List (Nat × ℚ × ℚ × Bool) := ["])
        for row in all_rows[start:start + 50]:
            dimension = int(row.get("dimension", "1"))
            converged = str(Fraction(row["converged"]) == 1).lower()
            lines.append(f"  ({dimension}, {lean_rat(Fraction(row['kkt_gap']))}, "
                         f"{lean_rat(Fraction(row['ordinary_loglik_gap_raw']))}, {converged}),")
        lines.append("]")
    lines.extend([
        "", "/-- Raw `(dimension, KKT residual, ordinary gap, converged)` diagnostics. -/",
        "def numericalRawFitDiagnostics : List (Nat × ℚ × ℚ × Bool) :=",
        f"  [{', '.join(batch_names)}].flatten",
    ])
    lines.extend(["", "end ReweightedNPMLE.NumericalStudy", ""])
    certificate = "\n".join(lines)
    regression_data, regression_audits = regression_certificate(path_rows, hashes)
    summary_data = summary_samples(by_summary_cell, hashes)
    if audit:
        for metric, enclosure, printed in regression_audits:
            valid = printed - Fraction(1, 2000) <= enclosure[0] and enclosure[1] <= printed + Fraction(1, 2000)
            print(f"raw-data OLS {metric}: enclosure approximately "
                  f"[{float(enclosure[0]):.17g}, {float(enclosure[1]):.17g}], "
                  f"printed precision {'PASS' if valid else 'FAIL'}")
    if check:
        if OUTPUT.read_text(encoding="utf-8") != certificate:
            raise SystemExit("Numerical Lean certificate does not match the source data")
        if not REGRESSION_OUTPUT.exists() or REGRESSION_OUTPUT.read_text(encoding="utf-8") != regression_data:
            raise SystemExit("Regression Lean certificate does not match the source data")
        if not SUMMARY_OUTPUT.exists() or SUMMARY_OUTPUT.read_text(encoding="utf-8") != summary_data:
            raise SystemExit("Summary Lean samples do not match the source data")
        print("All three numerical Lean artifacts exactly match all six source files")
    else:
        for output, content in [(OUTPUT, certificate), (REGRESSION_OUTPUT, regression_data),
                                (SUMMARY_OUTPUT, summary_data)]:
            if not output.exists() or output.read_text(encoding="utf-8") != content:
                output.write_text(content, encoding="utf-8")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="verify without changing files")
    parser.add_argument("--audit-numerics", action="store_true", help="audit printed ranges using exact source rationals")
    args = parser.parse_args()
    if args.audit_numerics and not args.check:
        parser.error("--audit-numerics requires --check to preserve the certificate")
    main(check=args.check, audit=args.audit_numerics)
