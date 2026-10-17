"""Translate recorded rational bounds to Lean arithmetic propositions.

This does not establish that the recorded numbers enclose an ODE solution.
The interval recurrence and its analytic interpretation are separate obligations.
"""
from pathlib import Path
from fractions import Fraction
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
INPUT = ROOT.parent / "verification/profile7/calabi7_ledger_1.json"
if not INPUT.exists():
    INPUT = ROOT.parent / "githubPDF/verification/profile7/calabi7_ledger_1.json"
LIMITS = {
    "product": "260000", "sum_products": "39000000", "weighted_sum": "127000000",
    "variation": "2.69", "origin_variation": ".00008", "q_linear": ".079",
    "identity_error": "1e-6", "jet_residual": "3e-14", "projected_residual": "1e-14",
    "d_row": ".00007",
}


def lean_rat(value):
    number = Fraction(value)
    return f"({number.numerator} / {number.denominator} : ℝ)"


def main():
    data = INPUT.read_bytes()
    record = json.loads(data)
    lines = ["import Mathlib.Basic.Real.Basic", "import Mathlib.Tactic.NormNum", "", "/-! Exact inequalities for the recorded rational ledger.",
             "These statements do not certify the ledger's derivation or the ODE. -/", "",
             "namespace Calabi.Certificate.Recorded", "",
             f"-- Input SHA256: {hashlib.sha256(data).hexdigest()}"]
    for name, limit in LIMITS.items():
        value = record["exact_bounds"][name]
        assert Fraction(value) < Fraction(limit)
        lines.extend([f"noncomputable def {name} : ℝ := {lean_rat(value)}", "",
                      f"theorem {name}_lt : {name} < {lean_rat(limit)} := by",
                      f"  norm_num [{name}]", ""])
    lines.append("end Calabi.Certificate.Recorded")
    dest = ROOT / "Calabi/Certificate/RecordedBounds.lean"
    dest.write_text("\n".join(lines) + "\n")
    kernel = ["import Init", "", "set_option exponentiation.threshold 1024", "",
              "namespace Calabi.Certificate.KernelChecks", "",
              "/-! Kernel arithmetic only. These checks do not derive the recorded ledger. -/", ""]
    for name, bound in LIMITS.items():
        value, limit = Fraction(record["exact_bounds"][name]), Fraction(bound)
        kernel.extend([
            f"theorem {name} : ({value.numerator} : Int) * {limit.denominator} <",
            f"    {limit.numerator} * {value.denominator} := by decide", ""])
    kernel.extend([
        "def tailNumerator (r : Int) : Int :=",
        "  -1404928 * r ^ 3 + 263424 * r ^ 2 * (10 ^ 12) -",
        "  18872 * r * (10 ^ 12) ^ 2 + (1404928 - 567) * (10 ^ 12) ^ 3", "",
        "theorem tail_negative : tailNumerator 1061676856305 < 0 := by decide",
        "theorem tail_positive : 0 < tailNumerator 1061676856304 := by decide", "",
        "theorem scale_positive : (0 : Int) < 2 ^ 384 := by decide", "",
        "end Calabi.Certificate.KernelChecks"])
    (ROOT / "Calabi/Certificate/KernelChecks.lean").write_text("\n".join(kernel) + "\n")
    print(f"Generated {len(LIMITS)} exact arithmetic checks.")


if __name__ == "__main__":
    main()
