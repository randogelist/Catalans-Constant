import CatalanAnchor.EulerAnalytic
import CatalanAnchor.EulerComputed

/-!
Unconditional replay of the saved finite certificate.  The analytic Euler
moments, integer rounding theorem, exact recurrence computation and affine
scope theorem are connected here without an interval hypothesis.
-/

noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 10000

namespace CatalanAnchor

open EulerFixedPoint EulerComputed

theorem euler_computed_scaled_enclosure :
    (fixedSum workScale terms : ℝ) ≤ (workScale : ℝ) * catalan ∧
      (workScale : ℝ) * catalan ≤ fixedSum workScale terms + 3 * terms + 1 := by
  have hr := recurrence_rounding workScale workScale_even eulerU eulerA
    eulerU_zero eulerA_zero eulerU_succ eulerA_succ
  have hs := scaled_enclosure workScale terms eulerA catalan ((1 / 2 : ℝ) ^ terms)
    (fun n => (hr n).2) (euler_partial_le_catalan terms)
    (catalan_le_euler_partial_add terms)
  have ht : (workScale : ℝ) * (1 / 2 : ℝ) ^ terms ≤ 1 := real_tail_checked.le
  exact ⟨hs.1, hs.2.trans (by linarith)⟩

/-- A strict 1000-place interval for the series-defined Catalan constant,
with no numeric or analytic hypothesis. -/
theorem CATALAN_INTERVAL_1000 : Certificate1000.Interval := by
  have hQ : (0 : ℝ) < workScale := by exact_mod_cast workScale_pos
  have hscale : (0 : ℝ) < Certificate1000.scale := by
    unfold Certificate1000.scale
    positivity
  have hs := euler_computed_scaled_enclosure
  have hlo : (Certificate1000.lo : ℝ) * (workScale : ℝ) <
      (fixedSum workScale terms : ℝ) * (Certificate1000.scale : ℝ) := by
    exact_mod_cast lower_checked
  have hhi : ((fixedSum workScale terms : ℝ) + 3 * (terms : ℝ) + 1) *
      (Certificate1000.scale : ℝ) < (Certificate1000.hi : ℝ) * (workScale : ℝ) := by
    exact_mod_cast upper_checked
  constructor
  · exact ((div_lt_div_iff₀ hscale hQ).mpr hlo).trans_le
      ((div_le_iff₀ hQ).mpr (by simpa [mul_comm] using hs.1))
  · exact ((le_div_iff₀ hQ).mpr (by simpa [mul_comm] using hs.2)).trans_lt
      ((div_lt_div_iff₀ hQ hscale).mpr hhi)

theorem CATALAN_LINEAR_FORM_1000 :
    0 < (Certificate1000.A : ℝ) * catalan + (Certificate1000.B : ℝ) ∧
      (Certificate1000.A : ℝ) * catalan + (Certificate1000.B : ℝ) <
        1 / (Certificate1000.bound : ℝ) :=
  CATALAN_LINEAR_FORM_1000_OF_INTERVAL CATALAN_INTERVAL_1000

/-- Every rational through the exact saved 501-digit denominator bound is
different from Catalan's constant. -/
theorem CATALAN_FINITE_SCOPE_1000 :
    ∀ q : ℚ, q.den ≤ Certificate1000.bound → (q : ℝ) ≠ catalan :=
  CATALAN_SCOPE_1000_OF_INTERVAL CATALAN_INTERVAL_1000

theorem NATIVE_CATALAN_FINITE_SCOPE_1000 :
    ∀ q : ℚ, q.den ≤ Certificate1000.bound → (q : ℝ) ≠ nativeCatalan :=
  NATIVE_CATALAN_SCOPE_1000_OF_INTERVAL CATALAN_INTERVAL_1000

/-- A concise weaker consequence with an easily stated denominator bound. -/
theorem NATIVE_CATALAN_FINITE_SCOPE_10_POW_500 (q : ℚ) (hq : q.den ≤ 10 ^ 500) :
    (q : ℝ) ≠ nativeCatalan :=
  NATIVE_CATALAN_FINITE_SCOPE_1000 q (hq.trans Certificate1000.bound_decimal_size.1)

end CatalanAnchor
