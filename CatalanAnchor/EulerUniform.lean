import CatalanAnchor.EulerAnalytic
import CatalanAnchor.EulerFixedPoint

/-!
Uniform integer enclosures of Catalan's constant at every requested precision.
The extra twelve decimal places are guard digits; the analytic and rounding
estimates are proved for every natural precision, rather than replayed as data.
-/

namespace CatalanAnchor.EulerUniform

def workScale (p : ℕ) : ℕ := 10 ^ (p + 12)
def terms (p : ℕ) : ℕ := 4 * (p + 12)
def lower (p : ℕ) : ℕ := EulerFixedPoint.fixedSum (workScale p) (terms p)
def upper (p : ℕ) : ℕ := lower p + 3 * terms p + 1

theorem workScale_pos (p : ℕ) : 0 < workScale p := by
  unfold workScale
  positivity

theorem workScale_even (p : ℕ) : 2 ∣ workScale p := by
  exact (show (2 : ℕ) ∣ 10 by norm_num).pow (by omega : p + 12 ≠ 0)

/-- Four binary Euler steps per decimal guard digit bound the scaled tail by one. -/
theorem tail_bound (p : ℕ) :
    (workScale p : ℝ) * (1 / 2 : ℝ) ^ terms p ≤ 1 := by
  unfold workScale terms
  push_cast
  rw [pow_mul, ← mul_pow]
  exact pow_le_one₀ (by norm_num) (by norm_num)

theorem lower_le_upper (p : ℕ) : lower p ≤ upper p := by
  unfold upper
  omega

/-- The integer replay encloses the series-defined Catalan constant uniformly. -/
theorem scaled_enclosure (p : ℕ) :
    (lower p : ℝ) ≤ (workScale p : ℝ) * catalan ∧
      (workScale p : ℝ) * catalan ≤ (upper p : ℝ) := by
  have hr := EulerFixedPoint.recurrence_rounding
    (workScale p) (workScale_even p) eulerU eulerA
    eulerU_zero eulerA_zero eulerU_succ eulerA_succ
  have he := EulerFixedPoint.scaled_enclosure
    (workScale p) (terms p) eulerA catalan ((1 / 2 : ℝ) ^ terms p)
    (fun n => (hr n).2)
    (euler_partial_le_catalan (terms p))
    (catalan_le_euler_partial_add (terms p))
  constructor
  · exact he.1
  · have ht := tail_bound p
    have hu : (upper p : ℝ) = (lower p : ℝ) + 3 * (terms p : ℝ) + 1 := by
      simp only [upper, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    rw [hu]
    change (workScale p : ℝ) * catalan ≤
      (EulerFixedPoint.fixedSum (workScale p) (terms p) : ℝ) + 3 * (terms p : ℝ) + 1
    linarith [he.2]

end CatalanAnchor.EulerUniform
