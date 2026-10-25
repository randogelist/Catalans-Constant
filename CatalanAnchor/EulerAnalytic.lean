import CatalanAnchor.EulerKernel

noncomputable section
open MeasureTheory Set
namespace CatalanAnchor

private theorem kernel_deriv (n : ℕ) (s x : ℝ) :
    HasDerivAt (fun y : ℝ => y * (1 - (s * y) ^ 2) ^ (n + 1))
      ((2 * (n : ℝ) + 3) * (1 - (s * x) ^ 2) ^ (n + 1) -
        2 * ((n : ℝ) + 1) * (1 - (s * x) ^ 2) ^ n) x := by
  have hb : HasDerivAt (fun y : ℝ => 1 - (s * y) ^ 2) (-2 * s ^ 2 * x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub (((hasDerivAt_id x).const_mul s).pow 2) using 1 <;>
      first | rfl | (try simp only [id_eq]; ring)
  convert (hasDerivAt_id x).mul (hb.pow (n + 1)) using 1 <;>
    first | rfl | (try simp only [id_eq, Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, pow_succ]; ring)

private theorem euler_inner_recurrence (n : ℕ) (s : ℝ) :
    (2 * (n : ℝ) + 3) * (∫ y in (0 : ℝ)..1, (1 - (s * y) ^ 2) ^ (n + 1)) -
      2 * ((n : ℝ) + 1) * (∫ y in (0 : ℝ)..1, (1 - (s * y) ^ 2) ^ n) =
      (1 - s ^ 2) ^ (n + 1) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy => kernel_deriv n s y)
    ((by fun_prop : Continuous (fun y : ℝ =>
      (2 * (n : ℝ) + 3) * (1 - (s * y) ^ 2) ^ (n + 1) -
      2 * ((n : ℝ) + 1) * (1 - (s * y) ^ 2) ^ n)).intervalIntegrable 0 1)
  rw [intervalIntegral.integral_sub
    ((by fun_prop : Continuous (fun y : ℝ =>
      (2 * (n : ℝ) + 3) * (1 - (s * y) ^ 2) ^ (n + 1))).intervalIntegrable 0 1)
    ((by fun_prop : Continuous (fun y : ℝ =>
      2 * ((n : ℝ) + 1) * (1 - (s * y) ^ 2) ^ n)).intervalIntegrable 0 1)] at h
  simpa only [intervalIntegral.integral_const_mul, mul_one, mul_zero, zero_pow,
    zero_mul, sub_zero, one_mul] using h



/-- The first moment obeys the elementary beta-integral recurrence. -/
theorem eulerSingleMoment_recurrence (n : ℕ) :
    (2 * (n : ℝ) + 3) * eulerSingleMoment (n + 1) =
      2 * ((n : ℝ) + 1) * eulerSingleMoment n := by
  have h := euler_inner_recurrence n 1
  simp only [one_mul, one_pow, sub_self, zero_pow (Nat.succ_ne_zero n)] at h
  exact sub_eq_zero.mp h

/-- Integrating the same derivative in the other variable gives the square moment. -/
theorem eulerMoment_recurrence (n : ℕ) :
    (2 * (n : ℝ) + 3) * eulerMoment (n + 1) =
      2 * ((n : ℝ) + 1) * eulerMoment n + eulerSingleMoment (n + 1) := by
  have hc (k : ℕ) :
      Continuous (fun x : ℝ => ∫ y in (0 : ℝ)..1, (1 - (x * y)^2)^k) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (by fun_prop) 0 1
  have hi := intervalIntegral.integral_congr (a := (0 : ℝ)) (b := 1) (μ := volume)
    (fun x hx => euler_inner_recurrence n x)
  rw [intervalIntegral.integral_sub
    (((hc (n + 1)).const_mul _).intervalIntegrable 0 1)
    (((hc n).const_mul _).intervalIntegrable 0 1)] at hi
  simp only [intervalIntegral.integral_const_mul] at hi
  change (2 * (n : ℝ) + 3) * eulerMoment (n + 1) -
      2 * ((n : ℝ) + 1) * eulerMoment n = eulerSingleMoment (n + 1) at hi
  linarith

/-- The scaled first Euler moment has a rational first-order update. -/
theorem eulerU_succ (n : ℕ) :
    eulerU (n + 1) = ((n : ℝ) + 1) * eulerU n / (2 * (n : ℝ) + 3) := by
  have h := eulerSingleMoment_recurrence n
  have hd : 2 * (n : ℝ) + 3 ≠ 0 := by positivity
  unfold eulerU
  rw [pow_succ (2 : ℝ) (n + 1)]
  field_simp
  nlinarith

/-- The scaled square moment is driven by the first Euler moment. -/
theorem eulerA_succ (n : ℕ) :
    eulerA (n + 1) =
      (((n : ℝ) + 1) * eulerA n + eulerU (n + 1)) / (2 * (n : ℝ) + 3) := by
  have h := eulerMoment_recurrence n
  have hd : 2 * (n : ℝ) + 3 ≠ 0 := by positivity
  unfold eulerA eulerU
  rw [pow_succ (2 : ℝ) (n + 1)]
  field_simp
  nlinarith

end CatalanAnchor
