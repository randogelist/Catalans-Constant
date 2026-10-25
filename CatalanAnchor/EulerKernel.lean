import CatalanAnchor.Integral

/-! Positive Euler moments and a finite geometric enclosure of Catalan's constant. -/

noncomputable section
open MeasureTheory Set Filter

namespace CatalanAnchor

def eulerMoment (n : ℕ) : ℝ :=
  squareIntegral (fun x y => (1 - (x * y) ^ 2) ^ n)

def eulerSingleMoment (n : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..1, (1 - x ^ 2) ^ n

def eulerA (n : ℕ) : ℝ := eulerMoment n / (2 : ℝ) ^ (n + 1)

def eulerU (n : ℕ) : ℝ := eulerSingleMoment n / (2 : ℝ) ^ (n + 1)

def eulerPartial (N : ℕ) : ℝ := ∑ k ∈ Finset.range N, eulerA k

private def EulerSquareContinuous (f : ℝ → ℝ → ℝ) : Prop :=
  Continuous fun p : ℝ × ℝ => f p.1 p.2

private theorem euler_continuous_inner {f : ℝ → ℝ → ℝ}
    (hf : EulerSquareContinuous f) :
    Continuous fun x => ∫ y in (0 : ℝ)..1, f x y :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hf 0 1

private theorem euler_continuous_slice {f : ℝ → ℝ → ℝ}
    (hf : EulerSquareContinuous f) (x : ℝ) : Continuous (f x) :=
  hf.comp (continuous_const.prodMk continuous_id)

private theorem euler_square_congr {f g : ℝ → ℝ → ℝ}
    (h : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, f x y = g x y) :
    squareIntegral f = squareIntegral g := by
  apply intervalIntegral.integral_congr
  intro x hx
  apply intervalIntegral.integral_congr
  intro y hy
  exact h x (by simpa using hx) y (by simpa using hy)

private theorem euler_square_sub {f g : ℝ → ℝ → ℝ}
    (hf : EulerSquareContinuous f) (hg : EulerSquareContinuous g) :
    squareIntegral (fun x y => f x y - g x y) = squareIntegral f - squareIntegral g := by
  unfold squareIntegral
  simp_rw [intervalIntegral.integral_sub
    ((euler_continuous_slice hf _).intervalIntegrable 0 1)
    ((euler_continuous_slice hg _).intervalIntegrable 0 1)]
  exact intervalIntegral.integral_sub
    ((euler_continuous_inner hf).intervalIntegrable 0 1)
    ((euler_continuous_inner hg).intervalIntegrable 0 1)

private theorem euler_square_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ → ℝ)
    (hf : ∀ i ∈ s, EulerSquareContinuous (f i)) :
    squareIntegral (fun x y => ∑ i ∈ s, f i x y) = ∑ i ∈ s, squareIntegral (f i) := by
  unfold squareIntegral
  simp_rw [intervalIntegral.integral_finsetSum
    (fun i hi => (euler_continuous_slice (hf i hi) _).intervalIntegrable 0 1)]
  exact intervalIntegral.integral_finsetSum
    (fun i hi => (euler_continuous_inner (hf i hi)).intervalIntegrable 0 1)

private theorem euler_square_nonneg {f : ℝ → ℝ → ℝ}
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, 0 ≤ f x y) :
    0 ≤ squareIntegral f := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro x hx
  exact intervalIntegral.integral_nonneg (by norm_num) (hf x hx)

private theorem euler_square_mono {f g : ℝ → ℝ → ℝ}
    (hf : EulerSquareContinuous f) (hg : EulerSquareContinuous g)
    (h : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, f x y ≤ g x y) :
    squareIntegral f ≤ squareIntegral g := by
  apply intervalIntegral.integral_mono_on (by norm_num)
    ((euler_continuous_inner hf).intervalIntegrable 0 1)
    ((euler_continuous_inner hg).intervalIntegrable 0 1)
  intro x hx
  exact intervalIntegral.integral_mono_on (by norm_num)
    ((euler_continuous_slice hf x).intervalIntegrable 0 1)
    ((euler_continuous_slice hg x).intervalIntegrable 0 1) (h x hx)

private theorem euler_unit_square {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : x ^ 2 ≤ 1 := by
  nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]

private theorem euler_unit_product {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    x * y ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact mul_nonneg hx.1 hy.1
  · calc
      x * y ≤ 1 * y := mul_le_mul_of_nonneg_right hx.2 hy.1
      _ ≤ 1 := by simpa using hy.2

theorem eulerA_zero : eulerA 0 = 1 / 2 := by
  norm_num [eulerA, eulerMoment, squareIntegral]

theorem eulerU_zero : eulerU 0 = 1 / 2 := by
  norm_num [eulerU, eulerSingleMoment]

theorem eulerA_nonneg (n : ℕ) : 0 ≤ eulerA n := by
  unfold eulerA eulerMoment
  apply div_nonneg _ (by positivity)
  apply euler_square_nonneg
  intro x hx y hy
  exact pow_nonneg (sub_nonneg.mpr (euler_unit_square (euler_unit_product hx hy))) n

theorem eulerU_nonneg (n : ℕ) : 0 ≤ eulerU n := by
  unfold eulerU eulerSingleMoment
  apply div_nonneg _ (by positivity)
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro x hx
  exact pow_nonneg (sub_nonneg.mpr (euler_unit_square hx)) n

private theorem euler_finite_geometric (N : ℕ) (u : ℝ) (hu : 1 + u ≠ 0) :
    1 / (1 + u) - (∑ k ∈ Finset.range N, (1 - u) ^ k / (2 : ℝ) ^ (k + 1)) =
      ((1 - u) / 2) ^ N / (1 + u) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, sub_add_eq_sub_sub, ih]
    simp only [div_pow, pow_succ]
    have htwo : (2 : ℝ) ^ N ≠ 0 := by positivity
    field_simp [hu, htwo]
    ring

private def eulerRemainderKernel (N : ℕ) (x y : ℝ) : ℝ :=
  ((1 - (x * y) ^ 2) / 2) ^ N / (1 + (x * y) ^ 2)

private theorem euler_catalan_kernel_continuous : EulerSquareContinuous catalanKernel := by
  unfold EulerSquareContinuous catalanKernel
  apply continuous_const.div (by fun_prop)
  intro p
  positivity

private theorem euler_remainder_continuous (N : ℕ) :
    EulerSquareContinuous (eulerRemainderKernel N) := by
  unfold EulerSquareContinuous eulerRemainderKernel
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro p
  positivity

private theorem euler_remainder_identity (N : ℕ) :
    catalan - eulerPartial N = squareIntegral (eulerRemainderKernel N) := by
  have hc : ∀ k ∈ Finset.range N, EulerSquareContinuous
      (fun x y : ℝ => (1 - (x * y) ^ 2) ^ k / (2 : ℝ) ^ (k + 1)) := by
    intro k hk
    unfold EulerSquareContinuous
    fun_prop
  have hs : squareIntegral (fun x y : ℝ =>
      ∑ k ∈ Finset.range N, (1 - (x * y) ^ 2) ^ k / (2 : ℝ) ^ (k + 1)) =
      eulerPartial N := by
    rw [euler_square_sum _ _ hc]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [eulerA, eulerMoment, squareIntegral, intervalIntegral.integral_div]
  have hcat : squareIntegral catalanKernel = catalan :=
    CATALAN_DOUBLE_INTEGRAL_IDENTIFIED.symm
  rw [← hcat, ← hs, ← euler_square_sub euler_catalan_kernel_continuous
    (by unfold EulerSquareContinuous; fun_prop)]
  apply euler_square_congr
  intro x hx y hy
  exact euler_finite_geometric N ((x * y) ^ 2) (by positivity)

private theorem euler_remainder_bounds (N : ℕ) :
    0 ≤ squareIntegral (eulerRemainderKernel N) ∧
      squareIntegral (eulerRemainderKernel N) ≤ (1 / 2 : ℝ) ^ N := by
  have hpoint : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      0 ≤ eulerRemainderKernel N x y ∧ eulerRemainderKernel N x y ≤ (1 / 2 : ℝ) ^ N := by
    intro x hx y hy
    have hsq := euler_unit_square (euler_unit_product hx hy)
    have hbase : 0 ≤ (1 - (x * y) ^ 2) / 2 := by nlinarith
    have hbase_le : (1 - (x * y) ^ 2) / 2 ≤ (1 / 2 : ℝ) := by
      nlinarith [sq_nonneg (x * y)]
    constructor
    · exact div_nonneg (pow_nonneg hbase N) (by positivity)
    · calc
        eulerRemainderKernel N x y ≤ ((1 - (x * y) ^ 2) / 2) ^ N := by
          exact div_le_self (pow_nonneg hbase N) (by nlinarith [sq_nonneg (x * y)])
        _ ≤ (1 / 2 : ℝ) ^ N := pow_le_pow_left₀ hbase hbase_le N
  constructor
  · exact euler_square_nonneg (fun x hx y hy => (hpoint x hx y hy).1)
  · have hm := euler_square_mono (euler_remainder_continuous N)
      (show EulerSquareContinuous (fun _ _ : ℝ => (1 / 2 : ℝ) ^ N) from continuous_const)
      (fun x hx y hy => (hpoint x hx y hy).2)
    simpa [squareIntegral] using hm

theorem euler_partial_le_catalan (N : ℕ) : eulerPartial N ≤ catalan := by
  have h := (euler_remainder_bounds N).1
  rw [← euler_remainder_identity] at h
  linarith

theorem catalan_le_euler_partial_add (N : ℕ) :
    catalan ≤ eulerPartial N + (1 / 2 : ℝ) ^ N := by
  have h := (euler_remainder_bounds N).2
  rw [← euler_remainder_identity] at h
  linarith

end CatalanAnchor
