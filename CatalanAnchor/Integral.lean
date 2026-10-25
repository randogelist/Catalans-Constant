import CatalanAnchor.Series
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! A finite-remainder proof of the double-integral representation of Catalan's constant. -/

noncomputable section
open MeasureTheory Set Filter

namespace CatalanAnchor

def squareIntegral (f : ℝ → ℝ → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, f x y

private def SquareContinuous (f : ℝ → ℝ → ℝ) : Prop :=
  Continuous fun p : ℝ × ℝ => f p.1 p.2

private theorem continuous_inner {f : ℝ → ℝ → ℝ} (hf : SquareContinuous f) :
    Continuous fun x => ∫ y in (0 : ℝ)..1, f x y :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hf 0 1

private theorem continuous_slice {f : ℝ → ℝ → ℝ} (hf : SquareContinuous f) (x : ℝ) :
    Continuous (f x) :=
  hf.comp (continuous_const.prodMk continuous_id)

private theorem squareIntegral_congr {f g : ℝ → ℝ → ℝ}
    (h : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, f x y = g x y) :
    squareIntegral f = squareIntegral g := by
  apply intervalIntegral.integral_congr
  intro x hx
  apply intervalIntegral.integral_congr
  intro y hy
  exact h x (by simpa using hx) y (by simpa using hy)

private theorem squareIntegral_sub {f g : ℝ → ℝ → ℝ}
    (hf : SquareContinuous f) (hg : SquareContinuous g) :
    squareIntegral (fun x y => f x y - g x y) = squareIntegral f - squareIntegral g := by
  unfold squareIntegral
  simp_rw [intervalIntegral.integral_sub
    ((continuous_slice hf _).intervalIntegrable 0 1)
    ((continuous_slice hg _).intervalIntegrable 0 1)]
  exact intervalIntegral.integral_sub
    ((continuous_inner hf).intervalIntegrable 0 1)
    ((continuous_inner hg).intervalIntegrable 0 1)

private theorem squareIntegral_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ → ℝ)
    (hf : ∀ i ∈ s, SquareContinuous (f i)) :
    squareIntegral (fun x y => ∑ i ∈ s, f i x y) = ∑ i ∈ s, squareIntegral (f i) := by
  unfold squareIntegral
  simp_rw [intervalIntegral.integral_finsetSum
    (fun i hi => (continuous_slice (hf i hi) _).intervalIntegrable 0 1)]
  exact intervalIntegral.integral_finsetSum
    (fun i hi => (continuous_inner (hf i hi)).intervalIntegrable 0 1)

private theorem squareIntegral_nonneg {f : ℝ → ℝ → ℝ}
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, 0 ≤ f x y) :
    0 ≤ squareIntegral f := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro x hx
  exact intervalIntegral.integral_nonneg (by norm_num) (hf x hx)

private theorem squareIntegral_mono {f g : ℝ → ℝ → ℝ}
    (hf : SquareContinuous f) (hg : SquareContinuous g)
    (h : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, f x y ≤ g x y) :
    squareIntegral f ≤ squareIntegral g := by
  apply intervalIntegral.integral_mono_on (by norm_num)
    ((continuous_inner hf).intervalIntegrable 0 1)
    ((continuous_inner hg).intervalIntegrable 0 1)
  intro x hx
  exact intervalIntegral.integral_mono_on (by norm_num)
    ((continuous_slice hf x).intervalIntegrable 0 1)
    ((continuous_slice hg x).intervalIntegrable 0 1) (h x hx)

theorem squareIntegral_monomial (k : ℕ) :
    squareIntegral (fun x y => (x * y) ^ k) = 1 / (((k + 1 : ℕ) : ℝ) ^ 2) := by
  simp only [squareIntegral, mul_pow, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_mul_const, integral_pow]
  simp only [one_pow, zero_pow (Nat.succ_ne_zero k), sub_zero]
  push_cast
  field_simp

private theorem geometric_remainder (N : ℕ) (u : ℝ) (hu : 1 + u ≠ 0) :
    1 / (1 + u) - (∑ k ∈ Finset.range N, (-u) ^ k) = (-u) ^ N / (1 + u) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, sub_add_eq_sub_sub, ih, pow_succ]
    field_simp [hu]
    ring

def catalanKernel (x y : ℝ) : ℝ := 1 / (1 + (x * y) ^ 2)

private def remainderKernel (N : ℕ) (x y : ℝ) : ℝ :=
  (x * y) ^ (4 * N) / (1 + (x * y) ^ 2)

private theorem catalanKernel_continuous : SquareContinuous catalanKernel := by
  unfold SquareContinuous catalanKernel
  apply continuous_const.div (by fun_prop)
  intro p
  positivity

private theorem remainderKernel_continuous (N : ℕ) :
    SquareContinuous (remainderKernel N) := by
  unfold SquareContinuous remainderKernel
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro p
  positivity

private theorem squareIntegral_geometric_term (k : ℕ) :
    squareIntegral (fun x y => (-((x * y) ^ 2)) ^ k) = term k := by
  have hfun : (fun x y : ℝ => (-((x * y) ^ 2)) ^ k) =
      (fun x y : ℝ => (-1 : ℝ) ^ k * (x * y) ^ (2 * k)) := by
    funext x y
    rw [neg_pow, ← pow_mul]
  rw [hfun]
  have hmul : squareIntegral (fun x y : ℝ => (-1 : ℝ) ^ k * (x * y) ^ (2 * k)) =
      (-1 : ℝ) ^ k * squareIntegral (fun x y => (x * y) ^ (2 * k)) := by
    simp only [squareIntegral, intervalIntegral.integral_const_mul]
  rw [hmul, squareIntegral_monomial]
  simp [term, div_eq_mul_inv]

private theorem squareIntegral_even_remainder (N : ℕ) :
    squareIntegral catalanKernel - (∑ k ∈ Finset.range (2 * N), term k) =
      squareIntegral (remainderKernel N) := by
  have hc : ∀ k ∈ Finset.range (2 * N),
      SquareContinuous (fun x y : ℝ => (-((x * y) ^ 2)) ^ k) := by
    intro k hk
    unfold SquareContinuous
    fun_prop
  have hs : squareIntegral (fun x y : ℝ =>
      ∑ k ∈ Finset.range (2 * N), (-((x * y) ^ 2)) ^ k) =
      ∑ k ∈ Finset.range (2 * N), term k := by
    rw [squareIntegral_sum _ _ hc]
    exact Finset.sum_congr rfl (fun k hk => squareIntegral_geometric_term k)
  rw [← hs, ← squareIntegral_sub catalanKernel_continuous
    (by unfold SquareContinuous; fun_prop)]
  apply squareIntegral_congr
  intro x hx y hy
  have h := geometric_remainder (2 * N) ((x * y) ^ 2) (by positivity)
  have hp : (-((x * y) ^ 2)) ^ (2 * N) = (x * y) ^ (4 * N) := by
    rw [pow_mul, neg_sq, ← pow_mul, ← pow_mul]
    congr 1
    omega
  simpa only [catalanKernel, remainderKernel, hp] using h

private theorem remainderKernel_integral_bounds (N : ℕ) :
    0 ≤ squareIntegral (remainderKernel N) ∧
      squareIntegral (remainderKernel N) ≤ 1 / (((4 * N + 1 : ℕ) : ℝ) ^ 2) := by
  constructor
  · apply squareIntegral_nonneg
    intro x hx y hy
    unfold remainderKernel
    exact div_nonneg (pow_nonneg (mul_nonneg hx.1 hy.1) _) (by positivity)
  · rw [← squareIntegral_monomial]
    apply squareIntegral_mono (remainderKernel_continuous N)
      (by unfold SquareContinuous; fun_prop)
    intro x hx y hy
    unfold remainderKernel
    exact div_le_self (pow_nonneg (mul_nonneg hx.1 hy.1) _) (by nlinarith [sq_nonneg (x * y)])

theorem CATALAN_DOUBLE_INTEGRAL_IDENTIFIED :
    catalan = ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, 1 / (1 + (x * y) ^ 2) := by
  have htwo : Tendsto (fun N : ℕ => 2 * N) atTop atTop :=
    tendsto_atTop_mono (f := fun N : ℕ => N) (fun N => by omega) tendsto_id
  have hfour : Tendsto (fun N : ℕ => 4 * N) atTop atTop :=
    tendsto_atTop_mono (f := fun N : ℕ => N) (fun N => by omega) tendsto_id
  have hbound : Tendsto (fun N : ℕ => 1 / (((4 * N + 1 : ℕ) : ℝ) ^ 2))
      atTop (nhds 0) := by
    have h := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2).comp hfour
    simpa [Function.comp_def, div_pow] using h
  have hzero : Tendsto (fun N => squareIntegral (remainderKernel N)) atTop (nhds 0) :=
    squeeze_zero (fun N => (remainderKernel_integral_bounds N).1)
      (fun N => (remainderKernel_integral_bounds N).2) hbound
  have hpartial := hasSum_catalan.tendsto_sum_nat.comp htwo
  have hdifference : Tendsto
      (fun N => squareIntegral catalanKernel - ∑ k ∈ Finset.range (2 * N), term k)
      atTop (nhds (squareIntegral catalanKernel - catalan)) :=
    tendsto_const_nhds.sub hpartial
  simp_rw [squareIntegral_even_remainder] at hdifference
  have h := tendsto_nhds_unique hdifference hzero
  exact (sub_eq_zero.mp h).symm

end CatalanAnchor
