import CatalanAnchor.Series
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! Exact alternating-series bounds for the series defining Catalan's constant. -/

noncomputable section

open Filter Topology

namespace CatalanAnchor

/-- The positive magnitude of the `n`th Catalan-series term. -/
def magnitude (n : ℕ) : ℝ := 1 / (2 * (n : ℝ) + 1) ^ 2

/-- A finite partial sum, containing precisely `n` terms. -/
def partialSum (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, term k

theorem magnitude_antitone : Antitone magnitude := by
  intro m n hmn
  dsimp [magnitude]
  apply one_div_le_one_div_of_le (by positivity)
  gcongr

theorem magnitude_summable : Summable magnitude := by
  convert term_summable.norm using 1
  ext n
  simp [term, magnitude, norm_div, norm_pow,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ) + 1)]

theorem partialSum_tendsto : Tendsto partialSum atTop (𝓝 catalan) := by
  exact hasSum_catalan.tendsto_sum_nat

private theorem alternating_partialSum_tendsto :
    Tendsto (fun n => ∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * magnitude k)
      atTop (𝓝 catalan) := by
  have ht : Tendsto (fun n => ∑ k ∈ Finset.range n, term k)
      atTop (𝓝 catalan) := hasSum_catalan.tendsto_sum_nat
  simpa [term, magnitude, div_eq_mul_inv] using ht

/-- Every even partial sum is a certified lower bound. -/
theorem partialSum_even_le_catalan (n : ℕ) : partialSum (2 * n) ≤ catalan := by
  simpa [partialSum, term, magnitude, div_eq_mul_inv] using
    Antitone.alternating_series_le_tendsto alternating_partialSum_tendsto
      magnitude_antitone n

/-- Every odd partial sum is a certified upper bound. -/
theorem catalan_le_partialSum_odd (n : ℕ) : catalan ≤ partialSum (2 * n + 1) := by
  simpa [partialSum, term, magnitude, div_eq_mul_inv] using
    Antitone.tendsto_le_alternating_series alternating_partialSum_tendsto
      magnitude_antitone n

/-- The next positive term bounds the absolute error at every finite stage. -/
theorem partialSum_error_bound (n : ℕ) :
    |catalan - partialSum n| ≤ 1 / (2 * (n : ℝ) + 1) ^ 2 := by
  simpa [catalan, partialSum, term, magnitude, div_eq_mul_inv] using
    alternating_series_error_bound magnitude magnitude_antitone magnitude_summable n

theorem eight_ninths_lt_catalan : (8 : ℝ) / 9 < catalan := by
  have h := partialSum_even_le_catalan 2
  norm_num [partialSum, term, Finset.sum_range_succ] at h
  linarith

theorem catalan_lt_one : catalan < 1 := by
  have h := catalan_le_partialSum_odd 1
  norm_num [partialSum, term, Finset.sum_range_succ] at h
  linarith

theorem catalan_pos : 0 < catalan := by
  linarith [eight_ninths_lt_catalan]

/-- A small exact rational enclosure obtained from four and three terms. -/
theorem catalan_finite_enclosure :
    (10016 : ℝ) / 11025 ≤ catalan ∧ catalan ≤ (209 : ℝ) / 225 := by
  constructor
  · have h := partialSum_even_le_catalan 2
    norm_num [partialSum, term, Finset.sum_range_succ] at h ⊢
    exact h
  · have h := catalan_le_partialSum_odd 1
    norm_num [partialSum, term, Finset.sum_range_succ] at h ⊢
    exact h

end CatalanAnchor
