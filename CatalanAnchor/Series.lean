import Mathlib.Analysis.PSeries
import Mathlib.Tactic

/-! The absolutely convergent real series defining Catalan's constant. -/

noncomputable section
namespace CatalanAnchor

def term (n : ℕ) : ℝ := (-1 : ℝ) ^ n / (2 * (n : ℝ) + 1) ^ 2

def catalan : ℝ := ∑' n : ℕ, term n

theorem term_summable : Summable term := by
  have hp : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have ho := hp.comp_injective (i := fun n : ℕ => 2 * n + 1)
    (by intro m n h; dsimp at h; omega)
  apply Summable.of_norm
  apply ho.congr
  intro n
  simp [term, norm_div, norm_pow, abs_of_nonneg (by positivity :
    (0 : ℝ) ≤ 2 * (n : ℝ) + 1)]

theorem hasSum_catalan : HasSum term catalan := term_summable.hasSum

theorem CATALAN_SERIES_IDENTIFIED :
    catalan = ∑' n : ℕ, (-1 : ℝ) ^ n / (2 * (n : ℝ) + 1) ^ 2 := rfl

end CatalanAnchor
