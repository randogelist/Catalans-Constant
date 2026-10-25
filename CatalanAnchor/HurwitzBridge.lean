import CatalanAnchor.Series
import Mathlib.NumberTheory.LSeries.HurwitzZeta

/-! Identification with Mathlib's Hurwitz zeta values at rational shifts. -/

noncomputable section
namespace CatalanAnchor

def nativeComplex : ℂ :=
  (HurwitzZeta.hurwitzZeta (((1 / 4 : ℝ)) : UnitAddCircle) (2 : ℂ) -
    HurwitzZeta.hurwitzZeta (((3 / 4 : ℝ)) : UnitAddCircle) (2 : ℂ)) / 16

def nativeCatalan : ℝ := nativeComplex.re

private theorem scaled_hurwitz_term (n : ℕ) (b : ℝ) :
    (1 / ((n : ℂ) + ((b / 4 : ℝ) : ℂ)) ^ (2 : ℂ)) / 16 =
      1 / (4 * (n : ℂ) + (b : ℂ)) ^ 2 := by
  rw [Complex.cpow_two]
  have he : (n : ℂ) + ((b / 4 : ℝ) : ℂ) =
      (4 * (n : ℂ) + (b : ℂ)) / 4 := by push_cast; ring
  rw [he, div_pow, one_div_div]
  ring

theorem CATALAN_HURWITZ_IDENTIFIED : nativeComplex = (catalan : ℂ) := by
  have h₁ := (HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re
    (a := (1 / 4 : ℝ)) (s := (2 : ℂ)) (by norm_num) (by norm_num)).div_const 16
  have h₃ := (HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re
    (a := (3 / 4 : ℝ)) (s := (2 : ℂ)) (by norm_num) (by norm_num)).div_const 16
  have he : HasSum (fun n : ℕ => (term (2 * n) : ℂ))
      (HurwitzZeta.hurwitzZeta (((1 / 4 : ℝ)) : UnitAddCircle) (2 : ℂ) / 16) := by
    apply h₁.congr_fun
    intro n
    rw [scaled_hurwitz_term n 1]
    simp [term, pow_mul]
    ring
  have ho : HasSum (fun n : ℕ => (term (2 * n + 1) : ℂ))
      (-(HurwitzZeta.hurwitzZeta (((3 / 4 : ℝ)) : UnitAddCircle) (2 : ℂ) / 16)) := by
    apply h₃.neg.congr_fun
    intro n
    rw [scaled_hurwitz_term n 3]
    simp [term, pow_add, pow_mul]
    ring
  have hc : HasSum (fun n : ℕ => (term n : ℂ)) (catalan : ℂ) :=
    Complex.hasSum_ofReal.mpr hasSum_catalan
  have hn := HasSum.even_add_odd (f := fun n : ℕ => (term n : ℂ)) he ho
  calc
    nativeComplex =
        HurwitzZeta.hurwitzZeta (((1 / 4 : ℝ)) : UnitAddCircle) (2 : ℂ) / 16 +
          -(HurwitzZeta.hurwitzZeta (((3 / 4 : ℝ)) : UnitAddCircle) (2 : ℂ) / 16) := by
      unfold nativeComplex
      ring
    _ = (catalan : ℂ) := hn.unique hc

theorem CATALAN_NATIVE_IDENTIFIED : nativeCatalan = catalan := by
  unfold nativeCatalan
  rw [CATALAN_HURWITZ_IDENTIFIED]
  rfl

end CatalanAnchor
