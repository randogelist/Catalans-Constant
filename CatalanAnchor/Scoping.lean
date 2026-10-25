import CatalanAnchor.HurwitzBridge
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

/-!
# Integer linear forms: finite scope and conditional irrationality

This module proves arithmetic implications only. A single positive integer
linear form below `1 / d` excludes rational representations with denominator
at most `d`. An explicit family of positive, arbitrarily small integer linear
forms implies irrationality. No such family for Catalan's constant is asserted
to exist here.

The generic criterion is independently restated in the `CatalanAnchor`
namespace from the project's integer-linear-form argument. This module does
not import a zeta irrationality result.
-/

namespace CatalanAnchor

/-- Positive integer multiples cannot be arbitrarily small. -/
theorem NO_POSITIVE_SMALL_INTEGER_MULTIPLES
    (L : ℕ → ℝ) (d : ℕ) (hd : 0 < d)
    (hpositive : ∀ n, 0 < L n)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ n, L n < ε)
    (hinteger : ∀ n, ∃ m : ℤ, (d : ℝ) * L n = (m : ℝ)) : False := by
  have hdreal : 0 < (d : ℝ) := by exact_mod_cast hd
  obtain ⟨n, hn⟩ := hsmall (1 / (d : ℝ)) (by positivity)
  obtain ⟨m, hm⟩ := hinteger n
  have hm0 : (0 : ℝ) < (m : ℝ) := by
    rw [← hm]
    exact mul_pos hdreal (hpositive n)
  have hm1 : (m : ℝ) < 1 := by
    rw [← hm]
    calc
      (d : ℝ) * L n < (d : ℝ) * (1 / (d : ℝ)) :=
        mul_lt_mul_of_pos_left hn hdreal
      _ = 1 := by field_simp [ne_of_gt hdreal]
  have hmpos : (0 : ℤ) < m := by exact_mod_cast hm0
  have hmlt : m < (1 : ℤ) := by exact_mod_cast hm1
  omega

/-- Positive, arbitrarily small integer linear forms imply irrationality. -/
theorem IRRATIONAL_OF_INTEGER_LINEAR_FORMS
    (x : ℝ) (A B : ℕ → ℤ)
    (hpositive : ∀ n, 0 < (A n : ℝ) * x + (B n : ℝ))
    (hsmall : ∀ ε : ℝ, 0 < ε →
      ∃ n, (A n : ℝ) * x + (B n : ℝ) < ε) : Irrational x := by
  intro hx
  obtain ⟨q, hq⟩ := hx
  have hd : 0 < q.den := Nat.pos_of_ne_zero (Rat.den_nz q)
  let L : ℕ → ℝ := fun n => (A n : ℝ) * x + (B n : ℝ)
  apply NO_POSITIVE_SMALL_INTEGER_MULTIPLES L q.den hd
    (by simpa only [L] using hpositive)
    (by simpa only [L] using hsmall)
  intro n
  refine ⟨A n * q.num + B n * (q.den : ℤ), ?_⟩
  have hmul : (q.den : ℝ) * (q : ℝ) = (q.num : ℝ) := by
    exact_mod_cast (Rat.den_mul_eq_num q)
  change (q.den : ℝ) * ((A n : ℝ) * x + (B n : ℝ)) =
    ((A n * q.num + B n * (q.den : ℤ) : ℤ) : ℝ)
  rw [← hq]
  calc
    (q.den : ℝ) * ((A n : ℝ) * (q : ℝ) + (B n : ℝ)) =
        (A n : ℝ) * ((q.den : ℝ) * (q : ℝ)) +
          (B n : ℝ) * (q.den : ℝ) := by ring
    _ = ((A n * q.num + B n * (q.den : ℤ) : ℤ) : ℝ) := by
      rw [hmul]
      push_cast
      ring

/-- A single sufficiently small positive integer form excludes every rational
number whose reduced denominator is at most the stated bound. This finite
conclusion is not an assertion of irrationality. -/
theorem INTEGER_LINEAR_FORM_DENOMINATOR_SCOPE
    (x : ℝ) (A B : ℤ) (d : ℕ) (hd : 1 ≤ d)
    (hpositive : 0 < (A : ℝ) * x + (B : ℝ))
    (hsmall : (A : ℝ) * x + (B : ℝ) < 1 / (d : ℝ)) :
    ∀ q : ℚ, q.den ≤ d → (q : ℝ) ≠ x := by
  intro q hden hq
  have hdreal : 0 < (d : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hqdenreal : 0 < (q.den : ℝ) := by
    exact_mod_cast (Nat.pos_of_ne_zero (Rat.den_nz q))
  have hdenreal : (q.den : ℝ) ≤ (d : ℝ) := by exact_mod_cast hden
  have hmul : (q.den : ℝ) * (q : ℝ) = (q.num : ℝ) := by
    exact_mod_cast (Rat.den_mul_eq_num q)
  let m : ℤ := A * q.num + B * (q.den : ℤ)
  have hm : (q.den : ℝ) * ((A : ℝ) * x + (B : ℝ)) = (m : ℝ) := by
    rw [← hq]
    calc
      (q.den : ℝ) * ((A : ℝ) * (q : ℝ) + (B : ℝ)) =
          (A : ℝ) * ((q.den : ℝ) * (q : ℝ)) +
            (B : ℝ) * (q.den : ℝ) := by ring
      _ = (m : ℝ) := by
        rw [hmul]
        dsimp [m]
        push_cast
        ring
  have hm0 : (0 : ℝ) < (m : ℝ) := by
    rw [← hm]
    exact mul_pos hqdenreal hpositive
  have hm1 : (m : ℝ) < 1 := by
    rw [← hm]
    calc
      (q.den : ℝ) * ((A : ℝ) * x + (B : ℝ)) ≤
          (d : ℝ) * ((A : ℝ) * x + (B : ℝ)) :=
        mul_le_mul_of_nonneg_right hdenreal (le_of_lt hpositive)
      _ < (d : ℝ) * (1 / (d : ℝ)) :=
        mul_lt_mul_of_pos_left hsmall hdreal
      _ = 1 := by field_simp [ne_of_gt hdreal]
  have hmpos : (0 : ℤ) < m := by exact_mod_cast hm0
  have hmlt : m < (1 : ℤ) := by exact_mod_cast hm1
  omega

/-- The explicit arithmetic input needed by the irrationality criterion.
Constructing this structure for Catalan's constant remains a separate task. -/
structure IntegerLinearFormsWitness (x : ℝ) where
  A : ℕ → ℤ
  B : ℕ → ℤ
  positive : ∀ n, 0 < (A n : ℝ) * x + (B n : ℝ)
  arbitrarilySmall : ∀ ε : ℝ, 0 < ε →
    ∃ n, (A n : ℝ) * x + (B n : ℝ) < ε

/-- A proved implication from the explicit witness; no existence claim. -/
theorem IntegerLinearFormsWitness.irrational {x : ℝ}
    (W : IntegerLinearFormsWitness x) : Irrational x :=
  IRRATIONAL_OF_INTEGER_LINEAR_FORMS x W.A W.B W.positive W.arbitrarilySmall

/-- Finite denominator scope for the identified real Catalan constant. -/
theorem CATALAN_DENOMINATOR_SCOPE
    (A B : ℤ) (d : ℕ) (hd : 1 ≤ d)
    (hpositive : 0 < (A : ℝ) * catalan + (B : ℝ))
    (hsmall : (A : ℝ) * catalan + (B : ℝ) < 1 / (d : ℝ)) :
    ∀ q : ℚ, q.den ≤ d → (q : ℝ) ≠ catalan :=
  INTEGER_LINEAR_FORM_DENOMINATOR_SCOPE catalan A B d hd hpositive hsmall

/-- The same finite conclusion transported to the native scalar. -/
theorem NATIVE_CATALAN_DENOMINATOR_SCOPE
    (A B : ℤ) (d : ℕ) (hd : 1 ≤ d)
    (hpositive : 0 < (A : ℝ) * catalan + (B : ℝ))
    (hsmall : (A : ℝ) * catalan + (B : ℝ) < 1 / (d : ℝ)) :
    ∀ q : ℚ, q.den ≤ d → (q : ℝ) ≠ nativeCatalan := by
  rw [CATALAN_NATIVE_IDENTIFIED]
  exact CATALAN_DENOMINATOR_SCOPE A B d hd hpositive hsmall

/-- Catalan irrationality conditional on the explicit arithmetic witness. -/
theorem CATALAN_IRRATIONAL_OF_WITNESS
    (W : IntegerLinearFormsWitness catalan) : Irrational catalan :=
  W.irrational

/-- Native Catalan irrationality conditional on the same explicit witness. -/
theorem NATIVE_CATALAN_IRRATIONAL_OF_WITNESS
    (W : IntegerLinearFormsWitness catalan) : Irrational nativeCatalan := by
  rw [CATALAN_NATIVE_IDENTIFIED]
  exact W.irrational

end CatalanAnchor
