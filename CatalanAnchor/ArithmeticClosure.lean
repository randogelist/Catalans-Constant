import CatalanAnchor.CofinalClosure

/-!
An exact arithmetic formulation of the remaining Catalan continuation problem.
Every individual window is decidable using only integers and the finite Euler
recurrence. Exhaustion is a universal existence hypothesis, not a finite test.
-/

namespace CatalanAnchor.RieszAdmission

open GPBKQRXY.Riesz

/-- The finite strict margins used by the Catalan checker. -/
def IntegerWindow (k : ℕ) (B : ℤ) (q d : ℕ) : Prop :=
  0 < q ∧ 0 < d ∧
  0 < B * (EulerUniform.workScale k : ℤ) - (q : ℤ) * (EulerUniform.upper k : ℤ) ∧
  0 < B * (EulerUniform.workScale k : ℤ) - (q : ℤ) * (EulerUniform.lower k : ℤ) ∧
  (d : ℤ) * (B * (EulerUniform.workScale k : ℤ) -
    (q : ℤ) * (EulerUniform.lower k : ℤ)) < (EulerUniform.workScale k : ℤ)

instance (k : ℕ) (B : ℤ) (q d : ℕ) : Decidable (IntegerWindow k B q d) := by
  unfold IntegerWindow
  infer_instance

/-- The entire unresolved claim, expressed without a real-valued predicate. -/
def ArithmeticExhaustion : Prop :=
  ∀ d : ℕ, 0 < d → ∃ k : ℕ, ∃ B : ℤ, ∃ q : ℕ, IntegerWindow k B q d

def windowCoordinate (k : ℕ) (B : ℤ) (q d : ℕ) : Coordinates 3 where
  X := 1
  Y := 1
  stage := k
  state := ![(B : ℚ), (q : ℚ), (d : ℚ)]

@[simp] theorem windowCoordinate_numerator (k : ℕ) (B : ℤ) (q d : ℕ) :
    numerator (windowCoordinate k B q d) = B := by
  simp [numerator, windowCoordinate]

@[simp] theorem windowCoordinate_denominator (k : ℕ) (B : ℤ) (q d : ℕ) :
    denominator (windowCoordinate k B q d) = q := by
  simp [denominator, windowCoordinate]

@[simp] theorem windowCoordinate_scope (k : ℕ) (B : ℤ) (q d : ℕ) :
    scope (windowCoordinate k B q d) = d := by
  simp [scope, windowCoordinate]

theorem windowCoordinate_compatible_iff (k : ℕ) (B : ℤ) (q d : ℕ) :
    Compatible (windowCoordinate k B q d) ↔ IntegerWindow k B q d := by
  simp [Compatible, Canonical, lowerNumerator, upperNumerator,
    windowCoordinate, numerator, denominator, scope, IntegerWindow]

theorem windowCoordinate_admissible (k : ℕ) (B : ℤ) (q d : ℕ)
    (h : IntegerWindow k B q d) :
    Admissible (system id) (windowCoordinate k B q d) := by
  refine ⟨decide_eq_true ((windowCoordinate_compatible_iff k B q d).mpr h),
    ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [windowCoordinate]
  · norm_num [windowCoordinate]
  · change (0 : ℚ) < 1 / (scope (windowCoordinate k B q d) : ℚ)
    rw [windowCoordinate_scope]
    have hd : (0 : ℚ) < d := by exact_mod_cast h.2.1
    positivity
  · norm_num [system]
  · norm_num [system]

theorem compatible_integerWindow {c : Coordinates 3} (h : Compatible c) :
    IntegerWindow c.stage (numerator c) (denominator c) (scope c) := by
  exact h.2

/-- A certificate remains valid when its positive requested scope decreases. -/
theorem IntegerWindow.mono_scope {k : ℕ} {B : ℤ} {q d D : ℕ}
    (h : IntegerWindow k B q D) (hd : 0 < d) (hle : d ≤ D) :
    IntegerWindow k B q d := by
  refine ⟨h.1, hd, h.2.2.1, h.2.2.2.1, ?_⟩
  have hleZ : (d : ℤ) ≤ D := by exact_mod_cast hle
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right hleZ h.2.2.2.1.le) h.2.2.2.2

theorem arithmetic_exhaustion_iff_cofinal : ArithmeticExhaustion ↔ CofinalAdmission := by
  constructor
  · intro h D
    obtain ⟨k, B, q, hw⟩ := h (D + 1) (by omega)
    exact ⟨windowCoordinate k B q (D + 1),
      windowCoordinate_admissible k B q (D + 1) hw, by simp⟩
  · intro h d hd
    obtain ⟨c, hc, hdc⟩ := h d
    exact ⟨c.stage, numerator c, denominator c,
      (compatible_integerWindow (compatible_of_admissible id hc)).mono_scope hd hdc⟩

theorem successor_iff_arithmetic_exhaustion :
    Nonempty CatalanSuccessor ↔ ArithmeticExhaustion :=
  successor_iff_cofinal.trans arithmetic_exhaustion_iff_cofinal.symm

theorem lock_iff_arithmetic_exhaustion :
    (∃ next : Coordinates 3 → Coordinates 3, LockLaws (system next)) ↔
      ArithmeticExhaustion :=
  lock_iff_cofinal.trans arithmetic_exhaustion_iff_cofinal.symm

/-- Each finite integer check reaches the identified native real constant. -/
theorem integerWindow_native_linear_form {k : ℕ} {B : ℤ} {q d : ℕ}
    (h : IntegerWindow k B q d) :
    0 < (B : ℝ) - (q : ℝ) * nativeCatalan ∧
      (B : ℝ) - (q : ℝ) * nativeCatalan < 1 / (d : ℝ) := by
  rw [CATALAN_NATIVE_IDENTIFIED]
  have hf := compatible_linear_form (windowCoordinate k B q d)
    ((windowCoordinate_compatible_iff k B q d).mpr h)
  simpa only [windowCoordinate_numerator, windowCoordinate_denominator,
    windowCoordinate_scope] using hf

/-- This theorem supplies the endpoint only after arithmetic exhaustion is proved. -/
theorem NATIVE_CATALAN_IRRATIONAL_OF_ARITHMETIC_EXHAUSTION
    (h : ArithmeticExhaustion) : Irrational nativeCatalan :=
  NATIVE_CATALAN_IRRATIONAL_OF_COFINAL (arithmetic_exhaustion_iff_cofinal.mp h)

/-- The known seed proves every requested positive scope through its finite bound. -/
theorem seed_covers_finite_scopes (d : ℕ) (hd : 0 < d)
    (hle : d ≤ Certificate1000.bound) :
    IntegerWindow 1000 Certificate1000.B Certificate1000.A.natAbs d := by
  have h := compatible_integerWindow seed_compatible
  simp only [seed_stage, seed_numerator, seed_denominator, seed_scope] at h
  exact h.mono_scope hd hle

end CatalanAnchor.RieszAdmission
