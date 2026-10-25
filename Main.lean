import CatalanAnchor

open CatalanAnchor

example : nativeComplex = (catalan : ℂ) := CATALAN_HURWITZ_IDENTIFIED

example : nativeCatalan =
    ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, 1 / (1 + (x * y) ^ 2) := by
  rw [CATALAN_NATIVE_IDENTIFIED]
  exact CATALAN_DOUBLE_INTEGRAL_IDENTIFIED

example : (8 : ℝ) / 9 < nativeCatalan ∧ nativeCatalan < 1 := by
  rw [CATALAN_NATIVE_IDENTIFIED]
  exact ⟨eight_ninths_lt_catalan, catalan_lt_one⟩

example (n : ℕ) :
    |nativeCatalan - partialSum n| ≤ 1 / (2 * (n : ℝ) + 1) ^ 2 := by
  rw [CATALAN_NATIVE_IDENTIFIED]
  exact partialSum_error_bound n

example (q : ℚ) (hq : q.den ≤ 10) : (q : ℝ) ≠ nativeCatalan :=
  NATIVE_CATALAN_FINITE_SCOPE_TEN q hq

-- A proof-bearing family is an explicit input to this implication.
example (W : IntegerLinearFormsWitness catalan) : Irrational nativeCatalan :=
  NATIVE_CATALAN_IRRATIONAL_OF_WITNESS W

-- The analytic interval and the 501-digit denominator scope have no witness input.
example : Certificate1000.Interval := CATALAN_INTERVAL_1000

example (q : ℚ) (hq : q.den ≤ Certificate1000.bound) : (q : ℝ) ≠ nativeCatalan :=
  NATIVE_CATALAN_FINITE_SCOPE_1000 q hq

example (q : ℚ) (hq : q.den ≤ 10 ^ 500) : (q : ℝ) ≠ nativeCatalan :=
  NATIVE_CATALAN_FINITE_SCOPE_10_POW_500 q hq

-- The found finite witness is locally admissible for any proposed successor.
example (next : GPBKQRXY.Riesz.Coordinates 3 → GPBKQRXY.Riesz.Coordinates 3) :
    GPBKQRXY.Riesz.Admissible (RieszAdmission.system next) RieszAdmission.seed :=
  RieszAdmission.seed_admissible next

-- The integer linear-form interpretation is proved for every accepted coordinate.
example (next : GPBKQRXY.Riesz.Coordinates 3 → GPBKQRXY.Riesz.Coordinates 3) :
    GPBKQRXY.Riesz.LinearLaws (-catalan) (RieszAdmission.system next)
      RieszAdmission.readout := RieszAdmission.linear_laws next

-- Universal preservation and scope doubling remain an explicit input.
example (T : RieszAdmission.CatalanSuccessor) : Irrational nativeCatalan :=
  RieszAdmission.NATIVE_CATALAN_IRRATIONAL_OF_SUCCESSOR T

-- A passing local check does not itself prove the successor laws.
example : GPBKQRXY.Riesz.check (RieszAdmission.system id) RieszAdmission.seed = true :=
  RieszAdmission.identity_seed_checks

example : ¬ GPBKQRXY.Riesz.LockLaws (RieszAdmission.system id) :=
  RieszAdmission.identity_not_lock

-- The exact existence condition is isolated; it is not assumed globally.
example : Nonempty RieszAdmission.CatalanSuccessor ↔ RieszAdmission.ArithmeticExhaustion :=
  RieszAdmission.successor_iff_arithmetic_exhaustion

example (h : RieszAdmission.ArithmeticExhaustion) : Irrational nativeCatalan :=
  RieszAdmission.NATIVE_CATALAN_IRRATIONAL_OF_ARITHMETIC_EXHAUSTION h

-- The saved witness covers every positive scope below its exact finite bound.
example (d : ℕ) (hd : 0 < d) (hD : d ≤ Certificate1000.bound) :
    RieszAdmission.IntegerWindow 1000 Certificate1000.B Certificate1000.A.natAbs d :=
  RieszAdmission.seed_covers_finite_scopes d hd hD
