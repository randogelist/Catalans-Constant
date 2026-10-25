import GPBKQRXY.RieszRepresentative
import CatalanAnchor.EulerUniform
import CatalanAnchor.EulerComputed

/-!
# A checked Catalan coordinate and universal arithmetic interpretation

The successor is a parameter.  Compatibility is an exact finite integer test
using the uniformly proved Euler enclosure.  Every compatible coordinate has
the required positive small integer linear form.  This module constructs no
successor contraction law and makes no irrationality assertion.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 10000

namespace CatalanAnchor.RieszAdmission

open GPBKQRXY.Riesz

def numerator (c : Coordinates 3) : ℤ := (c.state 0).num
def denominator (c : Coordinates 3) : ℕ := (c.state 1).num.natAbs
def scope (c : Coordinates 3) : ℕ := (c.state 2).num.natAbs

/-- The state stores the actual integer readouts in rational coordinates. -/
def Canonical (c : Coordinates 3) : Prop :=
  c.state 0 = (numerator c : ℚ) ∧
  c.state 1 = (denominator c : ℚ) ∧
  c.state 2 = (scope c : ℚ)

def lowerNumerator (c : Coordinates 3) : ℤ :=
  numerator c * (EulerUniform.workScale c.stage : ℤ) -
    (denominator c : ℤ) * (EulerUniform.upper c.stage : ℤ)

def upperNumerator (c : Coordinates 3) : ℤ :=
  numerator c * (EulerUniform.workScale c.stage : ℤ) -
    (denominator c : ℤ) * (EulerUniform.lower c.stage : ℤ)

/-- Strict integer margins make the weak Euler enclosure sufficient. -/
def Compatible (c : Coordinates 3) : Prop :=
  Canonical c ∧ 0 < denominator c ∧ 0 < scope c ∧
    0 < lowerNumerator c ∧ 0 < upperNumerator c ∧
    (scope c : ℤ) * upperNumerator c < (EulerUniform.workScale c.stage : ℤ)

instance (c : Coordinates 3) : Decidable (Compatible c) := by
  unfold Compatible Canonical
  infer_instance

/-- The finite system leaves its successor as the sole construction parameter. -/
def system (next : Coordinates 3 → Coordinates 3) : EnvelopeSystem 3 where
  next := next
  compatible c := decide (Compatible c)
  error c := 1 / (scope c : ℚ)
  rate _ := 1 / 2

/-- The target is `-catalan`, so the positive form is `B - q*catalan`. -/
def readout : LinearReadout 3 where
  p c := -numerator c
  q c := denominator c

theorem compatible_of_admissible (next : Coordinates 3 → Coordinates 3)
    {c : Coordinates 3} (hc : Admissible (system next) c) : Compatible c := by
  exact of_decide_eq_true hc.1

theorem scope_pos_of_admissible (next : Coordinates 3 → Coordinates 3)
    {c : Coordinates 3} (hc : Admissible (system next) c) : 0 < scope c :=
  (compatible_of_admissible next hc).2.2.1

theorem denominator_pos_of_admissible (next : Coordinates 3 → Coordinates 3)
    {c : Coordinates 3} (hc : Admissible (system next) c) : 0 < denominator c :=
  (compatible_of_admissible next hc).2.1

/-- Every accepted coordinate has a positive integer linear form below the
reciprocal of its scope, independently of how the coordinate was discovered. -/
theorem compatible_linear_form (c : Coordinates 3) (hc : Compatible c) :
    0 < (numerator c : ℝ) - (denominator c : ℝ) * catalan ∧
      (numerator c : ℝ) - (denominator c : ℝ) * catalan < 1 / (scope c : ℝ) := by
  rcases hc with ⟨_, hq, hd, hl, _, hb⟩
  have hQ : (0 : ℝ) < (EulerUniform.workScale c.stage : ℝ) := by
    exact_mod_cast EulerUniform.workScale_pos c.stage
  have hqR : (0 : ℝ) ≤ (denominator c : ℝ) := by positivity
  have hdR : (0 : ℝ) < (scope c : ℝ) := by exact_mod_cast hd
  have hlR : (0 : ℝ) < (lowerNumerator c : ℝ) := by exact_mod_cast hl
  have hbR : (scope c : ℝ) * (upperNumerator c : ℝ) <
      (EulerUniform.workScale c.stage : ℝ) := by exact_mod_cast hb
  have henclosure := EulerUniform.scaled_enclosure c.stage
  have hlow : (lowerNumerator c : ℝ) ≤
      ((numerator c : ℝ) - (denominator c : ℝ) * catalan) *
        (EulerUniform.workScale c.stage : ℝ) := by
    calc
      (lowerNumerator c : ℝ) =
          (numerator c : ℝ) * (EulerUniform.workScale c.stage : ℝ) -
            (denominator c : ℝ) * (EulerUniform.upper c.stage : ℝ) := by
              simp only [lowerNumerator, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
      _ ≤ (numerator c : ℝ) * (EulerUniform.workScale c.stage : ℝ) -
          (denominator c : ℝ) * ((EulerUniform.workScale c.stage : ℝ) * catalan) :=
        sub_le_sub_left (mul_le_mul_of_nonneg_left henclosure.2 hqR) _
      _ = _ := by ring
  have hupp :
      ((numerator c : ℝ) - (denominator c : ℝ) * catalan) *
        (EulerUniform.workScale c.stage : ℝ) ≤ (upperNumerator c : ℝ) := by
    calc
      _ = (numerator c : ℝ) * (EulerUniform.workScale c.stage : ℝ) -
          (denominator c : ℝ) * ((EulerUniform.workScale c.stage : ℝ) * catalan) := by ring
      _ ≤ (numerator c : ℝ) * (EulerUniform.workScale c.stage : ℝ) -
          (denominator c : ℝ) * (EulerUniform.lower c.stage : ℝ) :=
        sub_le_sub_left (mul_le_mul_of_nonneg_left henclosure.1 hqR) _
      _ = (upperNumerator c : ℝ) := by
        simp only [upperNumerator, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
  have hp : 0 < (numerator c : ℝ) - (denominator c : ℝ) * catalan :=
    (mul_pos_iff_of_pos_right hQ).mp (lt_of_lt_of_le hlR hlow)
  have hm := lt_of_le_of_lt (mul_le_mul_of_nonneg_left hupp hdR.le) hbR
  have hsmall_mul :
      ((numerator c : ℝ) - (denominator c : ℝ) * catalan) * (scope c : ℝ) < 1 := by
    apply (mul_lt_mul_iff_of_pos_right hQ).mp
    calc
      _ = (scope c : ℝ) *
          (((numerator c : ℝ) - (denominator c : ℝ) * catalan) *
            (EulerUniform.workScale c.stage : ℝ)) := by ring
      _ < (EulerUniform.workScale c.stage : ℝ) := hm
      _ = 1 * (EulerUniform.workScale c.stage : ℝ) := by ring
  exact ⟨hp, (lt_div_iff₀ hdR).mpr hsmall_mul⟩

/-- Universal analytic and arithmetic interpretation is proved for every
admissible coordinate, with no successor or lock hypothesis. -/
theorem linear_laws (next : Coordinates 3 → Coordinates 3) :
    LinearLaws (-catalan) (system next) readout := by
  constructor
  · intro c hc
    exact denominator_pos_of_admissible next hc
  · intro c hc
    have h := compatible_linear_form c (compatible_of_admissible next hc)
    have heq : (readout.q c : ℝ) * (-catalan) - (readout.p c : ℝ) =
        (numerator c : ℝ) - (denominator c : ℝ) * catalan := by
      simp only [readout, Int.cast_neg]
      ring
    rw [heq]
    refine ⟨h.1, ?_⟩
    simpa [system] using h.2.le

def seed : Coordinates 3 where
  X := 3
  Y := 1
  stage := 1000
  state := ![(Certificate1000.B : ℚ), (Certificate1000.A.natAbs : ℚ),
    (Certificate1000.bound : ℚ)]

@[simp] theorem seed_numerator : numerator seed = Certificate1000.B := by
  simp [numerator, seed]

@[simp] theorem seed_denominator : denominator seed = Certificate1000.A.natAbs := by
  norm_num [denominator, seed, Certificate1000.A]

@[simp] theorem seed_scope : scope seed = Certificate1000.bound := by
  simp [scope, seed]

@[simp] theorem seed_stage : seed.stage = 1000 := rfl

theorem seed_euler_lower : EulerUniform.lower 1000 = EulerComputed.sumValue :=
  EulerComputed.fixedSum_value

theorem seed_euler_upper : EulerUniform.upper 1000 =
    EulerComputed.sumValue + 3 * EulerComputed.terms + 1 := by
  rw [EulerUniform.upper, seed_euler_lower]
  rfl

theorem seed_compatible : Compatible seed := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Canonical, seed, numerator, denominator, scope]
  · norm_num [seed_denominator, Certificate1000.A]
  · norm_num [seed_scope, Certificate1000.bound]
  · simp only [lowerNumerator, seed_numerator, seed_denominator,
      seed_euler_upper, seed_stage]
    norm_num [EulerUniform.workScale, EulerComputed.sumValue, EulerComputed.terms,
      Certificate1000.B, Certificate1000.A]
  · simp only [upperNumerator, seed_numerator, seed_denominator,
      seed_euler_lower, seed_stage]
    norm_num [EulerUniform.workScale, EulerComputed.sumValue,
      Certificate1000.B, Certificate1000.A]
  · simp only [upperNumerator, seed_numerator, seed_denominator,
      seed_scope, seed_euler_lower, seed_stage]
    norm_num [EulerUniform.workScale, EulerComputed.sumValue,
      Certificate1000.B, Certificate1000.A, Certificate1000.bound]

/-- A genuine admissible coordinate for every choice of the successor. -/
theorem seed_admissible (next : Coordinates 3 → Coordinates 3) :
    Admissible (system next) seed := by
  refine ⟨by exact decide_eq_true seed_compatible, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [seed]
  · norm_num [seed]
  · change (0 : ℚ) < 1 / (scope seed : ℚ)
    have hd : (0 : ℚ) < (scope seed : ℚ) := by
      exact_mod_cast seed_compatible.2.2.1
    positivity
  · norm_num [system]
  · norm_num [system]

theorem seed_checks (next : Coordinates 3 → Coordinates 3) :
    GPBKQRXY.Riesz.check (system next) seed = true :=
  (GPBKQRXY.Riesz.check_eq_true_iff (system next) seed).mpr (seed_admissible next)

end CatalanAnchor.RieszAdmission
