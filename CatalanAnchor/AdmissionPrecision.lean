import CatalanAnchor.Admission

/-!
Necessary precision growth for the Catalan admission architecture.
A finite accepted coordinate has scope strictly below its integer work scale.
Consequently a contracting admissible orbit cannot remain at bounded precision.
-/

namespace CatalanAnchor.RieszAdmission

open GPBKQRXY.Riesz

/-- A positive integer upper numerator forces a strict finite scope cap. -/
theorem scope_lt_workScale_of_compatible {c : Coordinates 3}
    (hc : Compatible c) : scope c < EulerUniform.workScale c.stage := by
  have hU : (1 : ℤ) ≤ upperNumerator c := by
    have h := hc.2.2.2.2.1
    omega
  have hs : (0 : ℤ) ≤ scope c := by positivity
  have hm : (scope c : ℤ) ≤ (scope c : ℤ) * upperNumerator c := by
    nlinarith
  have ht : (scope c : ℤ) < (EulerUniform.workScale c.stage : ℤ) :=
    hm.trans_lt hc.2.2.2.2.2
  exact_mod_cast ht

theorem scope_lt_workScale_of_admissible
    (next : Coordinates 3 → Coordinates 3) {c : Coordinates 3}
    (hc : Admissible (system next) c) :
    scope c < EulerUniform.workScale c.stage :=
  scope_lt_workScale_of_compatible (compatible_of_admissible next hc)

theorem workScale_mono {p P : ℕ} (h : p ≤ P) :
    EulerUniform.workScale p ≤ EulerUniform.workScale P := by
  unfold EulerUniform.workScale
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- A lock cannot have an admitted orbit whose precision stays bounded. -/
theorem no_lock_of_bounded_precision
    (next : Coordinates 3 → Coordinates 3) (c : Coordinates 3)
    (hc : Admissible (system next) c) (P : ℕ)
    (hstage : ∀ n, (orbit (system next) c n).stage ≤ P) :
    ¬ LockLaws (system next) := by
  intro L
  obtain ⟨n, hn⟩ := exists_small_error (system next) L c hc
    (EulerUniform.workScale P) (EulerUniform.workScale_pos P)
  have ha := orbit_admissible (system next) L c hc n
  have hs := scope_lt_workScale_of_admissible next ha
  have hb := hs.trans_le (workScale_mono (hstage n))
  have hp : (0 : ℚ) < scope (orbit (system next) c n) := by
    exact_mod_cast scope_pos_of_admissible next ha
  have hbq : (scope (orbit (system next) c n) : ℚ) <
      (EulerUniform.workScale P : ℚ) := by exact_mod_cast hb
  change (EulerUniform.workScale P : ℚ) *
    (1 / (scope (orbit (system next) c n) : ℚ)) < 1 at hn
  rw [mul_one_div] at hn
  have hgt := (div_lt_one hp).mp hn
  exact (not_lt_of_ge hbq.le) hgt

/-- Every admitted lock orbit must eventually exceed each finite precision. -/
theorem precision_unbounded_of_lock
    (next : Coordinates 3 → Coordinates 3) (L : LockLaws (system next))
    (c : Coordinates 3) (hc : Admissible (system next) c) (P : ℕ) :
    ∃ n, P < (orbit (system next) c n).stage := by
  by_contra h
  push Not at h
  exact no_lock_of_bounded_precision next c hc P h L

/-- Repeating an admitted coordinate cannot implement strict contraction. -/
theorem no_lock_of_fixed_admissible
    (next : Coordinates 3 → Coordinates 3) (c : Coordinates 3)
    (hc : Admissible (system next) c) (hnext : next c = c) :
    ¬ LockLaws (system next) := by
  intro L
  have h := L.contracts c hc
  change (1 / (scope (next c) : ℚ)) ≤
    (1 / 2 : ℚ) * (1 / (scope c : ℚ)) at h
  rw [hnext] at h
  have hp : (0 : ℚ) < 1 / (scope c : ℚ) := hc.2.2.2.1
  linarith

/-- The actual saved Catalan coordinate passes even for an identity successor. -/
theorem identity_seed_checks : check (system id) seed = true :=
  seed_checks id

/-- That same checked system cannot satisfy the contraction laws. -/
theorem identity_not_lock : ¬ LockLaws (system id) :=
  no_lock_of_fixed_admissible id seed (seed_admissible id) rfl

end CatalanAnchor.RieszAdmission
