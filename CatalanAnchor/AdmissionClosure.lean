import CatalanAnchor.Admission
import CatalanAnchor.HurwitzBridge
import GPBKQRXY.RieszRepresentative

/-!
The finite Catalan certificate supplies an admitted seed.  This file exposes
the additional universal successor obligations needed to apply the Riesz
contraction theorem.  No successor satisfying those obligations is asserted
to exist.
-/

noncomputable section

namespace CatalanAnchor.RieszAdmission

open GPBKQRXY.Riesz

/-- The ordinary, absolutely convergent Catalan series, with its sign changed. -/
def negativeCatalanSeries : AnalyticPowerSeriesInput (-catalan) where
  coefficient n := -((-1 : ℚ) ^ n / (2 * (n : ℚ) + 1) ^ 2)
  point := 1
  sums_to := by
    apply hasSum_catalan.neg.congr_fun
    intro n
    simp [term]

/-- The existing finite seed yields a representative only after the global
lock laws have been supplied. -/
def representative (next : Coordinates 3 → Coordinates 3)
    (L : LockLaws (system next)) : AnalyticRepresentative (-catalan) where
  series := negativeCatalanSeries
  width := 3
  envelope := system next
  readout := readout
  lock := L
  analytic := linear_laws next

/-- Finite coordinate admission remains conditional on the representative's
explicit global lock-law argument. -/
def seed_certificate (next : Coordinates 3 → Coordinates 3)
    (L : LockLaws (system next)) : AdmissionCertificate (representative next L) where
  coordinate := seed
  accepted :=
    ((representative next L).check_eq_true_iff seed).mpr (seed_admissible next)

theorem seed_coordinate_admission (next : Coordinates 3 → Coordinates 3)
    (L : LockLaws (system next)) : CoordinateAdmission (representative next L) :=
  ⟨(seed_certificate next L).coordinate, (seed_certificate next L).accepted⟩

/-- These are the unresolved, universal mathematical obligations on a
successor.  The checked seed alone does not supply either field. -/
structure CatalanSuccessor where
  next : Coordinates 3 → Coordinates 3
  preserves : ∀ c, Admissible (system next) c →
    Admissible (system next) (next c)
  doubles : ∀ c, Admissible (system next) c → 2 * scope c ≤ scope (next c)

/-- Admissibility preservation and scope doubling imply the three lock laws. -/
theorem CatalanSuccessor.lockLaws (T : CatalanSuccessor) : LockLaws (system T.next) where
  invariant := T.preserves
  rate_antitone := by
    intro c hc
    exact le_refl _
  contracts := by
    intro c hc
    change 1 / (scope (T.next c) : ℚ) ≤ (1 / 2 : ℚ) * (1 / (scope c : ℚ))
    have hp : (0 : ℚ) < scope c := by
      exact_mod_cast scope_pos_of_admissible T.next hc
    have hd : 2 * (scope c : ℚ) ≤ scope (T.next c) := by
      exact_mod_cast T.doubles c hc
    calc
      1 / (scope (T.next c) : ℚ) ≤ 1 / (2 * (scope c : ℚ)) :=
        one_div_le_one_div_of_le (by positivity) hd
      _ = (1 / 2 : ℚ) * (1 / (scope c : ℚ)) := by ring

theorem CATALAN_IRRATIONAL_OF_LOCK
    (next : Coordinates 3 → Coordinates 3) (L : LockLaws (system next)) :
    Irrational catalan := by
  have h := IRRATIONAL_OF_LINEAR_LOCK (-catalan) (system next) readout L
    (linear_laws next) seed (seed_admissible next)
  exact irrational_neg_iff.mp h

theorem NATIVE_CATALAN_IRRATIONAL_OF_LOCK
    (next : Coordinates 3 → Coordinates 3) (L : LockLaws (system next)) :
    Irrational nativeCatalan := by
  rw [CATALAN_NATIVE_IDENTIFIED]
  exact CATALAN_IRRATIONAL_OF_LOCK next L

theorem CATALAN_IRRATIONAL_OF_SUCCESSOR (T : CatalanSuccessor) :
    Irrational catalan :=
  CATALAN_IRRATIONAL_OF_LOCK T.next T.lockLaws

theorem NATIVE_CATALAN_IRRATIONAL_OF_SUCCESSOR (T : CatalanSuccessor) :
    Irrational nativeCatalan :=
  NATIVE_CATALAN_IRRATIONAL_OF_LOCK T.next T.lockLaws

end CatalanAnchor.RieszAdmission
