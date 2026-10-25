import GPBKQRXY.RieszCore

/-!
# A fixed target, a chosen analytic representative, and one checked coordinate

The series identity is anchored to the fixed target `x`. The analytic
interpretation and successor laws are explicit proof fields. A convergent
series alone does not construct those proofs or an admitted coordinate.
-/

namespace GPBKQRXY.Riesz

/-- A rational-coefficient power series evaluated at a rational point. -/
structure AnalyticPowerSeriesInput (x : ℝ) where
  coefficient : ℕ → ℚ
  point : ℚ
  sums_to : HasSum (fun k => (coefficient k : ℝ) * (point : ℝ) ^ k) x

structure LinearReadout (width : ℕ) where
  p : Coordinates width → ℤ
  q : Coordinates width → ℕ

/-- Prove these from the representative's identities and remainder estimates. -/
structure LinearLaws {width : ℕ} (x : ℝ)
    (S : EnvelopeSystem width) (R : LinearReadout width) : Prop where
  denominator_pos : ∀ c, Admissible S c → 0 < R.q c
  interpretation : ∀ c, Admissible S c →
    0 < (R.q c : ℝ) * x - (R.p c : ℝ) ∧
      (R.q c : ℝ) * x - (R.p c : ℝ) ≤ (S.error c : ℝ)

/-- The verified construction is chosen after fixing the target `x`. -/
structure AnalyticRepresentative (x : ℝ) where
  series : AnalyticPowerSeriesInput x
  width : ℕ
  envelope : EnvelopeSystem width
  readout : LinearReadout width
  lock : LockLaws envelope
  analytic : LinearLaws x envelope readout

namespace AnalyticRepresentative

abbrev Coordinates {x : ℝ} (A : AnalyticRepresentative x) :=
  GPBKQRXY.Riesz.Coordinates A.width

/-- Computed readouts belong to A; a witness cannot supply unrelated p,q,E,rho. -/
def check {x : ℝ} (A : AnalyticRepresentative x) (c : A.Coordinates) : Bool :=
  GPBKQRXY.Riesz.check A.envelope c && decide (0 < A.readout.q c)

theorem check_eq_true_iff {x : ℝ} (A : AnalyticRepresentative x)
    (c : A.Coordinates) : A.check c = true ↔ Admissible A.envelope c := by
  simp only [check, Bool.and_eq_true, GPBKQRXY.Riesz.check_eq_true_iff,
    decide_eq_true_eq]
  exact ⟨fun h => h.1, fun h => ⟨h, A.analytic.denominator_pos c h⟩⟩

end AnalyticRepresentative

def CoordinateAdmission {x : ℝ} (A : AnalyticRepresentative x) : Prop :=
  ∃ c : A.Coordinates, A.check c = true

/-- A concrete proof-carrying witness, normally closed with `by decide`. -/
structure AdmissionCertificate {x : ℝ} (A : AnalyticRepresentative x) where
  coordinate : A.Coordinates
  accepted : A.check coordinate = true

/-- Optional explicit readouts for a submitted witness; each is rechecked. -/
structure WitnessPacket (width : ℕ) where
  coordinate : Coordinates width
  numerator : ℤ
  denominator : ℕ
  error : ℚ
  rate : ℚ

def checkWitness {width : ℕ} (S : EnvelopeSystem width)
    (R : LinearReadout width) (w : WitnessPacket width) : Bool :=
  check S w.coordinate && decide
    (0 < R.q w.coordinate ∧ w.numerator = R.p w.coordinate ∧
      w.denominator = R.q w.coordinate ∧ w.error = S.error w.coordinate ∧
      w.rate = S.rate w.coordinate)

/-- Acceptance includes agreement with the chosen representative's readouts. -/
structure VerifiedWitness {x : ℝ} (A : AnalyticRepresentative x) where
  packet : WitnessPacket A.width
  accepted : checkWitness A.envelope A.readout packet = true

/-- Generic arithmetic closure, independent of any particular power series. -/
theorem IRRATIONAL_OF_LINEAR_LOCK {width : ℕ} (x : ℝ)
    (S : EnvelopeSystem width) (R : LinearReadout width)
    (L : LockLaws S) (H : LinearLaws x S R)
    (c : Coordinates width) (hc : Admissible S c) : Irrational x := by
  intro hx
  obtain ⟨r, hr⟩ := hx
  have hd : 0 < r.den := Nat.pos_of_ne_zero (Rat.den_nz r)
  have hdR : (0 : ℝ) < r.den := by exact_mod_cast hd
  obtain ⟨n, hn⟩ := exists_small_error S L c hc r.den hd
  let cn := orbit S c n
  have hcn : Admissible S cn := orbit_admissible S L c hc n
  obtain ⟨hpos, hbound⟩ := H.interpretation cn hcn
  have hsmallE : (r.den : ℝ) * (S.error cn : ℝ) < 1 := by
    exact_mod_cast hn
  have hsmall : (r.den : ℝ) * ((R.q cn : ℝ) * x - (R.p cn : ℝ)) < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hbound (le_of_lt hdR)) hsmallE
  let m : ℤ := (R.q cn : ℤ) * r.num - R.p cn * (r.den : ℤ)
  have hrat : (r.den : ℝ) * (r : ℝ) = (r.num : ℝ) := by
    exact_mod_cast (Rat.den_mul_eq_num r)
  have hm : (r.den : ℝ) * ((R.q cn : ℝ) * x - (R.p cn : ℝ)) = (m : ℝ) := by
    calc
      (r.den : ℝ) * ((R.q cn : ℝ) * x - (R.p cn : ℝ)) =
          (R.q cn : ℝ) * ((r.den : ℝ) * (r : ℝ)) -
            (R.p cn : ℝ) * (r.den : ℝ) := by rw [hr]; ring
      _ = (m : ℝ) := by rw [hrat]; dsimp [m]; push_cast; ring
  have hm0R : (0 : ℝ) < (m : ℝ) := by rw [← hm]; exact mul_pos hdR hpos
  have hm1R : (m : ℝ) < 1 := by rw [← hm]; exact hsmall
  have hm0 : (0 : ℤ) < m := by exact_mod_cast hm0R
  have hm1 : m < (1 : ℤ) := by exact_mod_cast hm1R
  omega

theorem IRRATIONAL_OF_VERIFIED_COORDINATE {x : ℝ}
    (A : AnalyticRepresentative x) (c : A.Coordinates) (h : A.check c = true) :
    Irrational x :=
  IRRATIONAL_OF_LINEAR_LOCK x A.envelope A.readout A.lock A.analytic c
    ((A.check_eq_true_iff c).mp h)

theorem IRRATIONAL_OF_CERTIFICATE {x : ℝ}
    (A : AnalyticRepresentative x) (w : AdmissionCertificate A) : Irrational x :=
  IRRATIONAL_OF_VERIFIED_COORDINATE A w.coordinate w.accepted

theorem IRRATIONAL_OF_VERIFIED_WITNESS {x : ℝ}
    (A : AnalyticRepresentative x) (w : VerifiedWitness A) : Irrational x := by
  have h := w.accepted
  simp only [checkWitness, Bool.and_eq_true, decide_eq_true_eq] at h
  exact IRRATIONAL_OF_LINEAR_LOCK x A.envelope A.readout A.lock A.analytic
    w.packet.coordinate ((check_eq_true_iff A.envelope w.packet.coordinate).mp h.1)

theorem IRRATIONAL_OF_COORDINATE_ADMISSION {x : ℝ}
    (A : AnalyticRepresentative x) (h : CoordinateAdmission A) : Irrational x := by
  obtain ⟨c, hc⟩ := h
  exact IRRATIONAL_OF_VERIFIED_COORDINATE A c hc

/-- The requested endpoint: choose A for the fixed x, then supply one entry. -/
theorem IRRATIONAL_OF_ADMITTED_REPRESENTATIVE (x : ℝ)
    (h : ∃ A : AnalyticRepresentative x, CoordinateAdmission A) : Irrational x := by
  obtain ⟨A, hA⟩ := h
  exact IRRATIONAL_OF_COORDINATE_ADMISSION A hA

/-- A sound construction cannot accept a seed for a rational target. -/
theorem rational_has_no_admitted_coordinate (r : ℚ)
    (A : AnalyticRepresentative (r : ℝ)) : ¬ CoordinateAdmission A := by
  intro h
  exact IRRATIONAL_OF_COORDINATE_ADMISSION A h ⟨r, rfl⟩

end GPBKQRXY.Riesz
