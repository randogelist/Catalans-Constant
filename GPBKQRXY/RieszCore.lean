import CatalanAnchor.Scoping

/-!
# Exact coordinates and the one-entry contraction theorem

Coordinates are finite rational data. X is matrix dimension, Y is tensor
order; neither field is silently identified with an arithmetic degree.
The Boolean entry check does not prove the successor laws. Those are
separate proof fields in `LockLaws`, to be discharged for each construction.
-/

namespace GPBKQRXY.Riesz

/-- A concrete finite coordinate type; the representative fixes `width`. -/
structure Coordinates (width : ℕ) where
  X : ℕ
  Y : ℕ
  stage : ℕ
  state : Fin width → ℚ

/-- All entry computations use exact data; no real-number comparison occurs. -/
structure EnvelopeSystem (width : ℕ) where
  next : Coordinates width → Coordinates width
  compatible : Coordinates width → Bool
  error : Coordinates width → ℚ
  rate : Coordinates width → ℚ

def Admissible {width : ℕ} (S : EnvelopeSystem width)
    (c : Coordinates width) : Prop :=
  S.compatible c = true ∧ 0 < c.X ∧ 0 < c.Y ∧
    0 < S.error c ∧ 0 < S.rate c ∧ S.rate c < 1

instance {width : ℕ} (S : EnvelopeSystem width) (c : Coordinates width) :
    Decidable (Admissible S c) := by
  unfold Admissible
  infer_instance

def check {width : ℕ} (S : EnvelopeSystem width) (c : Coordinates width) : Bool :=
  decide (Admissible S c)

theorem check_eq_true_iff {width : ℕ} (S : EnvelopeSystem width)
    (c : Coordinates width) : check S c = true ↔ Admissible S c := by
  simp [check]

/-- These universal laws are mathematical obligations, not checked seed data. -/
structure LockLaws {width : ℕ} (S : EnvelopeSystem width) : Prop where
  invariant : ∀ c, Admissible S c → Admissible S (S.next c)
  rate_antitone : ∀ c, Admissible S c → S.rate (S.next c) ≤ S.rate c
  contracts : ∀ c, Admissible S c → S.error (S.next c) ≤ S.rate c * S.error c

def orbit {width : ℕ} (S : EnvelopeSystem width) (c : Coordinates width) :
    ℕ → Coordinates width
  | 0 => c
  | n + 1 => S.next (orbit S c n)

theorem orbit_admissible {width : ℕ} (S : EnvelopeSystem width)
    (L : LockLaws S) (c : Coordinates width) (hc : Admissible S c) (n : ℕ) :
    Admissible S (orbit S c n) := by
  induction n with
  | zero => exact hc
  | succ n ih => exact L.invariant _ ih

theorem orbit_rate_le {width : ℕ} (S : EnvelopeSystem width)
    (L : LockLaws S) (c : Coordinates width) (hc : Admissible S c) (n : ℕ) :
    S.rate (orbit S c n) ≤ S.rate c := by
  induction n with
  | zero => exact le_refl _
  | succ n ih =>
      exact le_trans (L.rate_antitone _ (orbit_admissible S L c hc n)) ih

/-- The single accepted coordinate generates a uniform geometric envelope. -/
theorem orbit_error_le {width : ℕ} (S : EnvelopeSystem width)
    (L : LockLaws S) (c : Coordinates width) (hc : Admissible S c) (n : ℕ) :
    S.error (orbit S c n) ≤ S.rate c ^ n * S.error c := by
  induction n with
  | zero => simp [orbit]
  | succ n ih =>
      have hn := orbit_admissible S L c hc n
      have hE : 0 ≤ S.error (orbit S c n) := le_of_lt hn.2.2.2.1
      have hr : 0 ≤ S.rate c := le_of_lt hc.2.2.2.2.1
      calc
        S.error (orbit S c (n + 1))
            ≤ S.rate (orbit S c n) * S.error (orbit S c n) := L.contracts _ hn
        _ ≤ S.rate c * (S.rate c ^ n * S.error c) :=
          mul_le_mul (orbit_rate_le S L c hc n) ih hE hr
        _ = S.rate c ^ (n + 1) * S.error c := by ring

theorem orbit_error_antitone {width : ℕ} (S : EnvelopeSystem width)
    (L : LockLaws S) (c : Coordinates width) (hc : Admissible S c) :
    Antitone (fun n => S.error (orbit S c n)) := by
  apply antitone_nat_of_succ_le
  intro n
  have hn := orbit_admissible S L c hc n
  calc
    S.error (orbit S c (n + 1))
        ≤ S.rate (orbit S c n) * S.error (orbit S c n) := L.contracts _ hn
    _ ≤ 1 * S.error (orbit S c n) :=
      mul_le_mul_of_nonneg_right (le_of_lt hn.2.2.2.2.2) (le_of_lt hn.2.2.2.1)
    _ = S.error (orbit S c n) := one_mul _

/-- No universal family of later witnesses is assumed: it is derived here. -/
theorem exists_small_error {width : ℕ} (S : EnvelopeSystem width)
    (L : LockLaws S) (c : Coordinates width) (hc : Admissible S c)
    (K : ℕ) (hK : 0 < K) :
    ∃ n : ℕ, (K : ℚ) * S.error (orbit S c n) < 1 := by
  have hKQ : (0 : ℚ) < K := by exact_mod_cast hK
  have hKE : (0 : ℚ) < (K : ℚ) * S.error c := mul_pos hKQ hc.2.2.2.1
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
    (div_pos (by norm_num : (0 : ℚ) < 1) hKE) hc.2.2.2.2.2
  refine ⟨n, ?_⟩
  have hsmall : (K : ℚ) * (S.rate c ^ n * S.error c) < 1 := by
    have h := (lt_div_iff₀ hKE).mp hn
    nlinarith [h]
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left (orbit_error_le S L c hc n) (le_of_lt hKQ)) hsmall

/-- Arbitrarily late small envelopes, used for growing arithmetic scopes. -/
theorem exists_small_error_after {width : ℕ} (S : EnvelopeSystem width)
    (L : LockLaws S) (c : Coordinates width) (hc : Admissible S c)
    (K : ℕ) (hK : 0 < K) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ (K : ℚ) * S.error (orbit S c n) < 1 := by
  obtain ⟨n, hn⟩ := exists_small_error S L c hc K hK
  refine ⟨max N n, le_max_left _ _, ?_⟩
  have hE := orbit_error_antitone S L c hc (le_max_right N n)
  have hKQ : (0 : ℚ) ≤ K := by positivity
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hE hKQ) hn

end GPBKQRXY.Riesz
