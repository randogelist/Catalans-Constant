import CatalanAnchor.Series

/-!
Integer fixed-point replay of the positive Euler recurrence.  The analytic
sequence and its enclosure are explicit inputs: this file proves only the
rounding and finite-sum error estimates.
-/

namespace CatalanAnchor.EulerFixedPoint

def fixedState (Q : ℕ) : ℕ → ℕ × ℕ × ℕ
  | 0 => (Q / 2, Q / 2, 0)
  | n + 1 =>
    let s := fixedState Q n
    let U := ((n + 1) * s.1) / (2 * n + 3)
    let A := ((n + 1) * s.2.1 + U) / (2 * n + 3)
    (U, A, s.2.2 + s.2.1)

def fixedU (Q n : ℕ) : ℕ := (fixedState Q n).1
def fixedA (Q n : ℕ) : ℕ := (fixedState Q n).2.1
def fixedSum (Q n : ℕ) : ℕ := (fixedState Q n).2.2

@[simp] theorem fixedU_zero (Q : ℕ) : fixedU Q 0 = Q / 2 := rfl
@[simp] theorem fixedA_zero (Q : ℕ) : fixedA Q 0 = Q / 2 := rfl
@[simp] theorem fixedSum_zero (Q : ℕ) : fixedSum Q 0 = 0 := rfl

theorem fixedU_succ (Q n : ℕ) :
    fixedU Q (n + 1) = (n + 1) * fixedU Q n / (2 * n + 3) := rfl

theorem fixedA_succ (Q n : ℕ) :
    fixedA Q (n + 1) = ((n + 1) * fixedA Q n + fixedU Q (n + 1)) /
      (2 * n + 3) := rfl

theorem fixedSum_succ (Q n : ℕ) :
    fixedSum Q (n + 1) = fixedSum Q n + fixedA Q n := rfl

theorem fixedSum_eq_sum (Q N : ℕ) :
    fixedSum Q N = ∑ n ∈ Finset.range N, fixedA Q n := by
  induction N with
  | zero => simp
  | succ N ih => rw [fixedSum_succ, Finset.sum_range_succ, ih]

theorem nat_div_rounding (m d : ℕ) (hd : 0 < d) :
    0 ≤ (m : ℝ) / d - (m / d : ℕ) ∧
    (m : ℝ) / d - (m / d : ℕ) < 1 := by
  constructor
  · exact sub_nonneg.mpr Nat.cast_div_le
  · have h : m < (m / d + 1) * d :=
      (Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_succ_self (m / d))
    have hr : (m : ℝ) < ((m / d : ℕ) + 1) * d := by exact_mod_cast h
    have hdr : (0 : ℝ) < d := by exact_mod_cast hd
    have hdiv : (m : ℝ) / d < (m / d : ℕ) + 1 :=
      (div_lt_iff₀ hdr).mpr hr
    linarith

theorem recurrence_rounding
    (Q : ℕ) (hQ : 2 ∣ Q) (u a : ℕ → ℝ)
    (hu0 : u 0 = 1 / 2) (ha0 : a 0 = 1 / 2)
    (hu : ∀ n, u (n + 1) = ((n : ℝ) + 1) * u n / (2 * n + 3))
    (ha : ∀ n, a (n + 1) = (((n : ℝ) + 1) * a n + u (n + 1)) /
      (2 * n + 3)) :
    ∀ n, (0 ≤ (Q : ℝ) * u n - fixedU Q n ∧
      (Q : ℝ) * u n - fixedU Q n < 2) ∧
      (0 ≤ (Q : ℝ) * a n - fixedA Q n ∧
      (Q : ℝ) * a n - fixedA Q n < 3) := by
  intro n
  induction n with
  | zero =>
    rw [hu0, ha0, fixedU_zero, fixedA_zero, Nat.cast_div_charZero hQ]
    norm_num
    ring_nf
    norm_num
  | succ n ih =>
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hd : 0 < 2 * n + 3 := by omega
    have hdr : (0 : ℝ) < 2 * n + 3 := by positivity
    have hU := nat_div_rounding ((n + 1) * fixedU Q n) (2 * n + 3) hd
    have hA := nat_div_rounding
      ((n + 1) * fixedA Q n + fixedU Q (n + 1)) (2 * n + 3) hd
    push_cast at hU hA
    rw [← fixedU_succ] at hU
    rw [← fixedA_succ] at hA
    have hUeq : (Q : ℝ) * u (n + 1) - fixedU Q (n + 1) =
        ((n + 1) * ((Q : ℝ) * u n - fixedU Q n)) / (2 * n + 3) +
        (((n + 1) * (fixedU Q n : ℝ)) / (2 * n + 3) - fixedU Q (n + 1)) := by
      rw [hu n]
      ring
    have hUlo : 0 ≤ (Q : ℝ) * u (n + 1) - fixedU Q (n + 1) := by
      rw [hUeq]
      exact add_nonneg (div_nonneg (mul_nonneg (by positivity) ih.1.1)
        (le_of_lt hdr)) hU.1
    have hUhi : (Q : ℝ) * u (n + 1) - fixedU Q (n + 1) < 2 := by
      have ht : ((n + 1) * ((Q : ℝ) * u n - fixedU Q n)) /
          (2 * n + 3) < 1 := by
        apply (div_lt_iff₀ hdr).mpr
        nlinarith [ih.1.2]
      rw [hUeq]
      linarith [hU.2]
    have hAeq : (Q : ℝ) * a (n + 1) - fixedA Q (n + 1) =
        (((n + 1) * ((Q : ℝ) * a n - fixedA Q n) +
          ((Q : ℝ) * u (n + 1) - fixedU Q (n + 1))) / (2 * n + 3)) +
        ((((n + 1) * (fixedA Q n : ℝ) + fixedU Q (n + 1)) /
          (2 * n + 3)) - fixedA Q (n + 1)) := by
      rw [ha n]
      ring
    have hAlo : 0 ≤ (Q : ℝ) * a (n + 1) - fixedA Q (n + 1) := by
      rw [hAeq]
      exact add_nonneg (div_nonneg (add_nonneg
        (mul_nonneg (by positivity) ih.2.1) hUlo) (le_of_lt hdr)) hA.1
    have hAhi : (Q : ℝ) * a (n + 1) - fixedA Q (n + 1) < 3 := by
      have ht : (((n + 1) * ((Q : ℝ) * a n - fixedA Q n) +
          ((Q : ℝ) * u (n + 1) - fixedU Q (n + 1))) / (2 * n + 3)) < 2 := by
        apply (div_lt_iff₀ hdr).mpr
        nlinarith [ih.2.2]
      rw [hAeq]
      linarith [hA.2]
    exact ⟨⟨hUlo, hUhi⟩, ⟨hAlo, hAhi⟩⟩

theorem sum_rounding (Q N : ℕ) (a : ℕ → ℝ)
    (h : ∀ n, 0 ≤ (Q : ℝ) * a n - fixedA Q n ∧
      (Q : ℝ) * a n - fixedA Q n < 3) :
    (fixedSum Q N : ℝ) ≤ (Q : ℝ) * (∑ n ∈ Finset.range N, a n) ∧
    (Q : ℝ) * (∑ n ∈ Finset.range N, a n) ≤ fixedSum Q N + 3 * N := by
  have he : (Q : ℝ) * (∑ n ∈ Finset.range N, a n) - fixedSum Q N =
      ∑ n ∈ Finset.range N, ((Q : ℝ) * a n - fixedA Q n) := by
    rw [fixedSum_eq_sum, Nat.cast_sum, Finset.sum_sub_distrib, Finset.mul_sum]
  have hlo : 0 ≤ (Q : ℝ) * (∑ n ∈ Finset.range N, a n) - fixedSum Q N := by
    rw [he]
    exact Finset.sum_nonneg fun n _ => (h n).1
  have hhi : (Q : ℝ) * (∑ n ∈ Finset.range N, a n) - fixedSum Q N ≤ 3 * N := by
    rw [he]
    calc
      (∑ n ∈ Finset.range N, ((Q : ℝ) * a n - fixedA Q n)) ≤
          ∑ _n ∈ Finset.range N, (3 : ℝ) :=
        Finset.sum_le_sum fun n _ => (h n).2.le
      _ = 3 * N := by simp [mul_comm]
  constructor <;> linarith

theorem sum_rounding_strict (Q N : ℕ) (hN : 0 < N) (a : ℕ → ℝ)
    (h : ∀ n, 0 ≤ (Q : ℝ) * a n - fixedA Q n ∧
      (Q : ℝ) * a n - fixedA Q n < 3) :
    (Q : ℝ) * (∑ n ∈ Finset.range N, a n) < fixedSum Q N + 3 * N := by
  have he : (Q : ℝ) * (∑ n ∈ Finset.range N, a n) - fixedSum Q N =
      ∑ n ∈ Finset.range N, ((Q : ℝ) * a n - fixedA Q n) := by
    rw [fixedSum_eq_sum, Nat.cast_sum, Finset.sum_sub_distrib, Finset.mul_sum]
  have hhi : (Q : ℝ) * (∑ n ∈ Finset.range N, a n) - fixedSum Q N < 3 * N := by
    rw [he]
    calc
      (∑ n ∈ Finset.range N, ((Q : ℝ) * a n - fixedA Q n)) <
          ∑ _n ∈ Finset.range N, (3 : ℝ) := by
        apply Finset.sum_lt_sum (fun n _ => (h n).2.le)
        exact ⟨0, Finset.mem_range.mpr hN, (h 0).2⟩
      _ = 3 * N := by simp [mul_comm]
  linarith

theorem scaled_enclosure (Q N : ℕ) (a : ℕ → ℝ) (x tail : ℝ)
    (h : ∀ n, 0 ≤ (Q : ℝ) * a n - fixedA Q n ∧
      (Q : ℝ) * a n - fixedA Q n < 3)
    (hlo : (∑ n ∈ Finset.range N, a n) ≤ x)
    (hhi : x ≤ (∑ n ∈ Finset.range N, a n) + tail) :
    (fixedSum Q N : ℝ) ≤ (Q : ℝ) * x ∧
    (Q : ℝ) * x ≤ fixedSum Q N + 3 * N + (Q : ℝ) * tail := by
  have hs := sum_rounding Q N a h
  have hQ : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
  constructor
  · exact hs.1.trans (mul_le_mul_of_nonneg_left hlo hQ)
  · have ht := mul_le_mul_of_nonneg_left hhi hQ
    nlinarith [hs.2]

end CatalanAnchor.EulerFixedPoint
