import CatalanAnchor.Scoping

/-!
# Exact interval certificates for finite denominator scope

The input is a strict real interval and an integer-only certificate.  The
conclusion excludes finitely many rational denominators; no infinite family
or irrationality assertion is introduced.
-/

namespace CatalanAnchor

/-- The exact integer predicate used by the C scope checker. -/
structure IntervalFormCheck (lo hi : ℤ) (scale bound : ℕ) (A B : ℤ) : Prop where
  scale_pos : 0 < scale
  bound_pos : 1 ≤ bound
  coefficient_ne_zero : A ≠ 0
  lower_nonnegative :
    0 ≤ min (A * lo + B * (scale : ℤ)) (A * hi + B * (scale : ℤ))
  upper_positive :
    0 < max (A * lo + B * (scale : ℤ)) (A * hi + B * (scale : ℤ))
  upper_budget :
    (bound : ℤ) * max (A * lo + B * (scale : ℤ))
      (A * hi + B * (scale : ℤ)) ≤ (scale : ℤ)

/-- A nonconstant affine map takes a strict interval into the strict interval
between its two endpoint images, for either sign of its coefficient. -/
theorem affine_strict_interval
    {x lo hi A B : ℝ} (hA : A ≠ 0) (hlo : lo < x) (hhi : x < hi) :
    min (A * lo + B) (A * hi + B) < A * x + B ∧
      A * x + B < max (A * lo + B) (A * hi + B) := by
  rcases lt_or_gt_of_ne hA with hneg | hpos
  · constructor
    · exact lt_of_le_of_lt (min_le_right _ _)
        (by linarith [mul_lt_mul_of_neg_left hhi hneg])
    · exact lt_of_lt_of_le
        (by linarith [mul_lt_mul_of_neg_left hlo hneg]) (le_max_left _ _)
  · constructor
    · exact lt_of_le_of_lt (min_le_left _ _)
        (by linarith [mul_lt_mul_of_pos_left hlo hpos])
    · exact lt_of_lt_of_le
        (by linarith [mul_lt_mul_of_pos_left hhi hpos]) (le_max_right _ _)

/-- Integer endpoint comparisons prove a strictly positive linear form below
`1 / bound`. Equality is permitted in both integer certificate comparisons
because the input interval is strict and the coefficient is nonzero. -/
theorem interval_form_check_sound
    (x : ℝ) (lo hi : ℤ) (scale bound : ℕ) (A B : ℤ)
    (check : IntervalFormCheck lo hi scale bound A B)
    (hlo : (lo : ℝ) / (scale : ℝ) < x)
    (hhi : x < (hi : ℝ) / (scale : ℝ)) :
    0 < (A : ℝ) * x + (B : ℝ) ∧
      (A : ℝ) * x + (B : ℝ) < 1 / (bound : ℝ) := by
  have hs : (0 : ℝ) < (scale : ℝ) := by exact_mod_cast check.scale_pos
  have hd : (0 : ℝ) < (bound : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one check.bound_pos)
  have ha : (A : ℝ) ≠ 0 := by exact_mod_cast check.coefficient_ne_zero
  have hl : (lo : ℝ) < x * (scale : ℝ) := (div_lt_iff₀ hs).mp hlo
  have hh : x * (scale : ℝ) < (hi : ℝ) := (lt_div_iff₀ hs).mp hhi
  have hbounds := affine_strict_interval ha hl hh
    (B := (B : ℝ) * (scale : ℝ))
  have hnonneg : (0 : ℝ) ≤
      min ((A : ℝ) * (lo : ℝ) + (B : ℝ) * (scale : ℝ))
        ((A : ℝ) * (hi : ℝ) + (B : ℝ) * (scale : ℝ)) := by
    exact_mod_cast check.lower_nonnegative
  have hbudget : (bound : ℝ) *
      max ((A : ℝ) * (lo : ℝ) + (B : ℝ) * (scale : ℝ))
        ((A : ℝ) * (hi : ℝ) + (B : ℝ) * (scale : ℝ)) ≤ (scale : ℝ) := by
    exact_mod_cast check.upper_budget
  have hscaled_pos : 0 < ((A : ℝ) * x + (B : ℝ)) * (scale : ℝ) := by
    calc
      0 < (A : ℝ) * (x * (scale : ℝ)) + (B : ℝ) * (scale : ℝ) :=
        lt_of_le_of_lt hnonneg hbounds.1
      _ = ((A : ℝ) * x + (B : ℝ)) * (scale : ℝ) := by ring
  have hpositive : 0 < (A : ℝ) * x + (B : ℝ) :=
    (mul_pos_iff_of_pos_right hs).mp hscaled_pos
  have hscaled_upper : ((A : ℝ) * x + (B : ℝ)) * (scale : ℝ) <
      max ((A : ℝ) * (lo : ℝ) + (B : ℝ) * (scale : ℝ))
        ((A : ℝ) * (hi : ℝ) + (B : ℝ) * (scale : ℝ)) := by
    calc
      ((A : ℝ) * x + (B : ℝ)) * (scale : ℝ) =
          (A : ℝ) * (x * (scale : ℝ)) + (B : ℝ) * (scale : ℝ) := by ring
      _ < _ := hbounds.2
  have hproduct := lt_of_lt_of_le (mul_lt_mul_of_pos_left hscaled_upper hd) hbudget
  have hsmall_mul : ((A : ℝ) * x + (B : ℝ)) * (bound : ℝ) < 1 := by
    apply (mul_lt_mul_iff_of_pos_right hs).mp
    calc
      (((A : ℝ) * x + (B : ℝ)) * (bound : ℝ)) * (scale : ℝ) =
          (bound : ℝ) * (((A : ℝ) * x + (B : ℝ)) * (scale : ℝ)) := by ring
      _ < (scale : ℝ) := hproduct
      _ = 1 * (scale : ℝ) := by ring
  exact ⟨hpositive, (lt_div_iff₀ hd).mpr hsmall_mul⟩

/-- Kernel-checked bridge from a strict interval and a finite integer predicate
to exclusion of every rational with reduced denominator at most `bound`. -/
theorem interval_form_denominator_scope
    (x : ℝ) (lo hi : ℤ) (scale bound : ℕ) (A B : ℤ)
    (check : IntervalFormCheck lo hi scale bound A B)
    (hlo : (lo : ℝ) / (scale : ℝ) < x)
    (hhi : x < (hi : ℝ) / (scale : ℝ)) :
    ∀ q : ℚ, q.den ≤ bound → (q : ℝ) ≠ x := by
  obtain ⟨hpositive, hsmall⟩ :=
    interval_form_check_sound x lo hi scale bound A B check hlo hhi
  exact INTEGER_LINEAR_FORM_DENOMINATOR_SCOPE x A B bound
    check.bound_pos hpositive hsmall

end CatalanAnchor
