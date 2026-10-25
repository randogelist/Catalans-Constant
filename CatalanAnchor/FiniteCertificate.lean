import CatalanAnchor.Bounds
import CatalanAnchor.Scoping

namespace CatalanAnchor

/-- An unconditional finite scope, obtained from the proved rational enclosure.
It excludes denominators at most ten; it does not assert irrationality. -/
theorem NATIVE_CATALAN_FINITE_SCOPE_TEN :
    ∀ q : ℚ, q.den ≤ 10 → (q : ℝ) ≠ nativeCatalan := by
  apply NATIVE_CATALAN_DENOMINATOR_SCOPE (-1) 1 10 (by norm_num)
  · push_cast
    linarith [catalan_lt_one]
  · push_cast
    linarith [catalan_finite_enclosure.1]

end CatalanAnchor
