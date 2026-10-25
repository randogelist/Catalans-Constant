import CatalanAnchor.AdmissionClosure

/-!
# Exact closure by unbounded finite admissions

The finite admission predicate is independent of the successor.  A successor
with the required laws exists exactly when accepted coordinates have cofinal
scope.  The choice construction below is a mathematical equivalence; it does
not establish the cofinal-admission hypothesis or termination of a search.
-/

noncomputable section

namespace CatalanAnchor.RieszAdmission

open GPBKQRXY.Riesz

/-- Accepted coordinates exist at every requested finite denominator scope. -/
def CofinalAdmission : Prop :=
  ∀ D : ℕ, ∃ c : Coordinates 3,
    Admissible (system id) c ∧ D ≤ scope c

/-- The same condition expressed entirely through the existing finite check. -/
def CofinalCheckedAdmission : Prop :=
  ∀ D : ℕ, ∃ c : Coordinates 3,
    check (system id) c = true ∧ D ≤ scope c

/-- Changing the successor changes no local admission condition. -/
theorem admissible_independent_of_next
    (next₁ next₂ : Coordinates 3 → Coordinates 3) (c : Coordinates 3) :
    Admissible (system next₁) c ↔ Admissible (system next₂) c := by
  rfl

/-- Cofinal admission supplies the universal successor by selection at twice
the input scope.  No algorithmic termination theorem is asserted here. -/
def successorOfCofinal (h : CofinalAdmission) : CatalanSuccessor where
  next c := Classical.choose (h (2 * scope c))
  preserves := by
    intro c _
    exact (Classical.choose_spec (h (2 * scope c))).1
  doubles := by
    intro c _
    exact (Classical.choose_spec (h (2 * scope c))).2

/-- A genuine lock makes the admitted seed generate arbitrarily large scope. -/
theorem cofinal_of_lock
    (next : Coordinates 3 → Coordinates 3) (L : LockLaws (system next)) :
    CofinalAdmission := by
  intro D
  obtain ⟨n, hn⟩ := exists_small_error (system next) L seed
    (seed_admissible next) (D + 1) (by omega)
  let c := orbit (system next) seed n
  have hc : Admissible (system next) c :=
    orbit_admissible (system next) L seed (seed_admissible next) n
  have hp : (0 : ℚ) < scope c := by
    exact_mod_cast scope_pos_of_admissible next hc
  change ((D + 1 : ℕ) : ℚ) * (1 / (scope c : ℚ)) < 1 at hn
  rw [mul_one_div] at hn
  have hDq : ((D + 1 : ℕ) : ℚ) < scope c := (div_lt_one hp).mp hn
  have hDn : D + 1 < scope c := by exact_mod_cast hDq
  exact ⟨c, hc, by omega⟩

/-- The remaining successor-existence problem is exactly cofinal admission. -/
theorem successor_iff_cofinal :
    Nonempty CatalanSuccessor ↔ CofinalAdmission := by
  constructor
  · rintro ⟨T⟩
    exact cofinal_of_lock T.next T.lockLaws
  · intro h
    exact ⟨successorOfCofinal h⟩

/-- Allowing arbitrary lock laws does not weaken the cofinal-admission target. -/
theorem lock_iff_cofinal :
    (∃ next : Coordinates 3 → Coordinates 3, LockLaws (system next)) ↔
      CofinalAdmission := by
  constructor
  · rintro ⟨next, L⟩
    exact cofinal_of_lock next L
  · intro h
    exact ⟨(successorOfCofinal h).next, (successorOfCofinal h).lockLaws⟩

theorem cofinal_iff_checked : CofinalAdmission ↔ CofinalCheckedAdmission := by
  constructor
  · intro h D
    obtain ⟨c, hc, hD⟩ := h D
    exact ⟨c, (check_eq_true_iff (system id) c).mpr hc, hD⟩
  · intro h D
    obtain ⟨c, hc, hD⟩ := h D
    exact ⟨c, (check_eq_true_iff (system id) c).mp hc, hD⟩

theorem successor_iff_checked :
    Nonempty CatalanSuccessor ↔ CofinalCheckedAdmission :=
  successor_iff_cofinal.trans cofinal_iff_checked

/-- Conditional arithmetic endpoint, with all remaining existence content
displayed in one universally quantified finite-check hypothesis. -/
theorem CATALAN_IRRATIONAL_OF_COFINAL (h : CofinalAdmission) :
    Irrational catalan :=
  CATALAN_IRRATIONAL_OF_SUCCESSOR (successorOfCofinal h)

theorem NATIVE_CATALAN_IRRATIONAL_OF_COFINAL (h : CofinalAdmission) :
    Irrational nativeCatalan :=
  NATIVE_CATALAN_IRRATIONAL_OF_SUCCESSOR (successorOfCofinal h)

theorem NATIVE_CATALAN_IRRATIONAL_OF_COFINAL_CHECKS
    (h : CofinalCheckedAdmission) : Irrational nativeCatalan :=
  NATIVE_CATALAN_IRRATIONAL_OF_COFINAL (cofinal_iff_checked.mpr h)

end CatalanAnchor.RieszAdmission
