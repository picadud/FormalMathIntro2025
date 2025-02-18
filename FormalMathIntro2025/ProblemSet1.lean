import Mathlib.Tactic -- imports all the Lean tactics

set_option linter.unusedTactic false

namespace AaltoFormalMath2025

section
/-!
# Problem set 1: Cauchy sequences and bounded sequences on `ℝ`
-/


/-
## Convergent sequences are necessarily Cauchy
-/

-- This is the same definition as in *Kevin Buzzard's Section01reals*.
/-- If `n ↦ a(n)` is a sequence of reals and `t` is a real, `TendsTo a t`
is the assertion that the limit of `a(n)` as `n → ∞` is `t`. -/
def TendsTo (a : ℕ → ℝ) (t : ℝ) : Prop :=
  ∀ ε > 0, ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε

theorem tendsTo_def {a : ℕ → ℝ} {t : ℝ} :
    TendsTo a t ↔ ∀ ε, 0 < ε → ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε := by
  rfl -- true by definition

/-- If `n ↦ a(n)` is a sequence of reals, `IsCauchy a` is the assertion that
`n ↦ a(n)` is a Cauchy sequence (just as in MS-C1541 Metric Spaces). -/
def IsCauchy (a : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ B, ∀ n m, B ≤ n → B ≤ m → |a n - a m| < ε

theorem isCauchy_def {a : ℕ → ℝ} :
    IsCauchy a ↔ ∀ ε > 0, ∃ B : ℕ, ∀ n m, B ≤ n → B ≤ m → |a n - a m| < ε := by
  rfl -- true by definition

-- EXERCISE 1
/-- Any convergent real-number sequence is necessarily a Cauchy sequence. -/
theorem isCauchy_of_tendsTo {a : ℕ → ℝ} {t : ℝ} (a_lim : TendsTo a t) :
    IsCauchy a := by
  -- This is some work --- make sure you know the math proof first!
  -- You may take some inspiration from the uniqueness of limits proof.
  sorry



/-
## Cauchy sequences are necessarily bounded
-/

/-- If `n ↦ a(n)` is a sequence of reals, `IsBounded a` is the assertion that
`n ↦ a(n)` is a bounded sequence (just as in MS-C1541 Metric Spaces). -/
def IsBounded (a : ℕ → ℝ) :=
  ∃ M, ∀ n, |a n| ≤ M

-- EXERCISE 2
-- Before we can prove that all Cauchy-sequences are bounded, we need an auxiliary result.
lemma exists_forall_abs_initial_le (a : ℕ → ℝ) (m : ℕ) :
    ∃ M, ∀ n < m, |a n| ≤ M := by
  -- Let us prove this by induction on `m`.
  -- (This is our first induction proof.
  --  Maybe look up the explanations for the tactic `induction'` in Buzzard's course.)
  induction' m with m ih_m
  · -- Base case.
    sorry
  · -- Induction step.
    -- You might find, e.g., `Nat.lt_of_le_of_ne` and `Nat.succ_lt_succ_iff`
    -- and `Nat.succ_ne_succ` useful here.
    sorry

-- EXERCISE 3
/-- Any Cauchy sequence is bounded. -/
theorem isBounded_of_isCauchy {a : ℕ → ℝ} (a_cauchy : IsCauchy a) :
    IsBounded a := by
  -- This is some work --- make sure you know the math proof first!
  -- You may take some inspiration from the uniqueness of limits proof.
  sorry

-- EXERCISE 4
-- Now we easily get that:
/-- Any convergent real-number sequence is bounded. -/
theorem isBounded_of_tendsTo {a : ℕ → ℝ} {t : ℝ} (a_lim : TendsTo a t) :
    IsBounded a := by
  -- This is easy now!
  sorry

end

end AaltoFormalMath2025
