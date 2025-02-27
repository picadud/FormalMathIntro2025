import Mathlib.Tactic

set_option linter.unusedTactic false



namespace AaltoFormalMath2025


section Solving_equations_etc
/-!
### More examples in the spirit of Section02, sheets 1-2

Remember tactics `use` (handling ∃ by providing a witness) and `intro` (handling ∀),
as well as `norm_num` and `ring`.
-/

/-- This is *"Cardano's cubic"*.

There are of course soft existence arguments for roots of cubics, but here
you can just explicitly find a root and use it as a witness to the existential.

If you don't easily find a solution, feel free to use your favorite numerical
software to come up with an educated guess (which you can then prove), or ask
Google, or ask a friend. -/
theorem root_of_cardano_cubic :
    ∃ (x : ℝ), x ^ 3 = 15 * x + 4 := by
  use 4 -- Witness for x (we don't need the complicated solution formula with cube roots).
  norm_num
  done

/- This is asking you for a nontrivial *"Pythagorean triple"*. -/
theorem exists_pythagorean_triple :
    ∃ (a b c : ℕ), a ≠ 0 ∧ b ≠ 0 ∧ (a^2 + b^2 = c^2) := by
  use 3 -- Witness for a.
  use 4 -- Witness for b.
  use 5 -- Witness for c.
  refine ⟨?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · norm_num
  -- Note: `norm_num` works also in `ℕ` (not `ℝ`) and can close goals with `∧`.
  done

/-- Let's do one with a `∀` quantified, too. -/
example : -- Not bothering to give a name to this, so `example` rather than `theorem`.
    ∀ (a : ℝ), ∃ x, x^4 = 16 * a^4 := by
  intro a -- "Let a be a real number."
  use 2*a
  ring -- `norm_num` doesn't work, there is an unspecified real
       -- variable a in the formula, not an explicit number.
  done

/-- And one more (a factorization of an expression with a parameter). -/
example :
    ∀ (a : ℝ), ∃ (b : ℝ), ∀ (x : ℝ), x^2 - a^2 = (x - a) * (x - b) := by
  -- Maybe you can do this for extra practice.
  sorry

end Solving_equations_etc


end AaltoFormalMath2025
