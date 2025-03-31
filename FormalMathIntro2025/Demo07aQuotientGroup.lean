import Mathlib.Tactic



namespace AaltoFormalMath2025


section quotient_group_example
/-!
### Another example in the spirit of Section07, sheet 3
-/

-- Let `G` be a group.
variable (G : Type) [Group G]

-- Let `N ⊆ G` be a normal subgroup.
variable (N : Subgroup G) [N.Normal] -- `N.Normal` is shorthand for `Subgroup.Normal N`.

-- the quotient group `G ⧸ N`
#check G ⧸ N -- `Type` (the quotient type).
#synth Group (G ⧸ N ) -- Type class inference finds an instance of `Group` on the quotient.

open QuotientGroup -- ...so that we can write `mk'` instead of `QuotientGroup.mk'`

#check (mk' N : G →* G ⧸ N) -- The canonical projection `G → G ⧸ N`, as a group homomorphism.

-- Buzzard does this (and `exact?` finds it).
example (x y : G) : mk' N x = mk' N y ↔ ∃ n ∈ N, x * n = y := by
  exact mk'_eq_mk' N

-- Then how about this?
example (x y : G) : mk' N x = mk' N y ↔ ∃ n ∈ N, n * x = y := by
  -- `exact?` does not find anything.
  -- I think this lemma is missing, and I don't really know why...
  -- (Although maybe it is not surprising that left cosets are slightly preferred in this context.)
  -- So let's just do it.
  rw [mk'_eq_mk' N]
  constructor
  · intro h
    obtain ⟨z, z_mem_N, hz⟩ := h
    use x * z * x⁻¹
    constructor
    · apply ‹N.Normal›.conj_mem -- `exact?` basically finds this but there is some inference issue.
      exact z_mem_N
    · rw [hz]
      group
  · intro h
    obtain ⟨z, z_mem_N, hz⟩ := h
    use x⁻¹ * z * x⁻¹⁻¹ -- slightly crazy way of writing this, but makes later steps easier.
    constructor
    · apply ‹N.Normal›.conj_mem -- `exact?` basically finds this but there is some inference issue.
      exact z_mem_N
    · rw [← hz]
      group

end quotient_group_example


end AaltoFormalMath2025
