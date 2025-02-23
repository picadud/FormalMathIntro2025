import Mathlib

namespace AaltoFormalMath2025


noncomputable section a_very_very_interesting_proposition

-- A perfectly fine and very very interesting statement (defined in Mathlib):
#check RiemannHypothesis

-- Whether or not the `sorry` below can be filled in is not known to the
-- human kind at the moment.
-- In this course we will be filling in much easier `sorry`es.
theorem can_one_prove_this? : RiemannHypothesis := by
  unfold RiemannHypothesis
  sorry

-- Same with its negation, of course. Unknown to humanity.
theorem or_can_one_instead_prove_this? : ¬ RiemannHypothesis := by
  unfold RiemannHypothesis
  push_neg
  sorry

end a_very_very_interesting_proposition

end AaltoFormalMath2025
