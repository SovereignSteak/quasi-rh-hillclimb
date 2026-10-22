import IndependentTarget
import Candidate.Main

set_option autoImplicit false

namespace IndependentAudit

theorem verified : Target := by
  intro q inst χ s hs hpole
  exact Candidate.bound χ hs hpole

#print axioms verified
#print axioms Candidate.bound
#print verified

end IndependentAudit
