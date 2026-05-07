/- R4. SARSA(λ) — state-action-space analog of TD(λ). -/
import CreditAssignment.Basic
import CreditAssignment.EligibilityTrace

namespace CreditAssignment
namespace SARSALambda

/-- I4f: SARSA(λ) has no native similarity generalization. The update at
    (s_t, a_t) contributes nothing to Q(s_t, a') for a' ≠ a_t before
    an eligibility-trace mechanism narrows to (s,a) pairs. -/
theorem sarsaLambda_no_native_similarity : True := by
  trivial  -- placeholder; to be restated precisely + proved from the update form

end SARSALambda
end CreditAssignment
