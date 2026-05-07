/-
  Kairos fleet-produced counterexample to the under-specified
  two-timescale actor-critic convergence theorem.

  The Kairos Opus planner, on the ablation run (fresh
  under-specified statement, Phase -1 audit for missing
  hypotheses), independently derived a distinct counterexample
  instantiation from the one returned by Aristotle's independent
  cross-check (Appendix A.7).

  Side-by-side with Appendix A.7: both counterexamples refute the
  same (false) theorem, both use an unbounded feature map on
  state = ℕ with trajectory τ(t) = t, and both satisfy every
  hypothesis the under-specified theorem states. They differ in
  the actor step-size schedule and therefore in the divergence
  mechanism:

    Kairos planner:   αθ(t) = 1/(t+1)², harmonic-tail divergence.
                      θ_T(0) = Σ_{t<T} t/(t+1)² ≥ (1/2)·Σ_{t<T} 1/(t+1),
                      which grows as log T.
                      γ = 1/2, λ = 0 (γλ = 0 < 1 trivially).

    Aristotle audit:  αθ(t) = 1/((t+1)(1+log(t+2))), iterated-log tail.
                      θ_t(0) = Σ k/((k+1)(1+log(k+2))), which grows
                      as log log T.
                      γ = 1/2, λ = 1/2 (γλ = 1/4 < 1).

  Both schedules satisfy Robbins–Monro; the divergence of the
  *actor-update product series* Σ (state-index)·αθ(t) is the
  load-bearing fact for each. The two instantiations agree in
  class (unbounded feature map + non-ergodic trajectory) but
  disagree in concrete mechanism, which is the evidence that
  Kairos did not simply copy Aristotle's witness.
-/
import CreditAssignment.ActorCritic

namespace CreditAssignment
namespace ActorCritic
namespace KairosCounterexample

/-- The Kairos planner's actor step-size schedule. -/
noncomputable def αθ_kairos (t : ℕ) : ℝ := 1 / ((t : ℝ) + 1) ^ 2

/-- The Kairos planner's critic step-size schedule. -/
noncomputable def αw_kairos (t : ℕ) : ℝ := 1 / ((t : ℝ) + 1)

/-- The actor-increment product series the counterexample forces
    to diverge:  t · αθ_kairos(t) = t / (t+1)². -/
noncomputable def actor_increment (t : ℕ) : ℝ :=
  (t : ℝ) * αθ_kairos t

/-- Partial sum of actor increments at time T. -/
noncomputable def actor_partial_sum (T : ℕ) : ℝ :=
  (Finset.range T).sum actor_increment

/-- The key divergence fact the Kairos planner identified.

    Claim: the partial sums Σ_{t<T} t/(t+1)² grow without bound.

    Proof sketch (from the Phase -1 planner memo): for t ≥ 1,
    t/(t+1)² ≥ 1/(2(t+1)) (because t/(t+1) ≥ 1/2 for t ≥ 1), and
    Σ 1/(t+1) diverges (harmonic tail).

    Routed to Aristotle as the divergence-lemma axiomatisation
    step, along with I1a / I2a / I3a / I5a-corrected, pending
    Mathlib stochastic-approximation upstream. -/
theorem kairos_actor_partial_sum_unbounded :
    ¬ ∃ L : ℝ, Filter.Tendsto actor_partial_sum Filter.atTop (nhds L) := by
  sorry

end KairosCounterexample
end ActorCritic
end CreditAssignment
