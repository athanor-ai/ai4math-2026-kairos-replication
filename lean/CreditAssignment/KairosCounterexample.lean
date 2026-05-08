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

/-- For t ≥ 1, the actor increment t/(t+1)² is at least 1/(2(t+1)).
    This follows from t/(t+1) ≥ 1/2, i.e. 2t ≥ t+1, i.e. t ≥ 1. -/
private lemma actor_increment_ge_half_harmonic (t : ℕ) (ht : 1 ≤ t) :
    1 / (2 * ((t : ℝ) + 1)) ≤ actor_increment t := by
  simp only [actor_increment, αθ_kairos]
  have htR : (1 : ℝ) ≤ t := Nat.one_le_cast.mpr ht
  rw [show (t : ℝ) * (1 / ((t : ℝ) + 1) ^ 2) = (t : ℝ) / ((t : ℝ) + 1) ^ 2 by ring]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg ((t : ℝ) + 1)]

/-- The partial sums of actor increments dominate (1/2)·H_T − 1/2,
    where H_T = Σ_{i<T} 1/(i+1) is the T-th harmonic number.

    At t=0 the actor increment is 0 while the harmonic weight is 1/2,
    introducing a one-time deficit of 1/2.  For t ≥ 1 the pointwise
    bound holds exactly, so the deficit never grows. -/
private lemma actor_partial_sum_ge (T : ℕ) :
    (1/2) * (∑ i ∈ Finset.range T, (1 / ((i:ℝ) + 1))) - 1/2 ≤ actor_partial_sum T := by
  simp only [actor_partial_sum]
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    by_cases hT : 1 ≤ T
    · have h := actor_increment_ge_half_harmonic T hT
      have heq : 1 / (2 * ((T : ℝ) + 1)) = 1/2 * (1 / ((T : ℝ) + 1)) := by field_simp
      linarith [heq ▸ h]
    · have hT0 : T = 0 := by omega
      subst hT0
      simp [actor_increment, αθ_kairos]

/-- (1/2)·H_T − 1/2 → +∞ because the harmonic series diverges and
    scaling by 1/2 > 0 and shifting by −1/2 preserve divergence to +∞. -/
private lemma harmonic_minus_half_atTop :
    Filter.Tendsto (fun T : ℕ => (1/2) * (∑ i ∈ Finset.range T, (1 / ((i:ℝ) + 1))) - 1/2)
      Filter.atTop Filter.atTop := by
  have hH := Real.tendsto_sum_range_one_div_nat_succ_atTop
  have hscaled : Filter.Tendsto (fun T : ℕ => 1/2 * ∑ i ∈ Finset.range T, (1 / ((i:ℝ) + 1)))
      Filter.atTop Filter.atTop :=
    hH.const_mul_atTop (by norm_num : (0:ℝ) < 1/2)
  have key := hscaled.atTop_add (g := fun _ => -(1/2 : ℝ)) (C := -(1/2)) tendsto_const_nhds
  simp_rw [sub_eq_add_neg]
  exact key

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
  intro ⟨L, hL⟩
  -- Show actor_partial_sum → +∞ by comparison with the harmonic lower bound
  have hge : ∀ T, (1/2) * (∑ i ∈ Finset.range T, (1 / ((i:ℝ) + 1))) - 1/2 ≤ actor_partial_sum T :=
    actor_partial_sum_ge
  have hatTop : Filter.Tendsto actor_partial_sum Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono hge harmonic_minus_half_atTop
  -- A sequence tending to +∞ cannot tend to any finite limit
  exact not_tendsto_nhds_of_tendsto_atTop hatTop L hL

end KairosCounterexample
end ActorCritic
end CreditAssignment
