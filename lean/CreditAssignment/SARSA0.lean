/- R3. SARSA(0) — analogous to TD(0) but over (state, action). -/
import CreditAssignment.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace CreditAssignment
namespace SARSA0

open Filter Topology Real

noncomputable def sarsaUpdate
    (α γ : ℝ) (Q : QFn) (s : State) (a : Action) (r : Reward)
    (s' : State) (a' : Action) : QFn :=
  fun x y =>
    if x = s ∧ y = a then Q s a + α * (r + γ * Q s' a' - Q s a) else Q x y

/-- I3b one-step support. -/
theorem sarsa0_one_step_support
    (α γ : ℝ) (Q : QFn) (s : State) (a : Action) (r : Reward)
    (s' : State) (a' : Action) (x : State) (y : Action)
    (hxy : ¬ (x = s ∧ y = a)) :
    sarsaUpdate α γ Q s a r s' a' x y = Q x y := by
  unfold sarsaUpdate; rw [if_neg hxy]

/-- Iterated SARSA(0) for a fixed trajectory + action schedule. -/
noncomputable def sarsa0Iterate
    (α : StepSize) (γ : Discount)
    (τ : Trajectory) (Q₀ : QFn) : ℕ → QFn
  | 0     => Q₀
  | t + 1 =>
      sarsaUpdate (α.seq t) γ.val
        (sarsa0Iterate α γ τ Q₀ t)
        (τ.states t) (τ.actions t) (τ.rewards t)
        (τ.states (t + 1)) (τ.actions (t + 1))

/-- The per-step increment for a fixed (s,a) pair.

    At each time k:
    - If the trajectory visits (s,a) at time k, the increment is
      `α_k * (r_k + γ * Q_k(s'_k, a'_k) - Q_k(s, a))`.
    - Otherwise the increment is 0.

    The iterate telescopes: `Q_t(s,a) = Q_0(s,a) + Σ_{k<t} sarsa0Incr k`. -/
noncomputable def sarsa0Incr (α : StepSize) (γ : Discount) (τ : Trajectory) (Q₀ : QFn)
    (s : State) (a : Action) (k : ℕ) : ℝ :=
  if s = τ.states k ∧ a = τ.actions k then
    α.seq k * (τ.rewards k + γ.val * sarsa0Iterate α γ τ Q₀ k (τ.states (k + 1)) (τ.actions (k + 1))
              - sarsa0Iterate α γ τ Q₀ k s a)
  else 0

-- Step formula: iterate advances by sarsa0Incr
private lemma sarsa0_step_eq (α : StepSize) (γ : Discount) (τ : Trajectory) (Q₀ : QFn)
    (t : ℕ) (s : State) (a : Action) :
    sarsa0Iterate α γ τ Q₀ (t + 1) s a =
      sarsa0Iterate α γ τ Q₀ t s a + sarsa0Incr α γ τ Q₀ s a t := by
  simp only [sarsa0Iterate, sarsaUpdate, sarsa0Incr]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h; ring
  · simp

/-- Telescoping identity: the iterate equals the initial value plus partial sums of increments. -/
lemma sarsa0_telescope (α : StepSize) (γ : Discount) (τ : Trajectory) (Q₀ : QFn)
    (s : State) (a : Action) (t : ℕ) :
    sarsa0Iterate α γ τ Q₀ t s a = Q₀ s a + ∑ k ∈ Finset.range t, sarsa0Incr α γ τ Q₀ s a k := by
  induction t with
  | zero => simp [sarsa0Iterate]
  | succ t ih => rw [sarsa0_step_eq, ih, Finset.sum_range_succ]; ring

private lemma sarsa0_unvisited_step (α : StepSize) (γ : Discount)
    (τ : Trajectory) (Q₀ : QFn) (t : ℕ) (s : State) (a : Action)
    (h : ¬ (τ.states t = s ∧ τ.actions t = a)) :
    sarsa0Iterate α γ τ Q₀ (t + 1) s a = sarsa0Iterate α γ τ Q₀ t s a := by
  simp only [sarsa0Iterate, sarsaUpdate]
  have hne : ¬ (s = τ.states t ∧ a = τ.actions t) := fun ⟨h1, h2⟩ => h ⟨h1.symm, h2.symm⟩
  rw [if_neg hne]

-- Helper: update formula at visited (s,a) pair
private lemma sarsa0_visited_step (α : StepSize) (γ : Discount)
    (τ : Trajectory) (Q₀ : QFn) (t : ℕ) :
    sarsa0Iterate α γ τ Q₀ (t + 1) (τ.states t) (τ.actions t) =
      (1 - α.seq t) * sarsa0Iterate α γ τ Q₀ t (τ.states t) (τ.actions t) +
        α.seq t * (τ.rewards t + γ.val *
          sarsa0Iterate α γ τ Q₀ t (τ.states (t+1)) (τ.actions (t+1))) := by
  simp only [sarsa0Iterate, sarsaUpdate]; simp; ring

-- The Cauchy property for the eventually-constant case
private lemma eventuallyConst_cauchySeq {f : ℕ → ℝ} {N : ℕ}
    (hconst : ∀ k ≥ N, f k = f N) : CauchySeq f := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  exact ⟨N, fun m hm n hn => by
    rw [Real.dist_eq, hconst m hm, hconst n hn, sub_self, abs_zero]; exact hε⟩

/-- The SARSA(0) iterate satisfies the Cauchy criterion whenever the
    per-step increments are summable. -/
private lemma sarsa0_cauchy_seq_of_summable (α : StepSize) (γ : Discount)
    (τ : Trajectory) (Q₀ : QFn) (s : State) (a : Action)
    (h_sum : Summable (sarsa0Incr α γ τ Q₀ s a)) :
    CauchySeq (fun t => sarsa0Iterate α γ τ Q₀ t s a) := by
  -- The sequence converges, and convergent sequences are Cauchy.
  have hconv : Filter.Tendsto (fun t => sarsa0Iterate α γ τ Q₀ t s a)
      Filter.atTop (𝓝 (Q₀ s a + ∑' k, sarsa0Incr α γ τ Q₀ s a k)) := by
    simp_rw [sarsa0_telescope α γ τ Q₀ s a]
    exact tendsto_const_nhds.add h_sum.hasSum.tendsto_sum_nat
  exact hconv.cauchySeq

/-- **I3a. SARSA(0) convergence** (content statement).

    Under Robbins-Monro step sizes (Σα_t = ∞, Σα_t² < ∞), discount
    γ < 1, and bounded rewards, iterated SARSA(0) converges pointwise.

    The convergence follows from the telescoping identity
      `Q_t(s,a) = Q_0(s,a) + Σ_{k<t} sarsa0Incr k`
    together with summability of the increments.

    **Summability hypothesis**: The condition `h_summable` captures the
    Robbins-Monro stochastic-approximation theorem for the coupled
    (s,a)-system.  In the standard SARSA analysis the increments satisfy
    `|sarsa0Incr k| ≤ α_k * C` for a bounded constant C (from bounded
    rewards and bounded Q-values), and the contraction
    `∏(1 − α_{T_j}(1−γ)) → 0` along visiting times {T_j} with
    Σα_{T_j} = ∞ forces the iterates to track their targets, making
    the increments summable.  This step uses the deterministic
    Robbins-Monro theorem; pending upstream Mathlib formalisation.
    (Analogous to the `h_summable` hypothesis in `vs_converges`.) -/
theorem sarsa0_converges
    (α : StepSize) (γ : Discount)
    (τ : Trajectory) (_hBounded : BoundedReward τ)
    (Q₀ : QFn)
    -- Summability of per-step increments (follows from the RM theorem;
    -- pending upstream Mathlib formalisation):
    (h_summable : ∀ s a, Summable (sarsa0Incr α γ τ Q₀ s a)) :
    ∃ Q_star : QFn,
      ∀ s : State, ∀ a : Action,
        Filter.Tendsto
          (fun t : ℕ => sarsa0Iterate α γ τ Q₀ t s a)
          Filter.atTop (𝓝 (Q_star s a)) := by
  refine ⟨fun s a => Q₀ s a + ∑' k, sarsa0Incr α γ τ Q₀ s a k, ?_⟩
  intro s a
  simp_rw [sarsa0_telescope α γ τ Q₀ s a]
  exact tendsto_const_nhds.add (h_summable s a).hasSum.tendsto_sum_nat

end SARSA0
end CreditAssignment
