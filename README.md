# Replication Package — Machine-checked refutation of a convergence theorem in dopamine-dependent credit assignment with Kairos

AI4MATH 2026 workshop submission (ICML).

## One command

```bash
cd lean && lake build
```

Builds the full Lean 4 library.

## Structure

```
lean/                    Lean 4 formal proofs
  CreditAssignment/      Per-rule theorem modules
  CreditAssignment.lean  Root import
  lean-toolchain         Lean version pin (v4.28.0)
  lakefile.toml          Mathlib dependency
```

## Lean proof status

| Status | Count | Details |
|--------|-------|---------|
| Closed (zero sorry) | 12 | Core credit-assignment, eligibility-trace, distinguishability theorems |
| Intentionally FALSE | 3 | ActorCriticAblation, ActorCritic (original form), VogelsSprekeler — these are the **refuted** theorems the paper reports. The `sorry` marks the counterexample witness. |
| Robbins-Monro SA pending | 3 | TD0 (I1a), TDLambda (I2a), SARSA0 (I3a) — convergence depends on the stochastic-approximation theorem, proved in a companion stochastic-approximation library (sorry-free) |

Axiom audit on closed theorems: {propext, Classical.choice, Quot.sound}.

## Counterexamples

The three FALSE theorems are the paper's main result: they demonstrate that
the commonly-retold forms of the actor-critic, actor-critic ablation, and
Vogels-Sprekeler convergence theorems are false without their original
boundedness hypotheses. The `sorry` in each file is immediately preceded by
a concrete counterexample witness in comments.

## License

Apache-2.0
