# Replication Package — Machine-checked refutation of a convergence theorem in dopamine-dependent credit assignment with Kairos

AI4MATH 2026 workshop submission (ICML).

## One command

```bash
cd lean && lake build
```

Builds the full Lean 4 library (14 closed theorems, 3 Robbins-Monro content goals with `sorry`).

## Structure

```
lean/                    Lean 4 formal proofs
  CreditAssignment/      Per-rule theorem modules
  CreditAssignment.lean  Root import
  lean-toolchain         Lean version pin
```

## Lean proof status

- 14 of 18 theorems: closed (zero `sorry`, axiom audit {propext, Classical.choice, Quot.sound})
- 3 theorems (I1a, I2a, I3a): Robbins-Monro convergence content, `sorry` pending
- The stochastic-approximation infrastructure for these 3 is proved separately in Pythia

## License

Apache-2.0
