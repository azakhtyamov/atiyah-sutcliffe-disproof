# Atiyah–Sutcliffe Conjecture 1 is false

`AtiyahSutcliffeDisproof.lean` is a single Lean 4 file proving that the Atiyah–Sutcliffe conjecture 1,
as formalised in [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
(`AtiyahSutcliffe.conjecture_one` in `FormalConjectures/Arxiv/1102.4662/AtiyahSutcliffe.lean`), is false:

```lean
theorem AtiyahSutcliffe.conjecture_one_false :
    ¬ ∀ {n : ℕ} (x : Fin n → Point), Function.Injective x → LinearIndependent ℂ (pointPolynomial x)
-- depends on axioms: [propext, Classical.choice, Quot.sound]
```

The counterexample has 46 points: the helix points `(sin((2j+1)θ), (2j+1)·b, cos((2j+1)θ))`, `j = 0 … 22`,
with their images under the half-turn `(x, y, z) ↦ (−x, −y, z)`, and one pair moved to a zero of the Schur
residual of the even coefficient block (`tan(θ/2) = a ≈ 0.0685930529198825`, `b ≈ 0.3018996198236849`).
The zero is certified by a Newton–Kantorovich argument in 320-bit interval arithmetic that the Lean kernel
re-evaluates; no floating point, no `native_decide`, no `sorry`.

## Verify

Toolchain: Lean 4.33.1, Mathlib `v4.33.1` (the pin of formal-conjectures). In a checkout of
formal-conjectures:

```
lake build 'FormalConjectures.Arxiv.«1102.4662».AtiyahSutcliffe'
lake env lean AtiyahSutcliffeDisproof.lean
```

or `FC=/path/to/formal-conjectures ./verify.sh`. The file takes about ten minutes to check (kernel
evaluation of the certificate; peak memory about 16 GB); the last line printed is the axiom list above.

## Contents

The file concatenates the modules of the development that produced it: the lemma library `Atiyah.Facts`
(verified lemmas of the Crucian study that found the witness; statements as generated), then the readable
certificate layer `Atiyah.*`: fixed-point interval arithmetic, dual numbers, the coefficient program,
pivoted elimination, the Newton–Kantorovich check, the witness data and computation, the kernel checks (per
row, from `eval%` snapshots), the enclosure chain to the column dependence, and the final theorems.
