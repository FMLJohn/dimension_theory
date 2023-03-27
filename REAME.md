# Krull Dimension theory in Lean

Let $R$ be a commutative ring with unit, we define its krull dimension to be the length of the longest prime ideal chain $\mathfrak{p}_0 \subsetneq \mathfrak{p}_1 \subsetneq \dots \mathfrak{p}_n$ and 0 if there exists prime ideal chain of infinite length or if there does not exist any prime ideal chain at all. In Lean it is spelled out like the following:

```lean
structure prime_ideal_chain :=
(len : ℕ)
(chain : fin (len + 1) → ideal R)
(is_chain : strict_mono chain)
[is_prime : ∀ i, (chain i).is_prime]

class finite_dimensional_ring : Prop :=
(fin_dim : ∃ (M : prime_ideal_chain R), ∀ (N : prime_ideal_chain R), N.len ≤ M.len)

def krull_dim : ℕ := 
if H : finite_dimensional_ring R
then H.fin_dim.some.len
else 0
```

Alternatively, `krull_dim` could be defined to take values in `with_top (with_bot ℕ)` so that the zero ring would have negative infinity as its dimension and infinite dimensional ring would have positive infinity as its dimension. But we stick with `ℕ` for now.

## Results
If $R$ is finite dimensional and $S$ is not the zero ring, and if $R  → S$ is a surjective ring homomorphism, then $\dim S\le\dim R$. This is in [`krull_dimension.lean`](src/krull_dimension.lean#200)
```lean
theorem krull_dim_bounded [finite_dimensional_ring R]
  (S : Type*) [comm_ring S] [ nontrivial S]
  (f : R →+* S) (hf : function.surjective f) : krull_dim S ≤ krull_dim R
```
