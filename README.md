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

## Abstract approach

As discussed in [this Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/dimension.20of.20a.20ring.20.2F.20topological.20space/near/344117122), the theory of Krull dimension should be defined on any partially ordered set then Krull dimension of rings and topological spaces should be specialization of general definitions with appropriate posets substituted in. Here we adopt a (slightly) more general approach where Krull dimension makes sense for any preordered-sets $(S, \preccurlyeq)$ or simply $S$ if no confusion would occur.

A strict chain of $S$ with length $n$ is $s_0 \prec\dots\prec s_n$ with all $s_i\in S$. Then the krull dimension of $S$ is the supremum of length of all strict chains if the length of all strict chains are bounded; if otherwise, then Krull dimension of $S$ is negative infinity if $S$ is empty or positive infinity if $S$ contains strict chains of arbitrary length. Then the height of $s \in S$ is the Krull dimension of $\{x | x \preccurlyeq s\}$ with the induced preorder. If $S = \operatorname{Spec}R$ with inclusion as its ordering, then this definition of Krull dimension and height agrees with the usual definition of Krull dimension of a ring and height of prime ideals. If $S$ is the set of all closed irreducible sets of a topological space, then this definition is the Krull dimension of a topological space in the usual sense as well.

Let $\alpha$ and $\beta$ are two preordered sets. If $f : \alpha → \beta$ is strictly monotonic, then any strict chain of $\alpha$ can be pushed out to a strict chain of $\beta$, hence the Krull dimension of $\alpha$ is no greater than that of $\beta$. Dually, if $f : \alpha \to \beta$ is strictly comonotonic (i.e. $f(x) \prec_\beta f(y) \implies x \prec_\alpha y$, for all $x, y \in \beta$) and surjective, then any strict chain of $\beta$ can be pulled back to that of $\alpha$; hence krull dimension of $\beta$ is no greater than that of $\alpha$. Combining these two lemmas, order isomorphic sets have the same krull dimension. Krull dimension of $\alpha$ can also be computed as the supremum of the heights of all its elements.
