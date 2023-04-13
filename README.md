<!-- markdownlint-disable no-duplicate-header -->

# Krull Dimension Theory in Lean

## Abstract approach

As discussed in [this Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/dimension.20of.20a.20ring.20.2F.20topological.20space/near/344117122), the theory of Krull dimensions should be defined on any partially ordered set then the Krull dimension of rings and topological spaces should be specializations of general definitions with appropriate partially ordered sets substituted. Here we adopt a (slightly) more general approach where the Krull dimension makes sense for any preordered sets $(S, \preccurlyeq)$ or simply $S$ if no confusion would occur.

A strict chain of $S$ with length $n$ is $s_0 \prec\dots\prec s_n$ with all $s_i\in S$. Then the Krull dimension of $S$ is the supremum of lengths of all strict chains if lengths of all strict chains are bounded; if otherwise, then the Krull dimension of $S$ is negative infinity if $S$ is empty or positive infinity if $S$ contains strict chains of arbitrary length. Then the height of $s \in S$ is the Krull dimension of $\{x | x \preccurlyeq s\}$ with the induced preorder. If $S = \operatorname{Spec}R$ with inclusion as its ordering, then this definition of Krull dimension and height agrees with the usual definition of Krull dimension of a ring and height of prime ideals. If $S$ is the set of all closed irreducible sets of a topological space, then this definition is the Krull dimension of a topological space in the usual sense as well.

Let $\alpha$ and $\beta$ are two preordered sets. If $f : \alpha → \beta$ is strictly monotonic, then any strict chain of $\alpha$ can be pushed out to a strict chain of $\beta$, hence the Krull dimension of $\alpha$ is no greater than that of $\beta$. Dually, if $f : \alpha \to \beta$ is strictly comonotonic (i.e. $f(x) \prec_\beta f(y) \implies x \prec_\alpha y$, for all $x, y \in \beta$) and surjective, then any strict chain of $\beta$ can be pulled back to that of $\alpha$; hence the Krull dimension of $\beta$ is no greater than that of $\alpha$. Combining these two lemmas, order isomorphic sets have the same Krull dimension. The Krull dimension of $\alpha$ can also be computed as the supremum of the heights of all its elements.

### Implementations

Let $\alpha$ be a preordered set, then `strict_chain α` is implemented as

```lean
structure strict_chain :=
(len : ℕ)
(func : fin (len + 1) → α)
(strict_mono' : strict_mono func)
```

Then the Krull dimension of $\alpha$ is implemented as the supremum of lengths of all strict chains

```lean
@[reducible] def krull_dim : ℕ±∞ := 
⨆ (p : strict_chain α), p.len
```

where `ℕ±∞` is just `with_bot (with_top ℕ)`.

Then for any $a \in \alpha$, height and coheight of $a$ are implemented as

```lean
def height (a : α) : ℕ±∞ := 
krull_dim (set.Iic a)

def coheight (a : α) : ℕ±∞ := 
krull_dim (set.Ici a)
```

Then the Krull dimension of a ring is implemented as

```lean
def ring_krull_dim (R : Type*) [comm_ring R] : ℕ±∞ :=
krull_dim (prime_spectrum R)
```

and the Krull dimension of a topological space is implemented as

```lean
def topological_krull_dim (T : Type*) [topological_space T] : ℕ±∞ :=
krull_dim { s : set T | is_closed s ∧ is_irreducible s }
```

### Results

- An empty preordered set is negative infinity dimensional
  
  ```lean
  lemma krull_dim_eq_bot_of_is_empty [is_empty α] :   krull_dim α = ⊥ := sorry
  ```

- if $\alpha$ does not have the longest strict chain, then it is infinite-dimensional

  ```lean
  lemma krull_dim_eq_top_of_no_top_order [nonempty α]   [no_top_order (strict_chain α)] : 
    krull_dim α = ⊤ := sorry
  ```

- if $\alpha$ has a strict chain of the longest length, then $\dim\alpha$ is just the length of the longest chain

  ```lean
  lemma krull_dim_eq_len_of_order_top' [order_top   (strict_chain α)] 
    (q : strict_chain α) (h : is_top q) :
    krull_dim α = q.len := sorry
  ```

- if $f : \alpha \to \beta$ is a strictly monotonic function, then $\dim\alpha \le \dim\beta$

  ```lean
  lemma krull_dim_le_of_strict_mono (f : α → β) (hf :   strict_mono f) : krull_dim α ≤ krull_dim β :=
  ```
  
  and if $f : \alpha \to \beta$ is a surjective and strictly comonotic function, then $\dim \beta \le \dim \alpha$

  ```lean
  lemma krull_dim_le_of_strict_comono_and_surj 
    (f : α → β) (hf : strict_comono f) (hf' : function.surjective f) : krull_dim β ≤ krull_dim α := sorry
  ```

  and hence, order isomorphism preserves dimension

  ```lean
  lemma krull_dim_eq_of_order_iso (f : α ≃o β) : krull_dim α = krull_dim β :=
  ```

- Dual orders have the same dimension

  ```lean
  lemma krull_dim_eq_order_dual : krull_dim α =   krull_dim αᵒᵈ :=
  ```

- if $a_1 \le a_2$, then height of $a_1$ is no greater than that of $a_2$

  ```lean
  lemma height_mono {a b : α} (h : a ≤ b) : height a ≤ height b := sorry
  ```
  
  and if $a_1 \le a_2$, then coheight of $a_1$ is no smaller than that of $a_2$

  ```lean
  lemma coheight_antitone {a b : α} (h : a ≤ b) :   coheight b ≤ coheight a := sorry
  ```

  and when $\alpha$ is partially ordered, they can be computed by the length of chains with specific starting and ending points

  ```lean
  lemma height_eq (a : α) : 
  height a = ⨆ (p : strict_chain α) (hp : p ⟨p.len, lt_add_one _⟩ = a), p.len := sorry

  lemma coheight_eq (a : α) :
  coheight a = ⨆ (p : strict_chain α) (hp : p 0 = a), p.len := sorry
  ```

- In a partially ordered set $\alpha$, for every $a \in \alpha$, we have that $\operatorname{ht}(a) + \operatorname{coht}(a) \le \dim \alpha$ [Matsumura, p30].
  
  ```lean
  lemma height_add_coheight_le (a : α) : height a + coheight a ≤ krull_dim α :=
  ```

- The ring Krull dimension and the topological dimension of the prime spectrum of a ring are the same

  ```lean
  lemma eq_topological_krull_dim (R : Type*) [comm_ring  R] :
    ring_krull_dim R = topological_krull_dim (prime_spectrum R) :=
  ```

- A field is zero-dimensional and a PID that is not a field is one dimensional

  ```lean
  lemma ring_krull_dim.eq_zero_of_field (F : Type*) [field F] : ring_krull_dim F = 0 := sorry
  lemma PID_eq_one_of_not_field (R : Type*) [comm_ring R] [is_principal_ideal_ring R] [is_domain R] 
  (hR : ¬ is_field R) :
  ring_krull_dim R = 1 := sorry
  ```

- The Krull dimension of ring $R$ is equal to the supremum of heights of maximal ideals [00KG](https://stacks.math.columbia.edu/tag/00KG)
  
  ```lean
  lemma eq_sup_height_maximal_ideals (R : Type*) [comm_ring R] :
  ring_krull_dim R = ⨆ (p : prime_spectrum R) (hp : p.as_ideal.is_maximal), height p := sorry
  ```

## Deprecated approach

In [`krull_dimension.lean`](src/krull_dimension.lean), there is a definition of Krull dimension considering only commutative rings.

Let $R$ be a commutative ring with a unit, we define its Krull dimension to be the length of the longest prime ideal chain $\mathfrak{p}_0 \subsetneq \mathfrak{p}_1 \subsetneq \dots \mathfrak{p}_n$ and 0 if there exist prime ideal chains of longer and longer lengths or if there does not exist any prime ideal chain at all. In Lean it is spelled out like the following:

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

Alternatively, `krull_dim` could be defined to take values in `with_top (with_bot ℕ)` so that the zero ring would have negative infinity as its dimension and infinite-dimensional rings would have positive infinity as their dimensions. But we stick with `ℕ` for now.

### Results

If $R$ is finite-dimensional and $S$ is not the zero ring, and if $R  → S$ is a surjective ring homomorphism, then $\dim S\le\dim R$. This is in [`krull_dimension.lean`](src/krull_dimension.lean#200)

```lean
theorem krull_dim_bounded [finite_dimensional_ring R]
  (S : Type*) [comm_ring S] [ nontrivial S]
  (f : R →+* S) (hf : function.surjective f) : krull_dim S ≤ krull_dim R
```
