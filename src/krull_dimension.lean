import ring_theory.ideal.basic
import ring_theory.localization.at_prime

noncomputable theory

variables (R : Type*) [comm_ring R]

/--
a chain of prime ideal of length `n` is `𝔭₀ ⊂ 𝔭₁ ⊂ ... ⊂ 𝔭ₙ` where all `𝔭ᵢ`s are prime ideals.
-/
structure prime_ideal_chain :=
(len : ℕ)
(chain : fin (len + 1) → ideal R)
(is_chain : strict_mono chain)
[is_prime : ∀ i, (chain i).is_prime]

namespace prime_ideal_chain

/--
If `R` is not the zero ring, then there is at least one prime ideal chain for `R` has a maximal 
ideal.
-/
instance [nontrivial R] : nonempty (prime_ideal_chain R) :=
nonempty.intro
{ len := 0,
  chain := λ _, (ideal.exists_maximal R).some,
  is_chain := by { rintros ⟨i, (hi : i < 1)⟩ ⟨j, (hj : j < 1)⟩ (hij : i < j), exfalso, linarith, },
  is_prime := λ _, (ideal.exists_maximal R).some_spec.is_prime }

instance [nontrivial R] : inhabited (prime_ideal_chain R) :=
{ default :=
  { len := 0,
    chain := λ _, (ideal.exists_maximal R).some,
    is_chain := by { rintros ⟨i, (hi : i < 1)⟩ ⟨j, (hj : j < 1)⟩ (hij : i < j), exfalso, linarith, },
    is_prime := λ _, (ideal.exists_maximal R).some_spec.is_prime } }

/--
Two prime ideal chains are equal when they have the same length and the same prime ideals.
-/
@[ext]
lemma ext (M N : prime_ideal_chain R)
(len_eq : M.len = N.len)
(chain_eq : ∀ (i : fin (M.len + 1)), M.chain i = N.chain i) :
M = N :=
begin
cases M with h l m,
cases N with h' l' m',
dsimp at *,
subst len_eq,
congr,
ext,
rw chain_eq,
norm_num,
end

end prime_ideal_chain

/--
A ring `R` is said to be finite dimensional if there is a prime ideal chain with the maximal length.
Note that according to this definition, the zero ring is not finite dimensional, for it has no prime
ideal chains.
-/
class finite_dimensional_ring : Prop :=
(fin_dim : ∃ (M : prime_ideal_chain R), ∀ (N : prime_ideal_chain R), N.len ≤ M.len)

/--
If `R` is not the zero ring, then `R` is finite dimensional iff all prime ideal chains of `R` have
length bounded by some `n ∈ ℕ`
-/
lemma finite_dimensional_ring.iff_len_bounded [nontrivial R] : 
  finite_dimensional_ring R ↔ 
  ∃ (n : ℕ), ∀ (N : prime_ideal_chain R), N.len ≤ n :=
{ mp := λ h, ⟨h.fin_dim.some.len, h.fin_dim.some_spec⟩,
  mpr := λ h, 
  { fin_dim := ⟨(@nat.Sup_mem (set.range (prime_ideal_chain.len : prime_ideal_chain R → ℕ))
      ⟨(default : prime_ideal_chain R).len, ⟨_, rfl⟩⟩ ⟨h.some, begin 
        rintros _ ⟨x, rfl⟩,
        exact h.some_spec _,
      end⟩).some, λ N, begin 
        classical,
        generalize_proofs H,
        rw H.some_spec,
        rw nat.Sup_def ⟨h.some, _⟩,
        swap,
        { rintros _ ⟨m, rfl⟩,
          refine h.some_spec _, },
        generalize_proofs H2,
        exact nat.find_spec H2 _ ⟨_, rfl⟩,
      end⟩ } }


/--
The Krull dimension of a ring is the length of maximal chain if the ring is finite dimensional and 
0 otherwise.
Notes on implementation:
alternatively `krull_dim` should take value in `with_top (with_bot ℕ)` where the zero ring then
would have dimension negative infinity (`⊥`) and any infinite dimensional ring will have dimension 
positive infinity (`⊤`).
-/
def krull_dim : ℕ := 
@@dite (finite_dimensional_ring R) (classical.dec _) (λ H, H.fin_dim.some.len) (λ _, 0)

/--
If `R` is finite dimensional, then it has a prime ideal chain with the greatest length.
-/
def maximal_chain [finite_dimensional_ring R] : prime_ideal_chain R :=
finite_dimensional_ring.fin_dim.some

lemma maximal_chain_is_maximal [finite_dimensional_ring R] (M : prime_ideal_chain R) :
  M.len ≤ (maximal_chain R).len :=
finite_dimensional_ring.fin_dim.some_spec M

/--
If `R` is finite dimensional, then its dimension is the length of the longest prime ideal chain.
-/
lemma krull_dim_eq_len [finite_dimensional_ring R] : krull_dim R = (maximal_chain R).len :=
begin 
  dunfold krull_dim,
  split_ifs,
  refl,
end

/--
If `R` is infinite dimensional, then its dimension, according to our convention, is zero.
-/
lemma krull_dim_eq_zero (not_finite : ¬ finite_dimensional_ring R) : krull_dim R = 0 :=
begin 
  dunfold krull_dim,
  split_ifs,
  refl,
end

section

variables {R}

/--
Pulling back a chain of prime ideal chain of `S` along a surjective ring homomorphism `f : R ⟶ S`
to obtain a prime idael chain of `R` by `𝔭ᵢ ↦ f⁻¹ 𝔭ᵢ`.
-/
@[simps] def prime_ideal_chain.comap {S : Type*} [comm_ring S] (N : prime_ideal_chain S)
  (f : R →+* S) (hf : function.surjective f) : prime_ideal_chain R :=
{ len := N.len,
    chain := λ j, (N.chain j).comap f,
    is_chain := λ i j h, begin 
      dsimp,
      rw lt_iff_le_and_ne,
      split,
      { refine ideal.comap_mono _,
        refine le_of_lt (N.is_chain h), },
      { have neq := ne_of_lt (N.is_chain h),
        contrapose! neq,
        ext1 s,
        obtain ⟨r, rfl⟩:= hf s,
        rw [← ideal.mem_comap, neq, ideal.mem_comap], },
    end,
    is_prime := λ j, begin
      haveI := N.is_prime j,
      refine ideal.comap_is_prime _ _,
    end }


/--
If `R` is finite dimensional and `R ⟶ S` is a surjective ring homomorphism, then every prime ideal
chain of `S` has length at most `krull_dim R` 
-/
theorem prime_ideal_chain.length_bounded {S : Type*} [comm_ring S]
  (N : prime_ideal_chain S) [finite_dimensional_ring R]
  (f : R →+* S) (hf : function.surjective f) : 
  N.len ≤ krull_dim R :=
begin
  rw [show N.len = (N.comap f hf).len, from rfl, krull_dim_eq_len],
  apply maximal_chain_is_maximal,
end

end

/--
If `R` is finite dimensional and `R ⟶ S` is a surjective ring homomorphism, then `S` is finite
dimensional as well.
-/
lemma finite_dimensional_of_surj [finite_dimensional_ring R] 
  (S : Type*) [comm_ring S] [nontrivial S]
  (f : R →+* S) (hf : function.surjective f) : finite_dimensional_ring S :=
begin
  rw finite_dimensional_ring.iff_len_bounded,
  exact ⟨krull_dim R, λ N, N.length_bounded f hf ⟩,
end

/--
If `R` is finite dimensional and `R ⟶ S` is a surjective ring homomorphism, 
then `krull_dim S ≤ krull_dim R`.
-/
theorem krull_dim_le_of_surj [finite_dimensional_ring R]
  (S : Type*) [comm_ring S] [nontrivial S]
  (f : R →+* S) (hf : function.surjective f) : krull_dim S ≤ krull_dim R :=
begin
  haveI : finite_dimensional_ring S := finite_dimensional_of_surj R S f hf,
  rw krull_dim_eq_len,
  exact (maximal_chain S).length_bounded f hf,
end

/--
If `R` is finite dimensional and nontrivial and `S` is isomorphic
to `R`, then `krull_dim R = krull_dim S`.
-/
theorem krull_dim_eq_of_findim_nontriv_isom
  [finite_dimensional_ring R] [nontrivial R]
  (S : Type*) [comm_ring S] (e : R ≃+* S) :
  krull_dim R = krull_dim S :=
begin
  haveI : nontrivial S,
    exact function.injective.nontrivial
    (equiv_like.injective e),
  haveI : finite_dimensional_ring S,
    exact finite_dimensional_of_surj R S e
    (equiv_like.surjective e),
  have hRS : krull_dim R ≤ krull_dim S,
    exact krull_dim_le_of_surj S R (ring_equiv.symm e)
    (equiv_like.surjective (ring_equiv.symm e)),
  have hSR : krull_dim S ≤ krull_dim R,
    exact krull_dim_le_of_surj R S e
    (equiv_like.surjective e),
  exact le_antisymm hRS hSR,
end

/--
If `R` is nontrivial and `S` is isomorphic to `R`, then `krull_dim R = krull_dim S`.
-/
theorem krull_dim_eq_of_nontriv_isom [nontrivial R]
  (S : Type*) [comm_ring S] (e : R ≃+* S) :
  krull_dim R = krull_dim S :=
begin
  by_cases hf : finite_dimensional_ring R,
  haveI : finite_dimensional_ring R,
    exact hf,
  exact krull_dim_eq_of_findim_nontriv_isom R S e,
  have hi : ¬finite_dimensional_ring S,
    contrapose hf,
    rw not_not at hf ⊢,
    haveI : finite_dimensional_ring S,
      exact hf,
    exact finite_dimensional_of_surj S R (ring_equiv.symm e)
    (equiv_like.surjective (ring_equiv.symm e)),
  have h1 : krull_dim R = 0,
    exact krull_dim_eq_zero R hf,
  have h2 : krull_dim S = 0,
    exact krull_dim_eq_zero S hi,
  rw h1,
  rw h2,
end

/--
If `R` is trivial, then according to our definition, `R` is not finite dimensional.
-/
lemma not_fin_dim_of_triv [ht : ¬nontrivial R] :
  ¬finite_dimensional_ring R :=
begin
  by_contra hf,
    have hI : ∃ (I : ideal R), I.is_prime,
      use hf.fin_dim.some.chain 0,
      exact hf.fin_dim.some.is_prime 0,
    cases hI with I hI',
    have haz : ∀ (x : R), x = 0,
      intro x,
      by_contra,
      have htR : ¬(∃ (x y : R), x ≠ y),
        rw ←nontrivial_iff,
        exact ht,
      have nhtR : ∃ (x y : R), x ≠ y,
        use x,
        use 0,
      exact htR nhtR,
    have hIeqT : I = ⊤,
      ext x,
      split,
      intro,
      triv,
      rw (haz x),
      intro,
      exact ideal.zero_mem I,
    exact ideal.is_prime.ne_top hI' hIeqT,
end

/--
If `R` and `S` are isomorphic, then `krull_dim R = krull_dim S`.
-/
theorem krull_dim_eq_of_isom (S : Type*) [comm_ring S]
  [e : R ≃+* S] : krull_dim R = krull_dim S :=
begin
  by_cases hnt : nontrivial R,
  haveI : nontrivial R := hnt,
  exact krull_dim_eq_of_nontriv_isom R S e,
  have htS : ¬nontrivial S,
    intro hntS,
    have hntR : nontrivial R,
      rw nontrivial_iff at hntS ⊢,
      cases hntS with x h,
      cases h with y h',
      use ring_equiv.symm e x,
      use ring_equiv.symm e y,
      intro hxeye,
      exact h' ((ring_equiv.injective (ring_equiv.symm e))
      hxeye),
    exact hnt hntR,
  have hnfR : ¬finite_dimensional_ring R,
    exact (@not_fin_dim_of_triv R _ hnt),
  have hnfS : ¬finite_dimensional_ring S,
    exact (@not_fin_dim_of_triv S _ htS),
  have h1 : krull_dim R = 0,
    exact krull_dim_eq_zero R hnfR,
  have h2 : krull_dim S = 0,
    exact krull_dim_eq_zero S hnfS,
  rw h1,
  rw h2,
end

/--
If `R` is finite dimensional, `I` is an ideal of `R`, and `R ⧸ I` is
nontrivial, then `krull_dim (R ⧸ I) ≤ krull_dim R`.
-/
theorem krull_dim_le_of_quot [finite_dimensional_ring R] (I : ideal R) [nontrivial (R ⧸ I)] : 
  krull_dim (R ⧸ I) ≤ krull_dim R :=
begin
  haveI : finite_dimensional_ring (R ⧸ I) := 
    finite_dimensional_of_surj R (R ⧸ I) (ideal.quotient.mk I) ideal.quotient.mk_surjective,
  exact krull_dim_le_of_surj _ _ (ideal.quotient.mk I) ideal.quotient.mk_surjective,
end


section height

variables {R} 

/--
The height of a prime ideal `𝔭` is defined to be `krull_dim R_𝔭`
-/
def ideal.height (p : ideal R) [p.is_prime] : ℕ :=
krull_dim (localization.at_prime p)

example (p : ideal R) [p.is_prime] : ℕ := p.height

end height
