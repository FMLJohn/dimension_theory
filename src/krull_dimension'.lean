import order.monotone.basic
import order.with_bot
import data.fin.basic
import algebraic_geometry.prime_spectrum.basic
import ring_theory.ideal.basic

import .fin_lemmas

/--
`α, β` preodered sets
--- 
General theory
- [x] `f : α → β` is strictly monotonic, then `krull_dim α ≤ krull_dim β` by pushing out (using 
  `strict_chain.map`).
- [x] `f : α → β` is strictly comonotonic and surjective, then `krull_dim β ≤ krull_dim α` by 
  pulling back (using `strict_chain.comap`).
- [x] `height` makes sense for any preodered set.
- [x] `krull_dim` is equal to supremum of height.
- `krull_nat_dim` : works for "finite_dim" `[order_top (chain α)]`, `α → ℕ`.
- `krull_nat_dim = krull_dim` when finite dimensional
-------
Theory needs to take place in `Top, Ring, Module` Concerte
- (*) imply `R ⟶ S` surjective homomorphism, then `dim S ≤ dim R`;
- need to show `height 𝔭 = krull_dim (localizaiton.at_prime 𝔭)`
- `coheight` probably doesn't make sense in general preorder
- `height 𝔭 + coheight 𝔭 ≤ krull_dim R`
Important but far away
- If `R` is noetherian and local, then `R` is finite dimensional.
-/

noncomputable theory

local notation `ℕ±∞` := with_bot (with_top ℕ)

variables (α β : Type*)

section preorder

variables [preorder α] [preorder β]

section strict_comono

variables {α β}

/--
A function `f : α → β` is said to be strictly comonotonic (dual to strictly monotonic) 
if and only if `a < b` is implied by `f a < f b` for all `a, b : β`.
-/
def strict_comono (f : α → β) : Prop :=
∀ ⦃a b⦄, f a < f b → a < b

end strict_comono

/--
For a preordered set `(α, <)`, a strict chain of `α` of length `n` is a strictly monotonic function
`fin (n + 1) → α`, i.e. `a₀ < a₁ < ... < aₙ` with `a_i : α`.
-/
structure strict_chain :=
(len : ℕ)
(func : fin (len + 1) → α)
(strict_mono' : strict_mono func)

namespace strict_chain

instance : has_coe_to_fun (strict_chain α) (λ x, fin (x.len + 1) → α) :=
{ coe := λ x, x.func }

/--
The induced ordering on `strict_chain α` is by comparing length of strict chains.
-/
instance : has_le (strict_chain α) :=
{ le := λ p q, p.len ≤ q.len }

lemma le_def (p q : strict_chain α) : p ≤ q ↔ p.len ≤ q.len := iff.rfl

instance : has_lt (strict_chain α) :=
{ lt := λ p q, p.len < q.len }

lemma lt_def (p q : strict_chain α) : p < q ↔ p.len < q.len := iff.rfl

instance : preorder (strict_chain α) :=
{ le := (≤),
  lt := (<),
  le_refl := λ a, show a.len ≤ a.len, from le_refl _,
  le_trans := λ a b c (h : a.len ≤ b.len) (h' : b.len ≤ c.len), show a.len ≤ c.len, from h.trans h',
  lt_iff_le_not_le := λ a b, @lt_iff_le_not_le ℕ _ a.len b.len }

instance [is_empty α] : is_empty $ strict_chain α :=
{ false := λ p, @is_empty.elim α (infer_instance : is_empty α) (λ _, false) (p 0) }

instance [inhabited α] : inhabited $ strict_chain α :=
{ default := ⟨0, λ _, default, λ _ _ h, (ne_of_lt h $ subsingleton.elim _ _).elim⟩ }

instance [nonempty α] : nonempty $ strict_chain α :=
nonempty.intro ⟨0, λ _, nonempty.some infer_instance, λ _ _ h, (ne_of_lt h $ subsingleton.elim _ _).elim⟩

lemma top_len_unique [order_top (strict_chain α)] (p : strict_chain α) (hp : is_top p) :
  p.len = (⊤ : strict_chain α).len :=
le_antisymm (@le_top (strict_chain α) _ _ _) (hp ⊤)

lemma top_len_unique' (H1 H2 : order_top (strict_chain α)) : H1.top.len = H2.top.len :=
le_antisymm (H2.le_top H1.top) (H1.le_top H2.top)

variables {α β}

@[simps]
def reverse (i : strict_chain α) : strict_chain αᵒᵈ :=
{ len := i.len,
  func := i ∘ (has_sub.sub ⟨i.len, lt_add_one _⟩),
  strict_mono' := λ j k h, i.strict_mono' begin
    rw [fin.lt_def, fin.sub_def, fin.sub_def],
    dsimp only,
    zify,
    rw [int.coe_nat_sub (by linarith [j.2] : j.1 ≤ i.len + 1), 
      int.coe_nat_sub (by linarith [k.2] : k.1 ≤ i.len + 1)],
    rw [int.coe_nat_add, int.coe_nat_one, add_sub_left_comm, int.add_mod_self_left,
      add_sub_left_comm, int.add_mod_self_left, int.mod_eq_of_lt, int.mod_eq_of_lt],
    { refine int.sub_lt_sub_left _ _, exact_mod_cast h, },
    { refine sub_nonneg_of_le _, linarith [j.2], },
    { rw [sub_eq_add_neg], 
      refine int.add_lt_add_left _ _,
      rw neg_lt,
      refine lt_of_lt_of_le neg_one_lt_zero _,
      norm_num, },
    { refine sub_nonneg_of_le _, linarith [k.2], },
    { rw [sub_eq_add_neg], 
      refine int.add_lt_add_left _ _,
      rw neg_lt,
      refine lt_of_lt_of_le neg_one_lt_zero _,
      norm_num, },
  end }

@[simps]
def cons (p : strict_chain α) (a : α) (h : a < p 0) : strict_chain α :=
{ len := p.len + 1,
  func := fin.cons a p,
  strict_mono' := λ i,
  begin 
    refine fin.cases _ _ i,
    { intros j, 
      refine fin.cases _ _ j,
      { intros r, rw lt_self_iff_false at r, cases r },
      { intros k hk, 
        rw [fin.cons_zero, fin.cons_succ], 
        exact lt_of_lt_of_le h (p.strict_mono'.monotone $ by norm_num), }, },
    { intros i' j,
      refine fin.cases _ _ j,
      { intros r, cases not_lt_of_lt r (fin.succ_pos i'), },
      { intros k hk, 
        rw [fin.cons_succ, fin.cons_succ], 
        refine p.strict_mono' _,
        rwa fin.succ_lt_succ_iff at hk, }, },
  end }

lemma cons_zero (p : strict_chain α) (a : α) (h : a < p 0) : p.cons a h 0 = a :=
by simp only [cons_func, fin.cons_zero]

@[simps]
def snoc (p : strict_chain α) (a : α) (h : p ⟨p.len, lt_add_one _⟩ < a) : strict_chain α :=
{ len := p.len + 1,
  func := fin.snoc p a,
  strict_mono' := λ i j H, begin
    rw [fin.snoc, fin.snoc],
    by_cases h1 : j.1 < p.len + 1,
    { rw [dif_pos ((show i.1 < j.1, from H).trans h1), dif_pos h1, cast_eq, cast_eq],
      exact p.strict_mono' H },
    { rw [dif_neg h1, cast_eq],
      split_ifs with h2,
      { rw [cast_eq], 
        refine lt_of_le_of_lt (p.strict_mono'.monotone _) h,
        change i.1 ≤ p.len,
        linarith },
      { change i.1 < j.1 at H,
        have hi := i.2,
        have hj := j.2,
        push_neg at h2 h1,
        refine (ne_of_lt H _).elim,
        rw [show i.1 = p.len + 1, from _, show j.1 = p.len + 1, from _];
        linarith, }, },
  end }

lemma snoc_last (p : strict_chain α) (a : α) (h : p ⟨p.len, lt_add_one _⟩ < a) :
  p.snoc a h ⟨p.len + 1, lt_add_one _⟩ = a := 
by simp only [fin.snoc, lt_self_iff_false, not_false_iff, snoc_func, cast_eq, dif_neg]

/--
For two pre-ordered sets `α, β`, if `f : α → β` is strictly monotonic, then a strict chain of `α` 
can be pushed out to a strict chain of `β` by 
`a₀ < a₁ < ... < aₙ ↦ f a₀ < f a₁ < ... < f aₙ`
-/
@[simps]
def map (p : strict_chain α) (f : α → β) (hf : strict_mono f) : strict_chain β :=
{ len := p.len,
  func := f.comp p,
  strict_mono' := hf.comp p.strict_mono' }

/--
For two pre-ordered sets `α, β`, if `f : α → β` is surjective and strictly monotonic, then a strict 
chain of `β` can be pulled back to a strict chain of `α` by 
`b₀ < b₁ < ... < bₙ ↦ f⁻¹ b₀ < f⁻¹ b₁ < ... < f⁻¹ bₙ` where `f⁻¹ bᵢ` is an arbitrary element in the
preimage of `f⁻¹ {bᵢ}`.
-/
@[simps]
def comap (p : strict_chain β) (f : α → β) (hf1 : strict_comono f) (hf2 : function.surjective f) :
  strict_chain α :=
{ len := p.len,
  func := λ i, (hf2 (p i)).some,
  strict_mono' := λ i j h, hf1 (by simpa only [(hf2 _).some_spec] using p.strict_mono' h) }

variable (α)

lemma exists_len_gt_of_infinite_dim [no_top_order (strict_chain α)] [nonempty α] (n : ℕ) : 
  ∃ (p : strict_chain α), n < p.len :=
begin
  haveI : inhabited α := classical.inhabited_of_nonempty infer_instance,
  induction n with n ih,
  { obtain ⟨p, hp⟩ := no_top_order.exists_not_le (default : strict_chain α),
    refine ⟨p, lt_of_not_le hp⟩, },
  { rcases ih with ⟨p, hp⟩,
    rcases no_top_order.exists_not_le p with ⟨q, hq⟩,
    dsimp [le_def, not_le, nat.succ_eq_add_one] at *,
    exact ⟨q, by linarith⟩, },
end

end strict_chain

/--
Krull dimension of a pre-ordered set `α` is the supremum of lengths of all strict chains of `α`.
-/
@[reducible] def krull_dim : ℕ±∞ := ⨆ (p : strict_chain α), p.len

variables {α}

/--
Height of an element `a` of a pre-ordered set `α` is the Krull dimension of the subset `(-∞, a]`
-/
@[reducible] def height (a : α) : ℕ±∞ := krull_dim (set.Iic a)

/--
Coheight of an element `a` of a pre-ordered set `α` is the Krull dimension of the subset `[a, +∞)`
-/
@[reducible] def coheight (a : α) : ℕ±∞ := krull_dim (set.Ici a)

variable (α)

lemma krull_dim_eq_bot_of_is_empty [is_empty α] : krull_dim α = ⊥ :=
with_bot.csupr_empty _

lemma krull_dim_eq_top_of_no_top_order [nonempty α] [no_top_order (strict_chain α)] : 
  krull_dim α = ⊤ :=
le_antisymm le_top $ le_Sup_iff.mpr $ λ m hm, match m, hm with
| ⊥, hm := false.elim begin 
  haveI : inhabited α := classical.inhabited_of_nonempty infer_instance,
  exact not_le_of_lt (with_bot.bot_lt_coe _ : ⊥ < (0 : ℕ±∞)) 
    (hm ⟨⟨0, λ _, default, λ _ _ h, ((ne_of_lt h) $ subsingleton.elim _ _).elim⟩, rfl⟩),
end
| some ⊤, hm := le_refl _ 
| some (some m), hm := begin 
  rw mem_upper_bounds at hm,
  obtain ⟨p, hp⟩ := strict_chain.exists_len_gt_of_infinite_dim α m,
  specialize hm p.len ⟨p, rfl⟩,
  refine (not_lt_of_le hm _).elim,
  erw [with_bot.some_eq_coe, with_bot.coe_lt_coe, with_top.some_eq_coe, with_top.coe_lt_coe],
  assumption,
end
end

lemma krull_dim_eq_len_of_order_top [order_top (strict_chain α)] :
  krull_dim α = (⊤ : strict_chain α).len :=
le_antisymm (supr_le $ λ i, with_bot.coe_le_coe.mpr $ with_top.coe_le_coe.mpr $ 
    order_top.le_top i) (le_Sup ⟨_, rfl⟩)

lemma krull_dim_eq_len_of_order_top' [order_top (strict_chain α)] 
  (q : strict_chain α) (h : is_top q) :
  krull_dim α = q.len :=
(krull_dim_eq_len_of_order_top α).trans $ strict_chain.top_len_unique α _ h ▸ rfl

variables {α β}

lemma krull_dim_eq_len_of_is_top [order_top (strict_chain α)] (p : strict_chain α) (hp : is_top p) :
  krull_dim α = p.len :=
by rw [krull_dim_eq_len_of_order_top, (strict_chain.top_len_unique _ p hp).symm]

lemma no_top_order_of_strict_mono (f : α → β) (hf : strict_mono f) [no_top_order (strict_chain α)]
  [nonempty α]: (no_top_order (strict_chain β)) :=
{ exists_not_le := λ smb, let ⟨p, hp⟩ := (strict_chain.exists_len_gt_of_infinite_dim α smb.len) in 
    ⟨p.map f hf, not_le_of_lt hp⟩ }

lemma krull_dim_le_of_strict_mono (f : α → β) (hf : strict_mono f) : krull_dim α ≤ krull_dim β :=
supr_le $ λ p, le_Sup ⟨p.map _ hf, rfl⟩

lemma height_mono {a b : α} (h : a ≤ b) : height a ≤ height b :=
krull_dim_le_of_strict_mono (λ x, ⟨x, le_trans x.2 h⟩) $ λ _ _ h, h

lemma coheight_antitone {a b : α} (h : a ≤ b) : coheight b ≤ coheight a :=
supr_le $ λ p, le_Sup ⟨⟨p.len, (λ (x : set.Ici b), ⟨x, le_trans h x.2⟩) ∘ p, strict_mono.comp 
  (λ i j h, h) p.strict_mono'⟩, rfl⟩

lemma krull_dim_le_of_strict_comono_and_surj 
  (f : α → β) (hf : strict_comono f) (hf' : function.surjective f) : krull_dim β ≤ krull_dim α :=
supr_le $ λ p, le_Sup ⟨p.comap _ hf hf', rfl⟩

lemma krull_dim_eq_of_order_iso (f : α ≃o β) : krull_dim α = krull_dim β :=
le_antisymm (krull_dim_le_of_strict_mono f f.strict_mono) (krull_dim_le_of_strict_comono_and_surj f 
  (λ _ _ h, by convert f.symm.strict_mono h; rw f.symm_apply_apply) f.surjective)

variable (α)

lemma krull_dim_eq_supr_height : krull_dim α = ⨆ (a : α), height a :=
le_antisymm (supr_le $ λ i, le_supr_of_le (i ⟨i.len, lt_add_one _⟩) $ le_Sup 
  ⟨⟨_, λ m, ⟨i m, i.strict_mono'.monotone begin 
    rw [show m = ⟨m.1, m.2⟩, by cases m; refl, fin.mk_le_mk],
    linarith [m.2],
  end⟩, i.strict_mono'⟩, rfl⟩) $ 
supr_le $ λ a, krull_dim_le_of_strict_mono subtype.val $ λ _ _ h, h

lemma krull_dim_le_order_dual : krull_dim α ≤ krull_dim αᵒᵈ :=
supr_le $ λ i, le_Sup $ ⟨i.reverse, rfl⟩

lemma krull_dim_order_dual_le : krull_dim αᵒᵈ ≤ krull_dim α :=
(krull_dim_le_order_dual _).trans $ krull_dim_le_of_strict_mono 
  (order_dual.of_dual ∘ order_dual.of_dual) $ λ _ _ h, h 

lemma krull_dim_eq_order_dual : krull_dim α = krull_dim αᵒᵈ :=
le_antisymm (krull_dim_le_order_dual _) $ krull_dim_order_dual_le _

end preorder

section partial_order

section height_and_coheight

variables [partial_order α]

lemma height_eq (a : α) : 
  height a = ⨆ (p : strict_chain α) (hp : p ⟨p.len, lt_add_one _⟩ = a), p.len := 
le_antisymm (supr_le $ λ p, le_supr_iff.mpr $ λ m h, begin 
  by_cases hp : p ⟨p.len, lt_add_one _⟩ = ⟨a, le_refl _⟩,
  { specialize h ⟨p.len, λ i, p i, λ _ _ h, p.strict_mono' h⟩,
    rwa [supr_pos] at h,
    rwa subtype.ext_iff at hp, },
  { have hp' : p ⟨p.len, lt_add_one _⟩ < ⟨a, le_refl _⟩,
    { exact lt_of_le_of_ne ((p _).2) hp, },
    let q := p.snoc ⟨a, le_refl _⟩ hp',
    specialize h ⟨q.len, λ i, q i, λ _ _ h, q.strict_mono' h⟩,
    rw [supr_pos] at h,
    work_on_goal 2 { exact subtype.ext_iff_val.mp (p.snoc_last ⟨a, le_refl _⟩ hp'), },
    refine le_trans _ h,
    dsimp,
    erw [with_bot.coe_le_coe],
    norm_cast,
    linarith, },
end) $ supr_le $ λ p, supr_le $ λ hp, le_Sup ⟨⟨_, λ i, ⟨p i, hp ▸ p.strict_mono'.monotone begin 
  change i.1 ≤ p.len,
  linarith [i.2]
end⟩, λ _ _ h, p.strict_mono' h⟩, rfl⟩

lemma coheight_eq (a : α) :
  coheight a = ⨆ (p : strict_chain α) (hp : p 0 = a), p.len :=
le_antisymm (supr_le $ λ p, le_supr_iff.mpr $ λ m h, begin 
  by_cases hp : p 0 = ⟨a, le_refl _⟩,
  { specialize h ⟨p.len, λ i, p i, λ _ _ h, p.strict_mono' h⟩,
    rwa [supr_pos] at h,
    rwa subtype.ext_iff at hp, },
  { have hp' : (⟨a, le_refl _⟩ : set.Ici a) < p 0,
    { exact lt_of_le_of_ne (p _).2 (ne.symm hp), },
    let q := p.cons ⟨a, le_refl _⟩ hp',
    specialize h ⟨q.len, λ i, q i, λ _ _ h, q.strict_mono' h⟩,
    rw [supr_pos] at h,
    work_on_goal 2 { exact subtype.ext_iff_val.mp (p.cons_zero ⟨a, le_refl _⟩ hp'), },
    refine le_trans _ h,
    dsimp,
    erw [with_bot.coe_le_coe],
    norm_cast,
    linarith },
end) $ supr_le $ λ p, supr_le $ λ hp, le_Sup ⟨⟨_, λ i, ⟨p i, hp ▸ p.strict_mono'.monotone begin 
  change 0 ≤ i.1,
  norm_num,
end⟩, λ _ _ h, p.strict_mono' h⟩, rfl⟩

end height_and_coheight

end partial_order

/--
Krull dimension of a topological space is the supremum of length of chains of closed irreducible 
sets.
-/
def topological_krull_dim (T : Type*) [topological_space T] : ℕ±∞ :=
krull_dim { s : set T | is_closed s ∧ is_irreducible s }


/--
The ring theoretic Krull dimension is the Krull dimension of prime spectrum ordered by inclusion.
-/
def ring_krull_dim (R : Type*) [comm_ring R] : ℕ±∞ :=
krull_dim (prime_spectrum R)


namespace ring_krull_dim

lemma eq_topological_krull_dim (R : Type*) [comm_ring R] :
  ring_krull_dim R = topological_krull_dim (prime_spectrum R) :=
eq.symm $ (krull_dim_eq_order_dual _).trans $ krull_dim_eq_of_order_iso $ order_iso.symm 
{ to_fun := order_dual.to_dual ∘ λ p, ⟨prime_spectrum.zero_locus p.as_ideal, 
    prime_spectrum.is_closed_zero_locus p.as_ideal, 
    (prime_spectrum.is_irreducible_zero_locus_iff _).mpr $ 
      by simpa only [p.is_prime.radical] using p.is_prime⟩,
  inv_fun := (λ s, ⟨prime_spectrum.vanishing_ideal s.1, 
    prime_spectrum.is_irreducible_iff_vanishing_ideal_is_prime.mp s.2.2⟩ : 
    {s : set (prime_spectrum R) | is_closed s ∧ is_irreducible s} → prime_spectrum R) ∘ 
    order_dual.of_dual,
  left_inv := λ p, begin 
    ext1,
    dsimp,
    rw [prime_spectrum.vanishing_ideal_zero_locus_eq_radical, p.is_prime.radical],
  end,
  right_inv := λ s, begin 
    ext1,
    dsimp only [order_dual.to_dual, order_dual.of_dual, equiv.coe_refl, id, subtype.coe_mk, 
      function.comp_apply],
    rw [prime_spectrum.zero_locus_vanishing_ideal_eq_closure],
    exact s.2.1.closure_eq,
  end,
  map_rel_iff' := begin 
    intros p q, 
    simp only [equiv.coe_fn_mk, order_dual.to_dual_le_to_dual, subtype.mk_le_mk, set.le_eq_subset],
    rw [prime_spectrum.zero_locus_subset_zero_locus_iff, q.is_prime.radical],
    refl,
  end }

/--
If `R ⟶ S` is a surjective ring homomorphism, then `ring_krull_dim S ≤ ring_krull_dim R`.
-/
theorem le_of_surj (R S : Type*) [comm_ring R] [comm_ring S] (f : R →+* S)
  (hf : function.surjective f) : ring_krull_dim S ≤ ring_krull_dim R :=
krull_dim_le_of_strict_mono (prime_spectrum.comap f)
  (monotone.strict_mono_of_injective (λ _ _ h, ideal.comap_mono h) 
    (prime_spectrum.comap_injective_of_surjective f hf))

/--
If `I` is an ideal of `R`, then `ring_krull_dim (R ⧸ I) ≤ ring_krull_dim R`.
-/
theorem le_of_quot (R : Type*) [comm_ring R] (I : prime_spectrum R) :
  ring_krull_dim (R ⧸ I.as_ideal) ≤ ring_krull_dim R :=
le_of_surj _ _ (ideal.quotient.mk I.as_ideal) ideal.quotient.mk_surjective

/--
If `R` and `S` are isomorphic, then `krull_dim R = krull_dim S`.
-/
theorem eq_of_ring_equiv (R S : Type*) [comm_ring R] [comm_ring S] (e : R ≃+* S) :
  ring_krull_dim R = ring_krull_dim S :=
le_antisymm (le_of_surj S R (ring_equiv.symm e)
    (equiv_like.surjective (ring_equiv.symm e)))
      (le_of_surj R S e (equiv_like.surjective e))

instance (F : Type*) [field F] : unique (prime_spectrum F) :=
{ default := ⟨⊥, ideal.bot_prime⟩,
  uniq := λ p, prime_spectrum.ext _ _ $ ideal.ext $ λ x, begin
    rw [submodule.mem_bot],
    refine ⟨λ h, _, λ h, h.symm ▸ submodule.zero_mem _⟩,
    rwa [p.as_ideal.eq_bot_of_prime, submodule.mem_bot] at h,
  end }

instance (F : Type*) [field F] : order_top (strict_chain (prime_spectrum F)) :=
{ top := default,
  le_top := λ ⟨l, f, h⟩, show l ≤ 0, from decidable.by_contradiction $ λ rid, 
    ne_of_gt (@h 0 1 begin 
      simpa only [show (0 : fin (l + 1)) = ⟨0, _⟩, from rfl, 
        show (1 : fin (l + 1)) = ⟨1, lt_add_of_pos_left _ (not_le.mp rid)⟩, begin 
          rw [fin.eq_iff_veq, fin.one_val, fin.val_eq_coe, fin.coe_mk, ← nat.succ_pred_eq_of_pos 
            (not_le.mp rid), nat.one_mod],
        end] using nat.zero_lt_one,
    end) (subsingleton.elim _ _) }

lemma eq_zero_of_field (F : Type*) [field F] : ring_krull_dim F = 0 :=
krull_dim_eq_len_of_order_top (prime_spectrum F)

/--
Any PID that is not a field is finite dimensional with dimension 1
-/
@[simps]
def PID_finite_dimensional (R : Type*) [comm_ring R] [is_principal_ideal_ring R] [is_domain R] 
  (hR : ¬ is_field R) :
  order_top (strict_chain (prime_spectrum R)) :=
{ top := 
  { len := 1,
    func := (fin_two_arrow_equiv $ prime_spectrum R).symm ⟨⟨⊥, ideal.bot_prime⟩, 
      ⟨(ideal.exists_maximal R).some, (ideal.exists_maximal R).some_spec.is_prime⟩⟩,
    strict_mono' := λ i j h, 
    begin 
      fin_cases i; fin_cases j;
      try { refine (ne_of_lt h rfl).elim <|> refine (not_lt_of_lt h fin.zero_lt_one).elim },
      simpa only [fin_two_arrow_equiv_symm_apply, matrix.cons_val_zero, matrix.cons_val_one, 
        matrix.head_cons] using ideal.bot_lt_of_maximal _ hR,
      exact (ideal.exists_maximal R).some_spec,
    end },
  le_top := λ ⟨l, f, m⟩, show l ≤ 1, from decidable.by_contradiction $ λ rid, begin 
    rw not_le at rid,
    haveI : fact (2 ≤ l + 1) := ⟨by linarith⟩,
    haveI : fact (3 ≤ l + 1) := ⟨by linarith⟩,
    
    let a := submodule.is_principal.generator (f 1).as_ideal,
    let b := submodule.is_principal.generator (f 2).as_ideal,
    have lt1 : ideal.span {a} < ideal.span {b},
    { rw [ideal.span_singleton_generator, ideal.span_singleton_generator],
      refine m (_ : fin.val _ < fin.val _),
      rw [fin.one_val_eq_of_le, fin.two_val_eq_of_le],
      exact one_lt_two, },
    rw ideal.span_singleton_lt_span_singleton at lt1,
    rcases lt1 with ⟨h, ⟨r, hr1, hr2⟩⟩,
    have ha : prime a := submodule.is_principal.prime_generator_of_is_prime (f 1).as_ideal _,
    have hb : prime b := submodule.is_principal.prime_generator_of_is_prime (f 2).as_ideal _,
    { obtain ⟨x, hx⟩ := (hb.dvd_prime_iff_associated ha).mp ⟨r, hr2⟩,
      rw ←hx at hr2,
      rw ← mul_left_cancel₀ h hr2 at hr1, 
      refine (hr1 x.is_unit).elim },
    { intros h,
      suffices : (0 : fin (l + 1)) < 2,
      { have : (f 0).as_ideal < (f 2).as_ideal := m this,
        rw h at this,
        refine (not_le_of_lt this bot_le).elim },
      change (0 : fin _).1 < (2 : fin _).1,
      rw [fin.val_zero, fin.two_val_eq_of_le],
      exact zero_lt_two, },
    { intros h,
      suffices : (0 : fin (l + 1)) < 1,
      { have : (f 0).as_ideal < (f 1).as_ideal := m this,
        rw h at this,
        refine (not_le_of_lt this bot_le).elim },
      change (0 : fin _).1 < (1 : fin _).1,
      rw [fin.val_zero, fin.one_val_eq_of_le],
      exact zero_lt_one, },
  end }

lemma PID_eq_one_of_not_field (R : Type*) [comm_ring R] [is_principal_ideal_ring R] [is_domain R] 
  (hR : ¬ is_field R) :
  ring_krull_dim R = 1 :=
begin 
  rw [ring_krull_dim, @@krull_dim_eq_len_of_order_top _ _ (PID_finite_dimensional _ hR)],
  refl,
end

/--
https://stacks.math.columbia.edu/tag/00KG
-/
lemma eq_sup_height_maximal_ideals (R : Type*) [comm_ring R] :
  ring_krull_dim R = ⨆ (p : prime_spectrum R) (hp : p.as_ideal.is_maximal), height p :=
(krull_dim_eq_supr_height _).trans $ le_antisymm (supr_le $ λ p, begin
  let q : prime_spectrum R := ⟨(p.as_ideal.exists_le_maximal p.is_prime.1).some, 
    (p.as_ideal.exists_le_maximal _).some_spec.1.is_prime⟩,
  refine le_trans _ (le_Sup ⟨q, supr_pos ((p.as_ideal.exists_le_maximal _).some_spec.1)⟩),
  exact height_mono (p.as_ideal.exists_le_maximal _).some_spec.2,
end) begin 
  rw [show (⨆ (a : prime_spectrum R), height a) = ⨆ (a : prime_spectrum R) (h : true), height a, 
    by simp only [csupr_pos]],
  exact supr_le_supr_of_subset (λ x _, ⟨⟩),
end

/--
Suppose `I` is a prime ideal of `R`, then there is a canonical map from
`prime_spectrum (localization.at_prime I.as_ideal)` to `set.Iic I`.
-/
def localization_prime_spectrum_comap (R : Type*) [comm_ring R] (I : prime_spectrum R) :
  prime_spectrum (localization.at_prime I.as_ideal) → (set.Iic I) :=
  λ J, ⟨⟨J.as_ideal.comap (algebra_map R (localization.at_prime I.as_ideal)), ideal.is_prime.comap _⟩,
  λ z hz, @@decidable.by_contradiction (classical.dec _) $ λ hnz, J.is_prime.ne_top $ eq_top_iff.mpr $
    false.elim $ J.is_prime.1 $ (ideal.eq_top_iff_one _).mpr begin
      rw [show (1 : localization.at_prime I.as_ideal) = localization.mk z 1 * localization.mk 1
        ⟨z, hnz⟩, from _],
      refine ideal.mul_mem_right _ _ hz,
      rw [localization.mk_mul, mul_one, one_mul, localization.mk_eq_mk', is_localization.eq_mk'_iff_mul_eq,
        one_mul, subtype.coe_mk],
    end⟩

end ring_krull_dim
