import order.monotone.basic
import order.with_bot
import data.fin.basic
import tactic.linarith
import algebraic_geometry.prime_spectrum.basic
import ring_theory.ideal.basic

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

end preorder

/--
The ring theoretic Krull dimension is the Krull dimension of prime spectrum ordered by inclusion.
-/
def ring_krull_dim (R : Type*) [comm_ring R] : ℕ±∞ :=
krull_dim (prime_spectrum R)


namespace ring_krull_dim

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
theorem le_of_quot (I R : Type*) [comm_ring R] (I : ideal R) :
  ring_krull_dim (R ⧸ I) ≤ ring_krull_dim R :=
le_of_surj _ _ (ideal.quotient.mk I) ideal.quotient.mk_surjective

/--
If `R` and `S` are isomorphic, then `krull_dim R = krull_dim S`.
-/
theorem eq_of_isom (R S : Type*) [comm_ring R] [comm_ring S] (e : R ≃+* S) :
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
If `I` is a prime ideal of `R`, then we can embed `R` into `localizaiton.at_prime I`.
-/
def localization_embedding (R I : Type*) [comm_ring R] [I : ideal R] [I.is_prime]:
  R → (localization.at_prime I) := λ r, (localization.mk r 1)

end ring_krull_dim