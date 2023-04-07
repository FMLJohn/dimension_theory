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

- `f : α → β` is strictly monotonic, then `krull_dim α ≤ krull_dim β` (*) [`strict_chain.map`pushforward];
  - almost finished
- `f : α → β` is strictly comonotonic and surjective, then `krull_dim β ≤ krull_dim α` [`strict_chain.comap`pullback];
- `height` makes sense for any preodered set
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

def strict_comono (f : α → β) : Prop :=
∀ ⦃a b⦄, f a < f b → a < b

end strict_comono

structure strict_chain :=
(len : ℕ)
(func : fin (len + 1) → α)
(strict_mono' : strict_mono func)

namespace strict_chain

instance : has_coe_to_fun (strict_chain α) (λ x, fin (x.len + 1) → α) :=
{ coe := λ x, x.func }

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
  lt_iff_le_not_le := λ a b,
  begin 
    rw [le_def, lt_def, le_def],
    exact lt_iff_le_not_le,
  end }

instance [is_empty α] : is_empty $ strict_chain α :=
{ false := λ p, @is_empty.elim α (infer_instance : is_empty α) (λ _, false) (p 0) }

instance [inhabited α] : inhabited $ strict_chain α :=
{ default := ⟨0, λ _, default, λ _ _ h, (ne_of_lt h $ subsingleton.elim _ _).elim⟩ }

instance [nonempty α] : nonempty $ strict_chain α :=
nonempty.intro ⟨0, λ _, nonempty.some infer_instance, λ _ _ h, (ne_of_lt h $ subsingleton.elim _ _).elim⟩

lemma top_len_unique [order_top (strict_chain α)] (p : strict_chain α) (hp : is_top p) :
  p.len = (⊤ : strict_chain α).len :=
begin 
  have ineq1 : (⊤ : strict_chain α).len ≤ p.len := hp ⊤,
  have ineq2 : p.len ≤ (⊤ : strict_chain α).len := @le_top (strict_chain α) _ _ _,
  refine le_antisymm ineq2 ineq1,
end

lemma top_len_unique' (H1 H2 : order_top (strict_chain α)) : H1.top.len = H2.top.len :=
le_antisymm (H2.le_top H1.top) (H1.le_top H2.top)

variables {α β}
@[simps]
def map (p : strict_chain α) (f : α → β) (hf : strict_mono f) : strict_chain β :=
{ len := p.len,
  func := f.comp p,
  strict_mono' := hf.comp p.strict_mono' }

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

@[reducible] def krull_dim : ℕ±∞ := ⨆ (p : strict_chain α), p.len

variables {α}

@[reducible] def height (a : α) : ℕ±∞ :=
krull_dim (set.Iic a)

variable α

lemma krull_dim_eq_bot_of_is_empty [is_empty α] :
  krull_dim α = ⊥ :=
with_bot.csupr_empty _

lemma krull_dim_eq_top_of_no_top_order [nonempty α] [no_top_order (strict_chain α)] :
  krull_dim α = ⊤ :=
le_antisymm le_top $ le_Sup_iff.mpr $ λ m hm, 
match m, hm with
| ⊥, hm := false.elim begin 
  haveI : inhabited α := classical.inhabited_of_nonempty infer_instance,
  exact not_le_of_lt (with_bot.bot_lt_coe _ : ⊥ < (0 : ℕ±∞)) 
    (hm ⟨⟨0, λ _, default, λ _ _ h, ((ne_of_lt h) $ subsingleton.elim _ _).elim⟩, rfl⟩),
end
| some m, hm := match m, hm with
| ⊤, hm := le_refl _
| some m, hm := begin 
  rw mem_upper_bounds at hm,
  obtain ⟨p, hp⟩ := strict_chain.exists_len_gt_of_infinite_dim α m,
  specialize hm p.len ⟨p, rfl⟩,
  refine (not_lt_of_le hm _).elim,
  erw [with_bot.some_eq_coe, with_bot.coe_lt_coe, with_top.some_eq_coe, with_top.coe_lt_coe],
  assumption,
end
end
end

lemma krull_dim_eq_len_of_order_top [order_top (strict_chain α)] :
  krull_dim α = (⊤ : strict_chain α).len :=
le_antisymm (supr_le $ λ i, with_bot.coe_le_coe.mpr $ with_top.coe_le_coe.mpr $ 
    order_top.le_top i) (le_Sup ⟨_, rfl⟩)

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

end preorder

def ring_krull_dim (R : Type*) [comm_ring R] : ℕ±∞ :=
krull_dim (prime_spectrum R)

section partial_order

variables [partial_order α]

end partial_order
