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
- `f : α → β` is strictly comonotonic and surjective, then `krull_dim β ≤ krull_dim α` [`strict_chain.comap`pullback];
- (*) imply `R ⟶ S` surjective homomorphism, then `dim S ≤ dim R`;
- `height` makes sense for any preodered set

-------
Theory needs to take place in `Top, Ring, Module` Concerte
- need to show `height 𝔭 = krull_dim (localizaiton.at_prime 𝔭)`
- `coheight` probably doesn't make sense in general preorder
- `height 𝔭 + coheight 𝔭 ≤ krull_dim R`

-/

noncomputable theory

variables (α β : Type*)

section preorder

variables [preorder α] [preorder β]

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

lemma exists_len_gt_of_infinite_dim [no_top_order (strict_chain α)] [H : nonempty α] (n : ℕ) : 
  ∃ (p : strict_chain α), n < p.len :=
begin
  let a : α := H.some,
  set default_chain : strict_chain α := ⟨0, λ p, a, begin 
    intros a b h,
    exfalso,
    exact ne_of_lt h (subsingleton.elim _ _),
  end⟩ with d_eq, 
  induction n with n ih,
  { rcases no_top_order.exists_not_le default_chain with ⟨p, hp⟩,
    simp only [le_def, not_le, d_eq] at hp,
    exact ⟨p, hp⟩, },
  { rcases ih with ⟨p, hp⟩,
    rcases no_top_order.exists_not_le p with ⟨q, hq⟩,
    use q,
    rw [le_def, not_le] at hq,
    rw nat.succ_eq_add_one,
    linarith, },
end

end strict_chain

def krull_dim [decidable (is_empty α)] : with_bot (with_top ℕ) :=
psum.cases_on (top_order_or_no_top_order (strict_chain α)) 
(λ H, H.top.len) 
(λ H, if is_empty α then ⊥ else ⊤)

variables {α}

def height (a : α) [decidable (is_empty (set.Iic a))] : with_bot (with_top ℕ) :=
krull_dim (set.Iic a)

instance t1 [H : is_empty α] : decidable (is_empty α) :=
is_true H

lemma krull_dim_eq_bot_of_is_empty [is_empty α] :
  krull_dim α = ⊥ :=
begin 
  rw [krull_dim, show top_order_or_no_top_order (strict_chain α) = psum.inr _, from _],
  { dsimp only, rw if_pos, apply_instance },
  { fconstructor, intros a, refine @is_empty.elim (strict_chain α) infer_instance _ a, },
  { dunfold top_order_or_no_top_order, rw dif_pos, },
end

instance t2 [order_top (strict_chain α)] : decidable (is_empty α) :=
is_false begin 
  rw not_is_empty_iff,
  refine nonempty.intro ((⊤ : strict_chain α) 0),
end

lemma krull_dim_eq_len_of_order_top [order_top (strict_chain α)] :
  krull_dim α = (⊤ : strict_chain α).len :=
begin
  rw krull_dim,
  induction top_order_or_no_top_order (strict_chain α) with H H,
  { dsimp, congr' 1, apply strict_chain.top_len_unique', },
  { exfalso, 
    obtain ⟨p, hp⟩ := H.exists_not_le ⊤,
    refine hp _,
    apply le_top, },
end

lemma krull_dim_eq_len_of_is_top [order_top (strict_chain α)] (p : strict_chain α) (hp : is_top p) :
  krull_dim α = p.len :=
by rw [krull_dim_eq_len_of_order_top, (strict_chain.top_len_unique _ p hp).symm]

lemma krull_dim_le_of_inj [decidable $ is_empty α] [decidable $ is_empty β] 
  (f : α → β) (f : strict_mono f) : krull_dim α ≤ krull_dim β :=
sorry

#check @function.is_empty
end preorder

instance t3 (R : Type*) [H : decidable $ nontrivial R] [comm_ring R] : 
  decidable (is_empty $ prime_spectrum R) :=
match H with
| is_true h := is_false begin 
  rw not_is_empty_iff,
  resetI,
  exact ⟨⟨(ideal.exists_maximal R).some, (ideal.exists_maximal R).some_spec.is_prime⟩⟩,
end
| is_false h := is_true begin 
  rw not_nontrivial_iff_subsingleton at h,
  by_contra rid,
  rw not_is_empty_iff at rid,
  cases rid,
  refine rid.2.ne_top _,
  ext,
  simp only [submodule.mem_top, iff_true],
  convert ideal.zero_mem _,
  resetI,
  refine subsingleton.elim _ _,
end
end

def ring_krull_dim (R : Type*) [decidable $ nontrivial R] [comm_ring R] : with_bot (with_top ℕ) :=
krull_dim (prime_spectrum R)

section partial_order

variables [partial_order α]

end partial_order