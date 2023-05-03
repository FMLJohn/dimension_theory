import data.fin.basic
import data.fin.tuple.basic
import tactic.linarith

namespace fin

instance has_zero.of_lt (n : ℕ) [fact $ 0 < n] : has_zero (fin n) :=
@@fin.has_zero_of_ne_zero ⟨λ h, ne_of_lt (fact.out _) h.symm⟩

instance has_one.of_le (n : ℕ) [fact $ 3 ≤ n] : has_one (fin n) :=
@@fin.has_one_of_ne_zero ⟨begin 
  unfreezingI { rintro rfl },
  resetI,
  linarith [show 3 ≤ 0, from fact.out _], 
end⟩

lemma one_val_eq_of_le (n : ℕ) [fact $ 2 ≤ n] : (1 : fin n).val = 1 :=
nat.mod_eq_of_lt (by linarith [show 2 ≤ n, from fact.out (2 ≤ n)] : 1 < n)

lemma coe_one_eq_of_le (n : ℕ) [fact $ 2 ≤ n] : ((1 : fin n) : ℕ) = 1 :=
one_val_eq_of_le n

lemma one_pos_of_le (n : ℕ) [fact $ 2 ≤ n] : (0 : fin n) < (1 : fin n) :=
show 0 < _, by { rw [one_val_eq_of_le n], exact nat.zero_lt_one }

lemma two_val_eq_of_le (n : ℕ) [fact $ 3 ≤ n] : (2 : fin n).val = 2 :=
begin 
  haveI : fact (2 ≤ n) := ⟨by linarith [show 3 ≤ n, from fact.out _]⟩,
  rw [show (bit0 1 : fin n) = 2, from rfl, val_eq_coe, fin.coe_bit0, coe_one_eq_of_le],
  refine nat.mod_eq_of_lt (by linarith [show 3 ≤ n, from fact.out _]),
end

lemma coe_two_eq_of_le (n : ℕ) [fact $ 3 ≤ n] : (2 : fin n).val = 2 :=
two_val_eq_of_le n

/--
If `m = n`, then `fin m` and `fin n` are order isomorphic.
-/
@[simps]
def congr (m n : ℕ) (h : m = n) : fin m ≃o fin n :=
{ to_fun := λ j, ⟨j, h ▸ j.2⟩,
  inv_fun := λ j, ⟨j, h.symm ▸ j.2⟩,
  left_inv := λ j, fin.ext rfl,
  right_inv := λ j, fin.ext rfl,
  map_rel_iff' := λ _ _, iff.rfl }

@[elab_as_eliminator] def induction_of_zero_lt
  (n : ℕ) [fact $ 0 < n]
  {C : fin n → Sort*}
  (h0 : C 0)
  (hs : ∀ (i : ℕ) (hn : i < n - 1), C ⟨i, by linarith [fact.out $ 0 < n]⟩ → C ⟨i + 1, by linarith [fact.out $ 0 < n]⟩) :
  Π (i : fin n), C i :=
begin
  haveI : ne_zero n := ⟨ne.symm $ ne_of_lt (fact.out _)⟩,
  rintro ⟨i, hi⟩,
  induction i with i IH,
  { rwa [fin.mk_zero] },
  { refine hs i (by rwa [←nat.pred_eq_sub_one, nat.lt_pred_iff]) (IH _), }
end

def insert_nth_const {n} {α : Type*} (i : fin (n + 1)) (x : α) 
  (p : fin n → α) (j : fin (n + 1)) : α :=
@fin.insert_nth n (λ _, α) i x p j

lemma insert_nth_const_apply_above {n} {α : Type*}  
  {i j : fin (n + 1)} (h : i < j) (x : α)
  (p : fin n → α) :
  i.insert_nth_const x p j = 
  (p $ j.pred $ λ r, by { subst r, norm_num at h }) :=
begin 
  rw [insert_nth_const, insert_nth, succ_above_cases, dif_neg h.ne', dif_neg h.not_lt],
  generalize_proofs h1 h2,
  apply eq_of_heq ((eq_rec_heq _ _).trans _),
  refl,
end

lemma insert_nth_const_apply_below {n} {α : Type*} 
  {i j : fin (n + 1)} (h : j < i) (x : α)
  (p : fin n → α) :
  i.insert_nth_const x p j = 
  (p $ j.cast_lt $ by { change (_ : ℕ) < _ at h, linarith [i.2, j.2, h], }) :=
begin 
  rw [insert_nth_const, insert_nth, succ_above_cases, dif_neg h.ne, dif_pos h],
  generalize_proofs h1 h2,
  apply eq_of_heq ((eq_rec_heq _ _).trans _),
  refl,
end

@[simp] lemma insert_nth_const_apply_same  {n} {α : Type*}  
  (i : fin (n + 1)) (x : α) (p : fin n → α) :
  insert_nth_const i x p i = x :=
by rw [insert_nth_const, insert_nth, succ_above_cases, dif_pos rfl]

end fin
