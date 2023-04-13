import data.fin.basic
import tactic.linarith

namespace fin


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

end fin
