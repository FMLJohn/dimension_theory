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

lemma two_val_eq_of_le (n : ℕ) [fact $ 3 ≤ n] : (2 : fin n).val = 2 :=
begin 
  haveI : fact (2 ≤ n) := ⟨by linarith [show 3 ≤ n, from fact.out _]⟩,
  rw [show (bit0 1 : fin n) = 2, from rfl, val_eq_coe, fin.coe_bit0, coe_one_eq_of_le],
  refine nat.mod_eq_of_lt (by linarith [show 3 ≤ n, from fact.out _]),
end

lemma coe_two_eq_of_le (n : ℕ) [fact $ 3 ≤ n] : (2 : fin n).val = 2 :=
two_val_eq_of_le n

end fin