import ring_theory.ideal.basic
import ring_theory.localization.at_prime

noncomputable theory

variables (R : Type*) [comm_ring R]

/--

-/
structure prime_ideal_chain :=
(len : ℕ)
(chain : fin (len + 1) → ideal R)
(is_chain : strict_mono chain)
[is_prime : ∀ i, (chain i).is_prime]

namespace prime_ideal_chain


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


class finite_dimensional_ring : Prop :=
(fin_dim : ∃ (M : prime_ideal_chain R), ∀ (N : prime_ideal_chain R), N.len ≤ M.len)

variable [decidable $ finite_dimensional_ring R]

-- def krull_dim : with_top ℕ := 
-- if H : finite_dimensional_ring R 
-- then (H.fin_dim.some.len : with_top ℕ)
-- else ⊤

def krull_dim : ℕ := 
if H : finite_dimensional_ring R
then H.fin_dim.some.len
else 0

section height

variables {R} 
variable [∀ (p : ideal R) [hp : p.is_prime], decidable $ finite_dimensional_ring (localization.at_prime p)]

def ideal.height (p : ideal R) [p.is_prime] : ℕ :=
krull_dim (localization.at_prime p)

example (p : ideal R) [p.is_prime] : ℕ := p.height

end height

open_locale classical

def maximal_chain (S : Type*) [comm_ring S] [finite_dimensional_ring S] : prime_ideal_chain S :=
finite_dimensional_ring.fin_dim.some

def maximal_chain_wit (S : Type*) [comm_ring S] [finite_dimensional_ring S] : ∀ (N : prime_ideal_chain S), N.len ≤ (maximal_chain S).len:=
finite_dimensional_ring.fin_dim.some_spec



theorem subring_finite_dim (S : subring R) (H : finite_dimensional_ring S) (H1 : finite_dimensional_ring R) : krull_dim S ≤ krull_dim R :=
begin
unfreezingI { cases H with a b },

end
