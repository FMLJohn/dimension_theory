import ring_theory.ideal.basic
import ring_theory.localization.at_prime

noncomputable theory

variables (R : Type*) [comm_ring R]

structure prime_ideal_chain :=
(len : ℕ)
(chain : fin (len + 1) → ideal R)
(is_chain : strict_mono chain)
[is_prime : ∀ i, (chain i).is_prime]

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