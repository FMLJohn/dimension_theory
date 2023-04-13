import order.with_bot

/--
extended natural number with both negative and positive infinity.

**Warning** might be unexpected: in this implementation `⊥ + ⊤ = ⊥`.
-/
abbreviation eenat := with_bot (with_top ℕ)

notation `ℕ±∞` := eenat

namespace eenat

/--
recursor of extended natural number
-/
@[elab_as_eliminator] def rec {P : ℕ±∞ → Sort*} 
  (neg_infty : P ⊥) (pos_infty : P ⊤) (nat : ∀ (n : ℕ), P (some (some n))) :
  ∀ n, P n
| ⊥ := neg_infty
| (some ⊤) := pos_infty
| (some (some n)) := nat n

end eenat
