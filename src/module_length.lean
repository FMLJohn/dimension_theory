import ring_theory.simple_module

import .krull_dimension

noncomputable theory

variables (R : Type*) [comm_ring R]
variables (M : Type*) [add_comm_group M] [module R M]

def module_length : ℕ±∞ := krull_dim (submodule R M)

section sanity_check

lemma module_length_eq : 
  (module_length R M) = ⨆ (p : strict_chain (submodule R M)) 
  (hp : p 0 = ⊥ ∧ p ⟨p.len, lt_add_one _⟩ = ⊤), p.len :=
le_antisymm (supr_le $ λ p, le_supr_iff.mpr $ λ m hm, begin 
  by_cases hp1 : p 0 = ⊥,
  { by_cases hp2 : p ⟨p.len, lt_add_one _⟩ = ⊤,
    { specialize hm p,
      rwa supr_pos at hm,
      exact ⟨hp1, hp2⟩, },
    { specialize hm (p.snoc ⊤ (lt_top_iff_ne_top.mpr hp2)),
      rw supr_pos at hm,
      work_on_goal 2 { exact ⟨hp1, strict_chain.snoc_last _ _ _⟩, },
      refine le_trans _ hm,
      dsimp,
      erw [with_bot.coe_le_coe, with_top.coe_le_coe],
      norm_num, }, },
  { by_cases hp2 : p ⟨p.len, lt_add_one _⟩ = ⊤, 
    { specialize hm (p.cons ⊥ (bot_lt_iff_ne_bot.mpr hp1)),
      rw supr_pos at hm,
      work_on_goal 2 { exact ⟨strict_chain.cons_zero _ _ _, hp2⟩, },
      refine le_trans _ hm,
      dsimp,
      erw [with_bot.coe_le_coe, with_top.coe_le_coe],
      norm_num, },
    { specialize hm ((p.cons ⊥ (bot_lt_iff_ne_bot.mpr hp1)).snoc ⊤ (lt_top_iff_ne_top.mpr hp2)),
      rw supr_pos at hm,
      work_on_goal 2 
      { refine ⟨_, strict_chain.snoc_last _ _ _⟩, 
        rw [strict_chain.snoc_func, fin.snoc, dif_pos],
        work_on_goal 2 { exact nat.zero_lt_succ _, },
        exact p.cons_zero _ _, },
      refine le_trans _ hm,
      dsimp,
      erw [with_bot.coe_le_coe, with_top.coe_le_coe],
      linarith, }, },

end) begin 
  rw show module_length R M = ⨆ (p : strict_chain (submodule R M)) (hp : true), p.len, from _,
  work_on_goal 2 { simp_rw supr_true, refl, },
  exact supr_le_supr_of_subset (λ _ _, ⟨⟩),
end

lemma module_length_nonneg : 0 ≤ module_length R M :=
le_Sup ⟨⟨0, λ _, ⊥, λ i j h, (ne_of_lt h $ subsingleton.elim _ _).elim⟩, rfl⟩

end sanity_check