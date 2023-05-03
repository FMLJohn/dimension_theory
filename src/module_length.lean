import ring_theory.simple_module

import .krull_dimension
import .composition_series_submodules

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

lemma module_length_eq_composition_series_length 
  (s : composition_series (submodule R M)) 
  (s0 : s 0 = ⊥) (s_last : s ⟨s.length, lt_add_one _⟩ = ⊤) :
  module_length R M = s.length :=
le_antisymm (supr_le $ λ i, begin 
  erw [with_bot.coe_le_coe, with_top.coe_le_coe],
  apply strict_chain.length_le_composition_series;
  assumption
end) $ le_supr_iff.mpr $ λ m hm, let s' : strict_chain (submodule R M) := 
{ len := s.length,
  func := s.series,
  strict_mono' := s.strict_mono } in begin 
  rw show s.length = s'.len, from rfl,
  apply hm,
end

lemma module_length_finite_iff_exists_maximal_strict_chain :
  (∃ (m : ℕ), module_length R M = m) ↔ ∃ (p : strict_chain (submodule R M)), is_top p :=
{ mp := λ hm, begin
    obtain ⟨m, hm⟩ := hm,
    by_contra rid,
    push_neg at rid,
    haveI : no_top_order (strict_chain (submodule R M)),
    { fconstructor,
      contrapose! rid,
      refine exists_imp_exists (λ x hx, hx) rid, },
    obtain ⟨x, hx⟩ := strict_chain.exists_len_gt_of_infinite_dim (submodule R M) (m + 1),
    suffices ineq1 : (m : ℕ±∞) < module_length R M,
    { exact ne_of_lt ineq1 hm.symm, },
    rw [module_length, lt_supr_iff],
    refine ⟨x, _⟩,
    erw [with_bot.coe_lt_coe, with_top.coe_lt_coe],
    exact lt_trans (lt_add_one _) hx,
  end,
  mpr := begin 
    rintros ⟨p, hp⟩,
    refine ⟨p.len, le_antisymm _ _⟩,
    { rw [module_length, supr_le_iff],
      intros i,
      erw [with_bot.coe_le_coe, with_top.coe_le_coe],
      exact hp i, },
    { rw [module_length, krull_dim],
      exact le_Sup ⟨_, rfl⟩, },
  end }

variables {R M}

lemma strict_chain.bot_eq_of_is_top (p : strict_chain (submodule R M)) (hp : is_top p) :
  p 0 = ⊥ :=
begin 
  by_contra rid,
  change p 0 ≠ ⊥ at rid,
  have rid' : ⊥ < p 0,
  { rwa bot_lt_iff_ne_bot, },
  specialize hp (p.cons ⊥ rid'),
  change _ + 1 ≤ _ at hp,
  linarith,
end

lemma strict_chain.last_eq_of_is_top (p : strict_chain (submodule R M)) (hp : is_top p) :
  p ⟨p.len, lt_add_one _⟩ = ⊤ :=
begin 
  by_contra rid,
  change p ⟨p.len, lt_add_one _⟩ ≠ ⊤ at rid,
  have rid' : p ⟨p.len, lt_add_one _⟩ < ⊤,
  { rwa lt_top_iff_ne_top, },
  specialize hp (p.snoc ⊤ rid'),
  change _ + 1 ≤ _ at hp,
  linarith,
end

lemma strict_chain.step'_of_is_top (p : strict_chain (submodule R M)) (hp : is_top p) :
  ∀ (i : fin p.len), p (fin.cast_succ i) ⋖ p i.succ :=
begin 
  by_contra rid,
  push_neg at rid,
  obtain ⟨i, hi⟩ := rid,
  erw not_covby_iff (p.strict_mono' (fin.cast_succ_lt_succ _)) at hi,
  obtain ⟨x, hx1, hx2⟩ := hi,
  have : p.len + 1 ≤ p.len := hp (p.insert_nth i x hx1 hx2),
  linarith,
end

lemma module_length_finite_iff_exists_composition_series :
  (∃ (m : ℕ), module_length R M = m) ↔ 
  ∃ (x : composition_series (submodule R M)), x 0 = ⊥ ∧ x ⟨x.length, lt_add_one _⟩ = ⊤ :=
begin 
  rw module_length_finite_iff_exists_maximal_strict_chain,
  split,
  { rintros ⟨p, hp⟩,
    have ics : strict_chain.is_composition_series p := 
      ⟨p.bot_eq_of_is_top hp, p.last_eq_of_is_top hp, p.step'_of_is_top hp⟩,
    refine ⟨p.to_composition_series ics, _, _⟩;
    rw strict_chain.to_composition_series_apply,
    { exact p.bot_eq_of_is_top hp, },
    { convert p.last_eq_of_is_top hp,
      ext,
      rw strict_chain.to_composition_series_length,
      simp only [coe_coe, fin.coe_mk, fin.coe_of_nat_eq_mod, nat.mod_succ_eq_iff_lt],
      exact lt_add_one _, }, },
  { rintros ⟨x, hx0, hx1⟩,
    refine ⟨⟨x.length, x, x.strict_mono⟩, λ y, _⟩,
    change y.len ≤ x.length,
    apply strict_chain.length_le_composition_series;
    assumption, },
end

end sanity_check