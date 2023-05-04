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

lemma strict_chain.is_composition_series_iff (p : strict_chain (submodule R M)) :
  p.is_composition_series ↔ is_top p :=
{ mp := λ hp x, show x.len ≤ p.len, begin 
    have := strict_chain.length_le_composition_series 
    (p.to_composition_series hp) (strict_chain.to_composition_series_zero p hp)
      (strict_chain.to_composition_series_last p hp) x,
    refine le_trans this _,
    rw strict_chain.to_composition_series_length,
  end,
  mpr := λ hp, 
  { bot := strict_chain.bot_eq_of_is_top _ hp,
    top := strict_chain.last_eq_of_is_top _ hp,
    step' := strict_chain.step'_of_is_top _ hp } }

lemma noetherian_of_composition_series (s : composition_series (submodule R M))
  (s0 : s 0 = ⊥) (s_last : s ⟨_, lt_add_one _⟩ = ⊤) :
  is_noetherian R M :=
begin 
  rw is_noetherian_iff_well_founded,
  refine rel_embedding.well_founded_iff_no_descending_seq.2 ⟨λ a, _⟩,
  let p : strict_chain (submodule R M) := ⟨s.length + 1, λ x, a x, begin 
    intros i j h,
    dsimp,
    rw ← gt_iff_lt,
    erw a.2,
    exact h,
  end⟩,
  have : s.length + 1 ≤ s.length := strict_chain.length_le_composition_series s s0 s_last p,
  linarith only [this],
end

lemma submodule.exists_of_ne_top (N : submodule R M) (hN : N ≠ ⊤) : ∃ (x : submodule R M), N < x :=
begin 
  obtain ⟨m, -, nm⟩ := set_like.exists_of_lt (ne.lt_top hN : N < ⊤),
  refine ⟨N ⊔ R ∙ m, set_like.lt_iff_le_and_exists.mpr ⟨le_sup_left, ⟨m, _, nm⟩⟩⟩,
  exact (le_sup_right : (R ∙ m) ≤ _) (submodule.mem_span_singleton_self _)
end

lemma artinian_of_composition_series (s : composition_series (submodule R M))
  (s0 : s 0 = ⊥) (s_last : s ⟨_, lt_add_one _⟩ = ⊤) :
  is_artinian R M :=
⟨begin 
  refine rel_embedding.well_founded_iff_no_descending_seq.2 ⟨λ a, _⟩,
  let p : strict_chain (submodule R M) := ⟨s.length + 1, λ x, a (s.length + 1 - x), begin 
    intros i j h,
    dsimp,
    erw a.2,
    dsimp,
    change (i : ℕ) < j at h,
    have hi : (i : ℕ) ≤ _ := nat.le_of_lt_succ i.2,
    have hj : (j : ℕ) ≤ _ := nat.le_of_lt_succ j.2,
    apply nat.sub_lt_sub_of_lt;
    assumption,
  end⟩,
  have : s.length + 1 ≤ s.length := strict_chain.length_le_composition_series s s0 s_last p,
  linarith only [this],
end⟩

def smallest_supersubmodule [is_artinian R M] (N : submodule R M) : submodule R M :=
let wf : well_founded ((<) : submodule R M → submodule R M → Prop) := 
  (infer_instance : is_artinian R M).1 in
wf.succ N

lemma le_smallest_supersubmodule [is_artinian R M] (N : submodule R M) :
  N ≤ smallest_supersubmodule N :=
begin 
  delta smallest_supersubmodule,
  delta well_founded.succ,
  split_ifs,
  { exact le_of_lt (well_founded.min_mem _ _ _), },
  { exact le_refl _, }
end

lemma lt_smallest_supersubmodule_of_ne_top [is_artinian R M] (N : submodule R M) (hN : N ≠ ⊤) :
  N < smallest_supersubmodule N :=
begin 
  delta smallest_supersubmodule,
  generalize_proofs h,
  refine h.lt_succ (N.exists_of_ne_top hN),
end

lemma eq_top_of_eq_smallest_supersubmodule [is_artinian R M] (N : submodule R M) 
  (hN : N = smallest_supersubmodule N) : N = ⊤ :=
begin 
  contrapose! hN,
  exact ne_of_lt (lt_smallest_supersubmodule_of_ne_top N hN),
end

lemma eq_top_iff_eq_smallest_supersubmodule [is_artinian R M] (N : submodule R M) : 
  N = smallest_supersubmodule N ↔ N = ⊤ :=
begin 
  split,
  { exact eq_top_of_eq_smallest_supersubmodule N, },
  { rintro rfl,
    delta smallest_supersubmodule well_founded.succ,
    rw dif_neg,
    rintros ⟨y, hy⟩,
    exact not_top_lt hy, },
end

lemma covby_smallest_supersubmodule_of_ne_top [is_artinian R M] (N : submodule R M) (hN : N ≠ ⊤) :
  N ⋖ smallest_supersubmodule N :=
begin
  classical,
  rw covby_iff_lt_and_eq_or_eq,
  refine ⟨lt_smallest_supersubmodule_of_ne_top N hN, λ x hx1 hx2, _⟩,
  delta smallest_supersubmodule at hx2 ⊢,
  generalize_proofs h at hx2,
  rw le_iff_lt_or_eq at hx2,
  rcases hx2 with (hx2|rfl),
  { left,
    refine le_antisymm _ hx1,
    delta well_founded.succ at hx2,
    rw dif_pos (N.exists_of_ne_top hN) at hx2,
    have : ¬_ < _ := not_imp_not.mpr (well_founded.not_lt_min h _ _) (not_not.mpr hx2),
    rw [set_like.lt_iff_le_and_exists, not_and_distrib] at this,
    push_neg at this,
    exact this.resolve_left (not_not.mpr hx1), },
  { right, refl }
end

variables (R M)

def nth_largest_supersubmodule' [is_artinian R M]  (n : ℕ) : submodule R M := 
  smallest_supersubmodule ^[n] ⊥

lemma zeroth_largest_supersubmodule'_eq [is_artinian R M] : 
  (nth_largest_supersubmodule' R M 0 : submodule R M) = ⊥ :=
rfl

@[simps]
def nth_largest_supersubmodule [is_artinian R M] : ℕ →o submodule R M :=
{ to_fun := nth_largest_supersubmodule' R M,
  monotone' := λ m n h, begin 
    induction n with n ih,
    { rw zeroth_largest_supersubmodule'_eq, norm_num at h, subst h, exact bot_le },
    rw le_iff_lt_or_eq at h,
    rcases h with (h|rfl),
    { rw nat.lt_succ_iff at h,
      specialize ih h,
      refine le_trans ih _,
      delta nth_largest_supersubmodule',
      rw function.iterate_succ_apply',
      apply le_smallest_supersubmodule, },
    { exact le_refl _, },
  end }

lemma nth_largest_supersubmodule_eventually_stabilize [is_artinian R M] [is_noetherian R M] : 
  ∃ (n : ℕ), ∀ (m : ℕ), n ≤ m → 
    (nth_largest_supersubmodule R M n : submodule R M) = nth_largest_supersubmodule R M m :=
(monotone_stabilizes_iff_noetherian).mpr (infer_instance : is_noetherian R M) $
  nth_largest_supersubmodule R M

def nth_largest_supersubmodule_max_index [is_artinian R M] [is_noetherian R M] : ℕ :=
@@nat.find _ (λ _, classical.dec _) (nth_largest_supersubmodule_eventually_stabilize R M)

lemma nth_largest_supersubmodule_stablize_after_max_index [is_artinian R M] [is_noetherian R M] :
  ∀ (m : ℕ), nth_largest_supersubmodule_max_index R M ≤ m →
  nth_largest_supersubmodule R M (nth_largest_supersubmodule_max_index R M) = 
  nth_largest_supersubmodule R M m :=
begin 
  classical,
  exact nat.find_spec (nth_largest_supersubmodule_eventually_stabilize R M),
end

lemma nth_largest_supersubmodule_apply_max_index [is_artinian R M] [is_noetherian R M] :
  nth_largest_supersubmodule R M (nth_largest_supersubmodule_max_index R M) = ⊤ :=
begin 
  apply eq_top_of_eq_smallest_supersubmodule,
  rw show smallest_supersubmodule 
    ((nth_largest_supersubmodule R M) (nth_largest_supersubmodule_max_index R M)) = 
    nth_largest_supersubmodule R M (nth_largest_supersubmodule_max_index R M + 1),
  { rw [nth_largest_supersubmodule_coe, nth_largest_supersubmodule_coe, 
      nth_largest_supersubmodule', nth_largest_supersubmodule', function.iterate_succ'], },
  exact (nth_largest_supersubmodule_stablize_after_max_index R M) _ (le_of_lt $ lt_add_one _),
end

lemma nth_largest_supersubmodule_apply_of_lt_max_index [is_artinian R M] [is_noetherian R M] 
  (n : ℕ) (hn : n < nth_largest_supersubmodule_max_index R M) :
  nth_largest_supersubmodule R M n ≠ ⊤ :=
begin 
  classical,
  have H := (nat.lt_find_iff (nth_largest_supersubmodule_eventually_stabilize R M) n).mp hn n 
    (le_refl _),
  push_neg at H, 
  obtain ⟨m, hm1, hm2⟩ := H,
  intros rid,
  have ineq1 : nth_largest_supersubmodule R M n < nth_largest_supersubmodule R M m := 
    (le_iff_lt_or_eq.mp ((nth_largest_supersubmodule R M).2 hm1)).resolve_right hm2,
  rw rid at ineq1,
  refine not_top_lt ineq1,
end

@[simps]
def composition_series_of_artinian_and_noetherian [is_artinian R M] [is_noetherian R M] :
  composition_series (submodule R M) :=
{ length := nth_largest_supersubmodule_max_index R M,
  series := λ m, nth_largest_supersubmodule R M m,
  step' := λ i, show _ ⋖ _, begin 
    simp only [fin.coe_cast_succ, nth_largest_supersubmodule_coe, fin.coe_succ],
    have hi : (i : ℕ) < nth_largest_supersubmodule_max_index R M := i.2,
    delta nth_largest_supersubmodule',
    rw [function.iterate_succ_apply'],
    refine covby_smallest_supersubmodule_of_ne_top _ 
      (nth_largest_supersubmodule_apply_of_lt_max_index R M _ hi),
  end }

lemma composition_series_of_artinian_and_noetherian0 [is_artinian R M] [is_noetherian R M] :
  composition_series_of_artinian_and_noetherian R M 0 = ⊥ :=
by rw [composition_series_of_artinian_and_noetherian_series, fin.coe_zero, 
    nth_largest_supersubmodule_coe, nth_largest_supersubmodule', function.iterate_zero_apply]

lemma composition_series_of_artinian_and_noetherian_last [is_artinian R M] [is_noetherian R M] :
  composition_series_of_artinian_and_noetherian R M ⟨_, lt_add_one _⟩ = ⊤ :=
by rw [composition_series_of_artinian_and_noetherian_series, fin.coe_mk, 
    composition_series_of_artinian_and_noetherian_length, 
    nth_largest_supersubmodule_apply_max_index]

lemma module_length_finite_iff_notherian_and_aritinian :
  (∃ (m : ℕ), module_length R M = m) ↔ 
  (is_noetherian R M ∧ is_artinian R M) :=
begin 
  rw module_length_finite_iff_exists_composition_series,
  split,
  { rintros ⟨s, hs1, hs2⟩,
    exact ⟨noetherian_of_composition_series s hs1 hs2, artinian_of_composition_series s hs1 hs2⟩, },
  { rintros ⟨h1, h2⟩,
    resetI,
    refine ⟨composition_series_of_artinian_and_noetherian R M, 
      composition_series_of_artinian_and_noetherian0 R M, 
      composition_series_of_artinian_and_noetherian_last R M⟩, },
end

end sanity_check