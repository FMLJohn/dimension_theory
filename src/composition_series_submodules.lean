import ring_theory.simple_module
import data.list.indexes

import .krull_dimension

noncomputable theory

lemma relation.refl_trans_gen_of_chain'_wcovby {X : Type*} 
  [decidable_eq X] [inhabited X] [partial_order X]
  (l : list X) (hl : 0 < l.length) (l_chain : l.chain' (⩿)) : 
  relation.refl_trans_gen (⋖) (l.nth_le 0 hl) (l.nth_le (l.length - 1) $ by linarith) :=
begin 
  cases l with x0 l ih,
  { dsimp at hl, norm_num at hl },
  
  induction l with x1 l ih generalizing x0,
  { dsimp, exact relation.refl_trans_gen.refl },
  { dsimp at *, 
    specialize ih x1 (nat.zero_lt_succ _) (list.chain'_cons'.mp l_chain).2,
    have h1 : relation.refl_trans_gen (⋖) x0 x1,
    { rw list.chain'_cons at l_chain,
      by_cases eq0 : x0 = x1,
      { subst eq0, },
      { rw relation.refl_trans_gen.cases_head_iff,
        right,
        refine ⟨_, l_chain.1.covby_of_ne eq0, by refl⟩, }, },
    simp only [list.nth_le, add_zero, nat.add_succ_sub_one] at ih ⊢,
    refine relation.refl_trans_gen.trans h1 ih, },
end

lemma list.dedup_length_lt_of_not_nodup {X : Type*} [decidable_eq X] (l : list X) (h : ¬ l.nodup) :
  l.dedup.length < l.length :=
begin 
  contrapose! h,
  have h' := le_antisymm h (list.sublist.length_le (list.dedup_sublist _)),
  rw ←list.dedup_eq_self,
  exact list.sublist.eq_of_length (list.dedup_sublist _) h'.symm,
end

lemma list.dedup_ne_nil_of_ne_nil {X : Type*} [decidable_eq X] (l : list X) (h : l ≠ list.nil) :
  l.dedup ≠ list.nil := 
begin 
  contrapose! h,
  rw list.eq_nil_iff_forall_not_mem at h ⊢,
  intros a,
  rw ← list.mem_dedup,
  exact h a,
end

lemma list.map_ne_nil_of_ne_nil {X Y : Type*} (l : list X) (h : l ≠ list.nil)
  (f : X → Y) :
  l.map f ≠ list.nil := 
begin 
  induction l with x l ih,
  { cases h rfl, },
  { dsimp, exact list.cons_ne_nil _ _ },
end

lemma list.le_of_chain_le {X : Type*} [decidable_eq X] [partial_order X]
  (x : X) (l : list X) (l_chain : (x :: l).chain' (≤)) (y : X) (hy : y ∈ (x :: l)) :
  x ≤ y :=
begin 
  rw list.mem_cons_iff at hy,
  obtain (rfl|hy) := hy,
  { refl },
  rw list.mem_iff_nth_le at hy,
  obtain ⟨n, hn, rfl⟩ := hy,
  have s' : (x :: l).sorted (≤),
  { rw list.chain'_iff_pairwise at l_chain,
    exact l_chain, },
  rw [show x = (x :: l).nth_le 0 (nat.zero_lt_succ _), from rfl, 
    show l.nth_le n hn = (x :: l).nth_le n.succ (nat.succ_lt_succ hn), from rfl],
  refine s'.nth_le_mono (_ : (⟨0, _⟩ : fin (x :: l).length) ≤ ⟨n.succ, _⟩),
  exact nat.zero_le _,
end

lemma list.ge_of_chain_le {X : Type*} [decidable_eq X] [partial_order X]
  (x : X) (l : list X) (l_chain : (x :: l).chain' (≤)) (y : X) (hy : y ∈ (x :: l)) :
  y ≤ list.last (x :: l) (list.cons_ne_nil _ _)  :=
begin 
  have s' : (x :: l).sorted (≤),
  { rw list.chain'_iff_pairwise at l_chain,
    exact l_chain, },
  rw list.mem_iff_nth_le at hy,
  obtain ⟨m, hm, rfl⟩ := hy,
  rw [list.last_eq_nth_le],
  refine s'.nth_le_mono (_ : (⟨_, _⟩ : fin _) ≤ ⟨_, _⟩),
  exact nat.lt_succ_iff.mp hm,
end

lemma list.dedup_head'_of_chain_wcovby {X : Type*} [decidable_eq X] [partial_order X]
  (l : list X) (l_chain : l.chain' (⩿)) : l.dedup.head' = l.head' := 
match l, l_chain with
| [], _ := by simp
| x0::l, l_chain := begin 
  have ne_nil : (x0 :: l).dedup ≠ list.nil,
  { apply list.dedup_ne_nil_of_ne_nil, exact list.cons_ne_nil _ _ },
  obtain ⟨y, l', h⟩ : ∃ (y : X) (l' : list X), (x0 :: l).dedup = y :: l', 
  { induction h : (x0 :: l).dedup with y l' ih,
    { cases ne_nil h },
    exact ⟨y, l', rfl⟩, },
  rw [h, list.head', list.head'],
  have h1 : ∀ (x : X) (hx : x ∈ y :: l'), y ≤ x,
  { apply list.le_of_chain_le,
    rw ← h,
    exact list.chain'.sublist (l_chain.imp $ λ _ _, wcovby.le) (list.dedup_sublist _), },
  have h2 : ∀ (x : X) (hx : x ∈ x0 :: l), x0 ≤ x := λ x hx, 
    list.le_of_chain_le _ l (l_chain.imp $ λ _ _, wcovby.le) _ hx,
  rw le_antisymm (h1 x0 begin 
    rw [← h, list.mem_dedup],
    exact list.mem_cons_self _ _,
  end) (h2 y begin 
    have mem1 : y ∈ y :: l' := list.mem_cons_self _ _,
    rwa [← h, list.mem_dedup] at mem1,
  end),
end
end

lemma list.dedup_last_of_chain_wcovby {X : Type*} [decidable_eq X] [partial_order X] [inhabited X]
  (l : list X) (l_chain : l.chain' (⩿)) (hl : l ≠ list.nil) :
  l.dedup.last (list.dedup_ne_nil_of_ne_nil _ hl) = l.last hl := 
begin 
  obtain ⟨y, l', rfl⟩ : ∃ (y : X) (l' : list X), l = y :: l', 
  { induction l with y l' ih,
    { cases hl rfl },
    exact ⟨y, l', rfl⟩, },
  refine le_antisymm _ _,
  { apply list.ge_of_chain_le _ _ (l_chain.imp $ λ _ _, wcovby.le),
    rw ←list.mem_dedup, 
    exact list.last_mem _ },
  have ne_nil2 : (y :: l').dedup ≠ list.nil := list.dedup_ne_nil_of_ne_nil _ hl,
  obtain ⟨x, l, hl⟩ : ∃ (x : X) (l : list X), x :: l = (y :: l').dedup,
  { induction h : (y :: l').dedup with y l' ih,
    { cases ne_nil2 h, },
    exact ⟨_, _, rfl⟩, },
  simp_rw ← hl,
  refine list.ge_of_chain_le x l begin 
    rw hl,
    exact list.chain'.sublist (l_chain.imp $ λ _ _, wcovby.le) (list.dedup_sublist _),
  end _ _,
  rw [hl, list.mem_dedup],
  exact list.last_mem _,
end

lemma list.dedup_head_of_chain_wcovby {X : Type*} [decidable_eq X] [partial_order X] [inhabited X]
  (l : list X) (l_chain : l.chain' (⩿)) : l.dedup.head = l.head := 
by rwa [list.head_eq_head', list.head_eq_head', list.dedup_head'_of_chain_wcovby]

lemma list.dedup_chain'_wcovby_of_chain'_wcovby {X : Type*} [decidable_eq X] [partial_order X]
  (l : list X) (l_chain : l.chain' (⩿)) : l.dedup.chain' (⩿) := 
begin
  induction l with x l ih,
  { simp only [list.dedup_nil] },
  { rw list.chain'_cons' at l_chain,
    by_cases hx : x ∈ l,
    { rw list.dedup_cons_of_mem hx,
      exact ih l_chain.2 },
    { rw list.dedup_cons_of_not_mem hx,
      rw list.chain'_cons',
      refine ⟨_, ih l_chain.2⟩,
      rintros y (hy : _ = _), 
      refine l_chain.1 y (eq.trans (l.dedup_head'_of_chain_wcovby l_chain.2).symm hy) },  },
end

lemma list.dedup_chain'_covby_of_chain'_wcovby {X : Type*} [decidable_eq X] [partial_order X]
  (l : list X) (l_chain : l.chain' (⩿)) : l.dedup.chain' (⋖) := 
begin 
  have c := list.dedup_chain'_wcovby_of_chain'_wcovby l l_chain,
  rw list.chain'_iff_nth_le at c ⊢,
  simp_rw [wcovby_iff_covby_or_eq] at c,
  intros i hi,
  exact (c i hi).resolve_right (λ h, 
    by linarith [list.nodup_iff_nth_le_inj.mp l.nodup_dedup _ _ _ _ h]),
end

lemma list.chain'_covby_of_chain'_wcovby_of_nodup {X : Type*} [decidable_eq X] [partial_order X]
  (l : list X) (l_chain : l.chain' (⩿)) (l_nodup : l.nodup) :
  list.chain' (⋖) l :=
begin 
  rw ← list.dedup_eq_self at l_nodup,
  rw ← l_nodup,
  exact list.dedup_chain'_covby_of_chain'_wcovby _ l_chain,
end

section submodule

variables (R : Type*) [comm_ring R] (M : Type*) [add_comm_group M] [module R M]

def submodule.quotient_bot_equiv : (M ⧸ (⊥ : submodule R M)) ≃ₗ[R] M :=
begin
  refine linear_equiv.trans (submodule.quotient.equiv _ _ (linear_equiv.refl _ _) _)
    (linear_map.quot_ker_equiv_of_surjective (linear_map.id : M →ₗ[R] M) (λ y, ⟨_, rfl⟩)),
  { erw submodule.map_id,
    rw linear_map.ker_id, },
end

end submodule

namespace composition_series

variables {R : Type*} [comm_ring R] {M : Type*} [add_comm_group M] [module R M]
variables (s : composition_series (submodule R M)) (N : submodule R M)

@[reducible]
def qf (i : ℕ) (hi : i < s.length) : Type* :=
(s ⟨i + 1, (add_lt_add_iff_right _).mpr hi⟩) ⧸ 
  (submodule.comap (s ⟨i + 1, (add_lt_add_iff_right _).mpr hi⟩).subtype 
    (s ⟨i, hi.trans (lt_add_one _)⟩))

instance qf_is_simple (i : ℕ) (hi : i < s.length) : is_simple_module R (s.qf i hi) :=
begin 
  rw [←covby_iff_quot_is_simple (s.strict_mono.monotone _)],
  work_on_goal 2 { norm_num, },
  exact s.step ⟨i, hi⟩,
end

def equiv_of_equiv_submodule_qf' (i : ℕ) (hi : i < s.length) 
  (X : Type*) [add_comm_group X] [module R X] (Y : submodule R (s.qf i hi)) 
  (e : X ≃ₗ[R] Y) [decidable $ Y = ⊥] : 
  (X ≃ₗ[R] punit) ⊕ X ≃ₗ[R] s.qf i hi :=
or.by_cases ((s.qf_is_simple i hi).2 Y) 
  (λ eq1, sum.inl ⟨λ _, punit.star, λ _ _, rfl, λ _ _, rfl, λ _, 0, λ x, begin 
    dsimp,
    haveI : subsingleton Y,
    { rw eq1, exact unique.subsingleton, },
    haveI : subsingleton X := equiv.subsingleton e.to_equiv,
    exact subsingleton.elim _ _
  end, λ _, subsingleton.elim _ _⟩) 
  (λ eq1, sum.inr ⟨coe ∘ e, by { intros, simp only [function.comp_apply, map_add, 
    submodule.coe_add] }, by { intros, simp only [function.comp_apply, map_smul, ring_hom.id_apply,
    submodule.coe_smul] }, e.symm ∘ (λ x, ⟨x, eq1.symm ▸ ⟨⟩⟩), begin 
      intros x, 
      simp only [function.comp_apply],
      conv_rhs { rw ←linear_equiv.symm_apply_apply e x },
      congr' 1,
      ext, 
      refl, 
    end, begin 
      intros x,
      simp only [function.comp_apply],
      rw linear_equiv.apply_symm_apply,
      refl, 
    end⟩)

lemma equiv_of_equiv_submodule_qf (i : ℕ) (hi : i < s.length) 
  (X : Type*) [add_comm_group X] [module R X] (Y : submodule R (s.qf i hi)) 
  (h : nonempty (X ≃ₗ[R] Y)) : 
  nonempty (X ≃ₗ[R] punit) ∨ nonempty (X ≃ₗ[R] s.qf i hi) :=
begin
  classical,
  exact (s.equiv_of_equiv_submodule_qf' i hi X Y h.some).elim (or.inl ∘ nonempty.intro)
    (or.inr ∘ nonempty.intro),
end

@[reducible]
def inter : list (submodule R N) := 
  s.to_list.map $ λ si, submodule.comap N.subtype (N ⊓ si)

lemma inter_length : (s.inter N).length = s.length + 1 := 
by rw [inter, list.length_map, composition_series.to_list, list.length_of_fn]

lemma inter_nth_le (i : ℕ) (hi : i < s.length + 1) : 
  (s.inter N).nth_le i ((s.inter_length N).symm ▸ hi) = 
  submodule.comap N.subtype (N ⊓ s ⟨i, hi⟩) :=
begin 
  rw [list.nth_le_map],
  work_on_goal 2 { rwa [composition_series.to_list, list.length_of_fn], },
  congr' 2, 
  exact list.nth_le_of_fn _ ⟨i, _⟩,
end

lemma inter_le (i : ℕ) (hi : i < s.length) : 
  (s.inter N).nth_le i ((s.inter_length N).symm ▸ hi.trans $ lt_add_one _) ≤ 
  (s.inter N).nth_le (i + 1) ((s.inter_length N).symm ▸ (add_lt_add_iff_right 1).mpr hi) := 
begin 
  generalize_proofs h1 h2,
  rw inter_length at h1 h2,
  rw [inter_nth_le _ _ _ h1, inter_nth_le _ _ _ h2],
  refine submodule.comap_mono (le_inf inf_le_left (inf_le_right.trans _)),
  refine s.strict_mono.monotone _,
  norm_num,
end

@[reducible, derive [add_comm_group, module R]]
def inter_qf (i : ℕ) (hi : i < s.length) : Type* :=
  (s.inter N).nth_le (i + 1) ((s.inter_length N).symm ▸ (add_lt_add_iff_right 1).mpr hi) ⧸ 
  (submodule.comap 
    ((s.inter N).nth_le (i + 1) ((s.inter_length N).symm ▸ (add_lt_add_iff_right 1).mpr hi)).subtype
    ((s.inter N).nth_le i ((s.inter_length N).symm ▸ hi.trans $ lt_add_one _)))

@[reducible]
def inter_nth_le_to_qf (i : ℕ) (hi : i < s.length) :
  (s.inter N).nth_le (i+1) ((s.inter_length N).symm ▸ (add_lt_add_iff_right 1).mpr hi) →ₗ[R] 
  s.qf i hi :=
(submodule.mkq _).comp $ N.subtype.restrict $ λ ⟨x, hx1⟩ hx2, begin 
  rw [inter_nth_le, submodule.mem_comap] at hx2,
  exact hx2.2,
end

lemma inter_nth_le_to_qf_ker (i : ℕ) (hi : i < s.length) :
  (s.inter_nth_le_to_qf N i hi).ker = 
  (submodule.comap 
    ((s.inter N).nth_le (i + 1) ((s.inter_length N).symm ▸ (add_lt_add_iff_right 1).mpr hi)).subtype
    ((s.inter N).nth_le i (lt_of_lt_of_le hi $ (s.inter_length N).symm ▸ by norm_num))) :=
begin 
  ext ⟨x, hx⟩,
  rw [linear_map.mem_ker, submodule.mem_comap, submodule.subtype_apply, linear_map.comp_apply,
    linear_map.restrict_apply, submodule.mkq_apply, submodule.quotient.mk_eq_zero, 
    submodule.mem_comap, submodule.subtype_apply, subtype.coe_mk, 
    inter_nth_le s N i (hi.trans (lt_add_one _)), submodule.subtype_apply, submodule.coe_mk,
    submodule.mem_comap, submodule.subtype_apply, submodule.mem_inf, iff_and_self],
  intros hx',
  rw inter_nth_le s N _ _ at hx,
  work_on_goal 2 { linarith, },
  exact hx.1,
end

def inter_qf_equiv (i : ℕ) (hi : i < s.length) : 
  s.inter_qf N i hi ≃ₗ[R] (s.inter_nth_le_to_qf N i hi).range :=
linear_equiv.trans (submodule.quotient.equiv _ _ (linear_equiv.refl _ _) begin 
  rw inter_nth_le_to_qf_ker,
  exact submodule.map_id _,
end : _ ≃ₗ[R] _) ((s.inter_nth_le_to_qf N i hi).quot_ker_equiv_range)

lemma inter_qf_aux (i : ℕ) (hi : i < s.length) :
  nonempty (s.inter_qf N i hi ≃ₗ[R] punit) ∨
  nonempty (s.inter_qf N i hi ≃ₗ[R] s.qf i hi) := 
s.equiv_of_equiv_submodule_qf i hi _ _ ⟨s.inter_qf_equiv N i hi⟩

lemma inter_qf_aux' (i : ℕ) (hi : i < s.length) 
  [decidable (linear_map.range (s.inter_nth_le_to_qf N i hi) = ⊥)] :
  (s.inter_qf N i hi ≃ₗ[R] punit) ⊕
  (s.inter_qf N i hi ≃ₗ[R] s.qf i hi) := 
s.equiv_of_equiv_submodule_qf' i hi _ _ $ s.inter_qf_equiv N i hi

lemma eq_or_inter_qf_is_simple_module' (i : ℕ) (hi : i < s.length) :
  (s.inter N).nth_le (i + 1) ((s.inter_length N).symm ▸ (add_lt_add_iff_right 1).mpr hi) 
  = ((s.inter N).nth_le i (lt_of_lt_of_le hi $ (s.inter_length N).symm ▸ by norm_num))
  ∨ nonempty (s.inter_qf N i hi ≃ₗ[R] s.qf i hi) := 
begin 
  obtain ⟨⟨e⟩⟩|⟨⟨e⟩⟩ := s.inter_qf_aux N i hi,
  { left,
    have uniq_qf : nonempty (unique (s.inter_qf N i hi)) := ⟨equiv.unique e.to_equiv⟩,
    rw [submodule.unique_quotient_iff_eq_top, eq_top_iff] at uniq_qf,
    ext1, split,
    { intros hx, 
      have uniq_qf' := @uniq_qf ⟨x, hx⟩ ⟨⟩,
      rw submodule.mem_comap at uniq_qf',
      exact uniq_qf' },
    { intros hx, exact s.inter_le _ _ _ hx, }, },
  { right, exact ⟨e⟩, },
end

def eq_sum_inter_qf_is_simple_module' (i : ℕ) (hi : i < s.length)
  [decidable (linear_map.range (s.inter_nth_le_to_qf N i hi) = ⊥)] :
  (inhabited $ (s.inter N).nth_le (i + 1) ((s.inter_length N).symm ▸ (add_lt_add_iff_right 1).mpr hi) 
  = ((s.inter N).nth_le i (lt_of_lt_of_le hi $ (s.inter_length N).symm ▸ by norm_num)))
  ⊕ (s.inter_qf N i hi ≃ₗ[R] s.qf i hi) := 
(s.inter_qf_aux' N i hi).map (λ e, begin 
  have uniq_qf : nonempty (unique (s.inter_qf N i hi)) := ⟨equiv.unique e.to_equiv⟩,
  rw [submodule.unique_quotient_iff_eq_top, eq_top_iff] at uniq_qf,
  fconstructor,
  ext1, split,
  { intros hx, 
    have uniq_qf' := @uniq_qf ⟨x, hx⟩ ⟨⟩,
    rw submodule.mem_comap at uniq_qf',
    exact uniq_qf' },
  { intros hx, exact s.inter_le _ _ _ hx, }
end) $ λ e, e

lemma eq_or_inter_qf_is_simple_module (i : ℕ) (hi : i < s.length) :
  (s.inter N).nth_le (i + 1) ((s.inter_length N).symm ▸ (add_lt_add_iff_right 1).mpr hi) 
  = ((s.inter N).nth_le i (lt_of_lt_of_le hi $ (s.inter_length N).symm ▸ by norm_num))
  ∨ is_simple_module R (s.inter_qf N i hi) := 
begin 
  obtain ⟨⟨e⟩⟩|⟨⟨e⟩⟩ := s.inter_qf_aux N i hi,
  { left,
    have uniq_qf : nonempty (unique (s.inter_qf N i hi)) := ⟨equiv.unique e.to_equiv⟩,
    rw [submodule.unique_quotient_iff_eq_top, eq_top_iff] at uniq_qf,
    ext1, split,
    { intros hx, 
      have uniq_qf' := @uniq_qf ⟨x, hx⟩ ⟨⟩,
      rw submodule.mem_comap at uniq_qf',
      exact uniq_qf' },
    { intros hx, exact s.inter_le _ _ _ hx, }, },
  { right, exact is_simple_module.congr e, },
end

lemma eq_or_covby (i : ℕ) (hi : i < s.length) :
    ((s.inter N).nth_le i (lt_of_lt_of_le hi $ (s.inter_length N).symm ▸ by norm_num)) 
  = (s.inter N).nth_le (i + 1) ((s.inter_length N).symm ▸ (add_lt_add_iff_right 1).mpr hi)
  ∨ ((s.inter N).nth_le i (lt_of_lt_of_le hi $ (s.inter_length N).symm ▸ by norm_num)) ⋖ 
  (s.inter N).nth_le (i + 1) ((s.inter_length N).symm ▸ (add_lt_add_iff_right 1).mpr hi) := 
(s.eq_or_inter_qf_is_simple_module N i hi).elim (λ h, or.intro_left _ h.symm) 
    (λ h, or.intro_right _ $ (covby_iff_quot_is_simple $ s.inter_le N i hi).mpr h)
 
lemma wcovby (i : ℕ) (hi : i < s.length) :
    ((s.inter N).nth_le i (lt_of_lt_of_le hi $ (s.inter_length N).symm ▸ by norm_num)) 
  ⩿ (s.inter N).nth_le (i + 1) ((s.inter_length N).symm ▸ (add_lt_add_iff_right 1).mpr hi) := 
wcovby_iff_covby_or_eq.mpr $ or.symm $ s.eq_or_covby N i hi

lemma inter_chain'_wcovby : (s.inter N).chain' (⩿) :=
list.chain'_iff_nth_le.mpr $ λ i h, s.wcovby N i $ by 
  simpa only [inter_length, nat.add_succ_sub_one, add_zero] using h

lemma inter0_eq_bot (s0 : s 0 = ⊥) : 
  (s.inter N).nth_le 0 ((s.inter_length N).symm ▸ nat.zero_lt_succ _) = ⊥ :=
begin 
  rw [eq_bot_iff, inter_nth_le],
  rintros x ⟨hx1, (hx2 : ↑x ∈ s 0)⟩,
  rw s0 at hx2,
  rw submodule.mem_bot at hx2 ⊢,
  ext1,
  exact hx2,
end

lemma inter_last_eq_top (slast : s ⟨s.length, lt_add_one _⟩ = ⊤) : 
  (s.inter N).nth_le s.length ((s.inter_length N).symm ▸ lt_add_one _) = ⊤ :=
begin 
  rw [eq_top_iff, inter_nth_le],
  rintros ⟨x, hx⟩ ⟨⟩,
  exact ⟨hx, slast.symm ▸ ⟨⟩⟩,
end

def inter_qf_equiv_of_inter_nodup (h : (s.inter N).nodup)
  (i : ℕ) (hi : i < s.length)
  [decidable (linear_map.range (s.inter_nth_le_to_qf N i hi) = ⊥)] : 
  (s.inter_qf N i hi ≃ₗ[R] s.qf i hi) :=
sum.rec (λ ⟨r⟩, begin 
  have := (h.nodup.nth_le_inj_iff _ _).mp r,
  norm_num at this
end) id (s.eq_sum_inter_qf_is_simple_module' N i hi)

lemma eq_top_of_inter_qf_equiv (s0 : s 0 = ⊥) (slast : s ⟨s.length, lt_add_one _⟩ = ⊤)
  (h : (s.inter N).nodup)
  (i : ℕ) (hi : i < s.length + 1) :
  s ⟨i, hi⟩ = submodule.map N.subtype ((s.inter N).nth_le i (by rwa s.inter_length)) :=
begin
  classical,
  have inter_chain := list.chain'_covby_of_chain'_wcovby_of_nodup _ (s.inter_chain'_wcovby N) h,
  induction i with i ih,
  { rw [fin.mk_zero, s0, eq_comm, eq_bot_iff],
    rintros - ⟨y, hy, rfl⟩,
    rw [set_like.mem_coe, s.inter_nth_le N _ hi, fin.mk_zero, s0, inf_bot_eq, 
      submodule.comap_bot, linear_map.mem_ker] at hy,
    rw submodule.mem_bot,
    exact hy, },
  have ih' := ih ((lt_add_one _).trans hi), -- s i = N ⊓ s i
  have ih'' : s ⟨i, (lt_add_one _).trans hi⟩ = N ⊓ s ⟨i, (lt_add_one _).trans hi⟩,
  { rw [ih', eq_comm, inf_eq_right], 
    rintros _ ⟨y, hy, rfl⟩,
    rw [s.inter_nth_le N _ ((lt_add_one _).trans hi), set_like.mem_coe, submodule.mem_comap] at hy,
    exact hy.1, }, 
  have si_le : s ⟨i, (lt_add_one _).trans hi⟩ ≤ N,
  { rw ih'', exact inf_le_left, },
  
  rw list.chain'_iff_nth_le at inter_chain,
  have h1 := inter_chain i begin 
    rw [inter_length, nat.add_succ_sub_one, add_zero], 
    exact nat.succ_lt_succ_iff.mp hi, 
  end, -- N ⊓ s i ⋖ N ⊓ s (i + 1) as N-submodule
  generalize_proofs ineq1 ineq2 at h1,

  have le1 : N ⊓ s ⟨i, (lt_add_one _).trans hi⟩ ≤ N ⊓ s ⟨i + 1, hi⟩,
  { simp only [le_inf_iff, inf_le_left, true_and],
    refine le_trans inf_le_right (s.strict_mono.monotone _),
    norm_num, }, 
  have covby2 : s ⟨i, (lt_add_one _).trans hi⟩ ⋖ s ⟨i + 1, hi⟩,
  { refine s.step ⟨i, _⟩, rw inter_length at ineq2, exact nat.succ_lt_succ_iff.mp ineq2, },
  rw ← ih'' at le1,
  obtain (H|H) := covby2.eq_or_eq le1 inf_le_right,
  { have eq2 : (s.inter N).nth_le (i + 1) ineq2 = (s.inter N).nth_le i ineq1,
    { refine le_antisymm _ h1.le,
      rw [s.inter_nth_le N _ hi, s.inter_nth_le N _ ((lt_add_one _).trans hi)],
      refine submodule.comap_mono _,
      simp only [le_inf_iff, inf_le_left, true_and],
      rw H, 
      exact le_refl _, },
    have := (h.nodup.nth_le_inj_iff _ _).mp eq2,
    norm_num at this, },
  { rw ← H,
    ext1,
    rw [submodule.mem_inf, submodule.mem_map, inter_nth_le _ _ _ hi],
    split,
    { rintros ⟨hx1, hx2⟩,
      exact ⟨⟨x, hx1⟩, ⟨hx1, hx2⟩, rfl⟩, },
    { rintros ⟨y, ⟨hy1, hy2⟩, rfl⟩, exact ⟨submodule.coe_mem _, hy2⟩, }, },
end

lemma eq_top_of_inter_nodup (s0 : s 0 = ⊥) (slast : s ⟨s.length, lt_add_one _⟩ = ⊤) 
  (hinter : (s.inter N).nodup) :  N = ⊤ :=
begin 
  classical,
  have eq0 := s.eq_top_of_inter_qf_equiv N s0 slast hinter s.length (lt_add_one _),
  rw [slast, inter_nth_le, slast, inf_top_eq, submodule.map_comap_eq] at eq0,
  rw eq0,
  exact le_antisymm (λ x hx, ⟨⟨⟨x, hx⟩, rfl⟩, hx⟩) inf_le_right,
end

lemma inter_not_nodup_of_ne_top (s0 : s 0 = ⊥) (slast : s ⟨s.length, lt_add_one _⟩ = ⊤)
  (h : N < ⊤) : ¬ (s.inter N).nodup :=
begin 
  contrapose! h,
  rw [lt_top_iff_ne_top, not_ne_iff],
  apply eq_top_of_inter_nodup;
  assumption,
end

def of_inter (s0 : s 0 = ⊥) (slast : s ⟨s.length, lt_add_one _⟩ = ⊤) 
  [decidable_eq (submodule R N)] : 
  composition_series (submodule R N) :=
composition_series.of_list (s.inter N).dedup (list.dedup_ne_nil_of_ne_nil _ $ 
  list.map_ne_nil_of_ne_nil _ s.to_list_ne_nil _) $ list.dedup_chain'_covby_of_chain'_wcovby _ $ 
  inter_chain'_wcovby s N

lemma of_inter0 (s0 : s 0 = ⊥) (slast : s ⟨s.length, lt_add_one _⟩ = ⊤) 
  [decidable_eq (submodule R N)] : s.of_inter N s0 slast 0 = ⊥ :=
begin 
  rw [of_inter, of_list],
  dsimp,
  rwa [list.nth_le_zero, list.dedup_head_of_chain_wcovby _ (inter_chain'_wcovby s N), 
    ←list.nth_le_zero, inter0_eq_bot],
end

lemma of_inter_last (s0 : s 0 = ⊥) (slast : s ⟨s.length, lt_add_one _⟩ = ⊤) 
  [decidable_eq (submodule R N)] : s.of_inter N s0 slast ⟨_, lt_add_one _⟩ = ⊤ :=
begin 
  rw [of_inter, of_list],
  dsimp,
  rw [list.nth_le_length_sub_one, list.dedup_last_of_chain_wcovby _ (inter_chain'_wcovby s N), 
    ←list.nth_le_length_sub_one],
  work_on_goal 2 { simp only [inter_length, nat.add_succ_sub_one, add_zero, lt_add_iff_pos_right, 
    nat.lt_one_iff], },
  simp_rw [inter_length, nat.add_succ_sub_one, add_zero],
  rwa inter_last_eq_top,
end

lemma length_lt_of_lt [decidable_eq (submodule R N)] 
  (s0 : s 0 = ⊥) (slast : s ⟨s.length, lt_add_one _⟩ = ⊤) (h : N < ⊤) :
  ∃ (s' : composition_series (submodule R N)), 
    s' 0 = ⊥ ∧ s' ⟨_, lt_add_one _⟩ = ⊤ ∧ s'.length < s.length :=
⟨s.of_inter N s0 slast, s.of_inter0 N s0 slast, s.of_inter_last N s0 slast, begin 
  rw [of_inter, of_list], 
  dsimp,
  have ineq1 : (s.inter N).dedup.length < (s.inter N).length := 
    list.dedup_length_lt_of_not_nodup _ _,
  work_on_goal 2 { apply inter_not_nodup_of_ne_top; assumption, },
  rw inter_length at ineq1,
  have ineq2 : 0 < (s.inter N).dedup.length,
  { by_contra rid,
    push_neg at rid,
    norm_num at rid,
    rw list.length_eq_zero at rid,
    exact list.dedup_ne_nil_of_ne_nil _ (list.map_ne_nil_of_ne_nil _ s.to_list_ne_nil _) rid, },
  linarith,
end⟩

lemma inter_is_composition_series_aux (s0 : s 0 = ⊥) (slast : s ⟨s.length, lt_add_one _⟩ = ⊤) : 
  ∃ (l : list (submodule R N)) (hl : l ≠ list.nil), l.chain' (⋖) ∧ l.head = ⊥ ∧ l.last hl = ⊤ :=
begin 
  classical,
  have R := relation.refl_trans_gen_of_chain'_wcovby (s.inter N) _ (s.inter_chain'_wcovby N),
  work_on_goal 2 { rw inter_length, norm_num, },
  obtain ⟨l, hl1, hl2⟩ := list.exists_chain_of_relation_refl_trans_gen R,
  simp_rw [inter_length, nat.add_succ_sub_one, add_zero] at hl2,
  rw [inter0_eq_bot _ _ s0, inter_last_eq_top _ _ slast] at hl2,
  refine ⟨_ :: l, list.cons_ne_nil _ _, hl1, _, _⟩,
  { rw [list.head_cons, s.inter0_eq_bot N s0], },
  { rwa inter0_eq_bot _ _ s0, },
end

section classical

variables (R M)
open_locale classical

def module_length : with_top ℕ :=
if h : ∃ (s : composition_series (submodule R M)), s 0 = ⊥ ∧ s ⟨s.length, lt_add_one _⟩ = ⊤ 
then h.some.length 
else ⊤

lemma module_length_eq_length 
  (s : composition_series (submodule R M))
  (s0 : s 0 = ⊥) (s_last : s ⟨s.length, lt_add_one _⟩ = ⊤) :
  module_length R M = s.length :=
begin 
  delta module_length,
  split_ifs with h,
  { rw [with_top.coe_eq_coe],
    refine (jordan_holder _ _ _ _).length_eq,
    { rw [bot, bot, s0, h.some_spec.1], },
    { erw [top, top, s_last, h.some_spec.2] }, },
  { exact (h ⟨s, s0, s_last⟩).elim },
end

lemma module_length_lt_of_proper_submodule
  (s : composition_series (submodule R M))
  (s0 : s 0 = ⊥) (s_last : s ⟨s.length, lt_add_one _⟩ = ⊤)
  (N : submodule R M) (hN : N < ⊤) :
  module_length R N < module_length R M :=
begin 
  obtain ⟨x, x0, xlast, xlen⟩ := length_lt_of_lt s N s0 s_last hN,
  rwa [module_length_eq_length R N x x0 xlast, module_length_eq_length R M s s0 s_last,
    with_top.coe_lt_coe],
end

lemma module_length_congr
  (s : composition_series (submodule R M))
  (s0 : s 0 = ⊥) (s_last : s ⟨s.length, lt_add_one _⟩ = ⊤)
  (M' : Type*) [add_comm_group M'] [module R M']
  (e : M ≃ₗ[R] M') :
  module_length R M = module_length R M' :=
begin 
  rw [module_length_eq_length R M s s0 s_last, module_length_eq_length R M' ⟨s.length, 
    λ i, submodule.comap e.symm.to_linear_map (s i), begin 
      intros i, 
      change _ ⋖ _,
      have H : _ ⋖ _ := s.step i,
      rw covby_iff_quot_is_simple at H ⊢,
      work_on_goal 2 
      { exact submodule.comap_mono (s.strict_mono.monotone (le_of_lt $ fin.cast_succ_lt_succ _)), },
      work_on_goal 2
      { exact s.strict_mono.monotone (le_of_lt $ fin.cast_succ_lt_succ _) },
      refine @@is_simple_module.congr _ _ _ _ _ _ H,
      refine submodule.quotient.equiv _ _ _ _,
      { refine ⟨λ x, ⟨e.symm x, x.2⟩, _, _, λ x, ⟨e x, show e.symm (e x) ∈ _, begin 
          rw e.symm_apply_apply, exact x.2,
        end⟩, _, _⟩,
        { intros, ext, exact map_add _ _ _, },
        { intros, ext, exact map_smul e.symm r _, },
        { intros x, ext, exact e.apply_symm_apply _, },
        { intros x, ext, exact e.symm_apply_apply _, }, },
      { ext ⟨x, hx⟩,
        rw [submodule.mem_map, submodule.mem_comap],
        split,
        { rintros ⟨y, hy1, hy2⟩,
          rw [submodule.mem_comap, submodule.mem_comap, submodule.subtype_apply] at hy1,
          rw [linear_equiv.coe_mk, subtype.ext_iff, subtype.coe_mk, subtype.coe_mk] at hy2,
          rw [submodule.subtype_apply, submodule.coe_mk, ← hy2],
          exact hy1 },
        { intros hx,
          rw [submodule.subtype_apply, submodule.coe_mk] at hx,
          refine ⟨⟨e x, show e.symm (e x) ∈ _, by rwa e.symm_apply_apply⟩, _, _⟩,
          { rwa [submodule.mem_comap, submodule.subtype_apply, subtype.coe_mk, submodule.mem_comap, 
              linear_equiv.coe_to_linear_map, e.symm_apply_apply], },
          { rw [linear_equiv.coe_mk, subtype.ext_iff, subtype.coe_mk, subtype.coe_mk, 
              e.symm_apply_apply, subtype.coe_mk], }, }, },
    end⟩],
  { change submodule.comap _ _ = ⊥,
    rw [s0, submodule.comap_bot],
    exact linear_equiv.ker _, },
  { change submodule.comap _ (s ⟨s.length, lt_add_one _⟩) = ⊤,
    rw [s_last, submodule.comap_top], },
end

lemma module_length_lt_strict_mono
  (s : composition_series (submodule R M))
  (s0 : s 0 = ⊥) (s_last : s ⟨s.length, lt_add_one _⟩ = ⊤)
  (N1 N2 : submodule R M) (hN : N1 < N2) :
  module_length R N1 < module_length R N2 :=
begin 
  by_cases hN2 : N2 = ⊤,
  { subst hN2, 
    rw show module_length R (⊤ : submodule R M) = module_length R M, from 
      (module_length_congr R M s s0 s_last (⊤ : submodule R M) submodule.top_equiv.symm).symm,
    exact module_length_lt_of_proper_submodule R M s s0 s_last N1 hN, },
  { replace hN2 : N2 < ⊤,
    { rwa lt_top_iff_ne_top, },
    obtain ⟨s2, s20, s2_last, s2_len⟩ := length_lt_of_lt s N2 s0 s_last hN2,
    have lt' : (submodule.of_le $ le_of_lt hN).range < ⊤,
    { obtain ⟨x, hx1, hx2⟩ := (set_like.lt_iff_le_and_exists.mp hN).2,
      rw lt_top_iff_ne_top,
      intros r,
      have mem1 : (⟨x, hx1⟩ : N2) ∈ (⊤ : submodule R N2) := ⟨⟩,
      rw [←r, linear_map.mem_range] at mem1,
      obtain ⟨⟨y, hy1⟩, hy2⟩ := mem1,
      rw [subtype.ext_iff, subtype.coe_mk] at hy2,
      refine hx2 _,
      rw ←hy2,
      exact submodule.coe_mem _, },
    obtain ⟨s1, s10, s1_last, s1_len⟩ := length_lt_of_lt s2 (submodule.of_le $ le_of_lt hN).range 
      s20 s2_last lt',
    rwa [module_length_eq_length R N2 s2 s20 s2_last, show module_length R N1 = 
      module_length R (submodule.of_le $ le_of_lt hN).range, from _,
      module_length_eq_length R _ s1 s10 s1_last, with_top.coe_lt_coe],
    refine (module_length_congr R _ s1 s10 s1_last _ _).symm,
    rw [submodule.range_of_le],
    refine submodule.comap_subtype_equiv_of_le _,
    exact le_of_lt hN, },
end

end classical

end composition_series

variables {R : Type*} [comm_ring R] {M : Type*} [add_comm_group M] [module R M]
variables (s : composition_series (submodule R M))

lemma strict_chain.length_le_composition_series_aux 
  (s0 : s 0 = ⊥) (s_last : s ⟨s.length, lt_add_one _⟩ = ⊤)  
  (x : strict_chain (submodule R M)) (x_last : x ⟨x.len, lt_add_one _⟩ = ⊤) : x.len ≤ s.length :=
begin 
  classical,
  by_cases x_len : x.len = 0,
  { rw x_len, norm_num, },
  replace x_len : 0 < x.len,
  { contrapose! x_len,
    exact nat.eq_zero_of_le_zero x_len, },
  have : ∀ (i : fin x.len), composition_series.module_length R (x (fin.cast_succ i)) <
    composition_series.module_length R (x i.succ),
  { intros i,
    refine composition_series.module_length_lt_strict_mono R M s s0 s_last _ _ _,
    refine x.strict_mono' _,
    exact fin.cast_succ_lt_succ _, },
  have aux1 : ∀ (i : fin x.len), ↑i ≤ composition_series.module_length R (x (fin.cast_succ i)),
  { haveI : fact (0 < x.len) := ⟨x_len⟩,
    refine fin.induction_of_zero_lt x.len _ _,
    { norm_num },
    { intros i hi ih,
      specialize this ⟨i, lt_of_lt_of_le hi (by linarith)⟩,
      have ineq1 : ((i : ℕ) : with_top ℕ) < _ := lt_of_le_of_lt ih this,
      rw show fin.cast_succ (⟨i + 1, by linarith⟩ : fin x.len) = 
        (⟨i, by linarith⟩ : fin x.len).succ, from rfl,
      
      induction H : composition_series.module_length R (x (⟨i, by linarith⟩ : fin x.len).succ) with L,
      { exact le_top, },
      change _ = ↑L at H,
      rw H at *,
      erw with_top.coe_le_coe,
      erw with_top.coe_lt_coe at ineq1,
      change (i + 1) ≤ L, 
      rwa nat.succ_le_iff, } },
  specialize aux1 ⟨x.len - 1, by linarith⟩,
  have aux2 := lt_of_le_of_lt aux1 
    (composition_series.module_length_lt_of_proper_submodule R M s s0 s_last _ _),
  work_on_goal 2 
  { rw ←x_last,
    refine x.strict_mono' _,
    convert fin.cast_succ_lt_succ _ using 1,
    ext1,
    dsimp,
    linarith, },
  rw composition_series.module_length_eq_length R M s s0 s_last at aux2,
  erw with_top.coe_lt_coe at aux2,
  change _ - 1 < _ at aux2,
  linarith,
end

lemma strict_chain.length_le_composition_series
  (s0 : s 0 = ⊥) (s_last : s ⟨s.length, lt_add_one _⟩ = ⊤)  
  (x : strict_chain (submodule R M)) : x.len ≤ s.length :=
begin 
  by_cases x_last : x ⟨x.len, lt_add_one _⟩ = ⊤,
  { apply strict_chain.length_le_composition_series_aux;
    assumption, },
  let x' := x.snoc ⊤ (lt_top_iff_ne_top.mpr x_last),
  refine le_trans (le_of_lt (lt_add_one _ : x.len < x'.len)) (_ : x'.len ≤ _),
  apply strict_chain.length_le_composition_series_aux,
  { assumption },
  { assumption },
  exact strict_chain.snoc_last _ _ _,
end

variables {R M}

structure strict_chain.is_composition_series (x : strict_chain (submodule R M)) : Prop :=
(bot : x 0 = ⊥)
(top : x ⟨x.len, lt_add_one _⟩ = ⊤)
(step' : ∀ (i : fin x.len), x (fin.cast_succ i) ⋖ x i.succ)

def strict_chain.to_composition_series (x : strict_chain (submodule R M))
  (hx : x.is_composition_series) : composition_series (submodule R M) :=
composition_series.of_list (list.of_fn x) (λ r, begin
  rw list.eq_nil_iff_forall_not_mem at r,
  refine r (x 0) _,
  rw list.mem_of_fn,
  exact ⟨_, rfl⟩,
end) $ list.chain'_iff_nth_le.mpr $ λ i hi, show _ ⋖ _, begin
  simp only [list.length_of_fn, list.length, nat.add_succ_sub_one, add_zero] at hi,
  have eq1 := list.nth_le_of_fn x (⟨i, _⟩ : fin (x.len + 1)),
  simp_rw fin.coe_mk at eq1,
  have eq2 := list.nth_le_of_fn x (⟨i + 1, _⟩ : fin (x.len + 1)),
  simp_rw fin.coe_mk at eq2,
  rw [eq1, eq2],
  exact hx.step' ⟨i, hi⟩,
end

lemma strict_chain.to_composition_series_length (x : strict_chain (submodule R M))
  (hx : x.is_composition_series) : (x.to_composition_series hx).length = x.len :=
begin 
  delta strict_chain.to_composition_series composition_series.of_list,
  dsimp,
  rw list.length_of_fn,
  simp only [nat.add_succ_sub_one, add_zero],
end

lemma strict_chain.to_composition_series_apply (x : strict_chain (submodule R M))
  (hx : x.is_composition_series) (n) : (x.to_composition_series hx n) = x n :=
begin 
  delta strict_chain.to_composition_series composition_series.of_list,
  dsimp,
  rw list.nth_le_of_fn',
  congr,
  symmetry,
  rw nat.mod_succ_eq_iff_lt,
  refine lt_of_lt_of_le n.2 _,
  delta strict_chain.to_composition_series,
  rw composition_series.length_of_list,
  refine nat.succ_le_succ _,
  rw [←nat.pred_eq_sub_one, nat.pred_le_iff, list.length_of_fn],
end

lemma strict_chain.to_composition_series_zero (x : strict_chain (submodule R M))
  (hx : x.is_composition_series) : x.to_composition_series hx 0 = ⊥ :=
begin 
  rw x.to_composition_series_apply,
  exact hx.bot,
end

lemma strict_chain.to_composition_series_last (x : strict_chain (submodule R M))
  (hx : x.is_composition_series) : x.to_composition_series hx ⟨_, lt_add_one _⟩ = ⊤ :=
begin 
  rw x.to_composition_series_apply,
  rw strict_chain.to_composition_series_length,
  convert hx.top,
  ext,
  simp only [coe_coe, fin.coe_mk, fin.coe_of_nat_eq_mod, nat.mod_succ_eq_iff_lt],
  exact lt_add_one _,
end
