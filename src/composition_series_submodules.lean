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
sorry

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

/-
If two elements are adjecent in a deduped list, then they are adjecent in original one

-/
lemma list.is_adjecent_of_adjecent_in_dedup {X : Type*} [decidable_eq X] (l : list X)
  (i : ℕ) (hi : i < l.dedup.length - 1) : 
  ∃ (j : ℕ) (hj : j < l.length - 1), 
    l.dedup.nth_le i (lt_of_lt_of_le hi $ nat.sub_le _ 1) = 
    l.nth_le j (lt_of_lt_of_le hj $ nat.sub_le _ 1) ∧
    l.dedup.nth_le (i + 1) (nat.lt_pred_iff.mp hi) = l.nth_le (j + 1) (nat.lt_pred_iff.mp hj) := 
sorry

lemma list.dedup_chain'_covby_of_chain'_wcovby {X : Type*} [decidable_eq X] [partial_order X]
  (l : list X) (l_chain : l.chain' (⩿)) : l.dedup.chain' (⋖) :=
begin 
  rw list.chain'_iff_nth_le at l_chain ⊢,
  intros i hi,
  obtain ⟨j, hj, eq1, eq2⟩ := l.is_adjecent_of_adjecent_in_dedup i hi,
  rw [eq1, eq2],
  refine wcovby.covby_of_ne (l_chain j hj) _,
  rw [←eq1, ←eq2],
  exact (list.nodup.nth_le_inj_iff l.nodup_dedup _ _).not.mpr (by norm_num),
end

lemma list.chain'_covby_of_chain'_wcovby_of_nodup {X : Type*} [decidable_eq X] [partial_order X]
  (l : list X) (l_chain : l.chain' (⩿)) (l_nodup : l.nodup) :
  list.chain' (⋖) l :=
begin 
  rw ← list.dedup_eq_self at l_nodup,
  rw ← l_nodup,
  exact list.dedup_chain'_covby_of_chain'_wcovby _ l_chain,
end

lemma list.dedup_head_of_chain_wcoby {X : Type*} [decidable_eq X] [partial_order X] [inhabited X]
  (l : list X) (l_chain : l.chain' (⩿)) :
  l.dedup.head = l.head := sorry

lemma list.dedup_last_of_chain_wcoby {X : Type*} [decidable_eq X] [partial_order X] [inhabited X]
  (l : list X) (l_chain : l.chain' (⩿)) (hl : l ≠ list.nil) :
  l.dedup.last (list.dedup_ne_nil_of_ne_nil _ hl) = l.last hl := sorry

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

-- lemma inter_nth_le_to_qf_surj_of_nodup (h : (s.inter N).nodup) (i : ℕ) (hi : i < s.length) : 
--   function.surjective (s.inter_nth_le_to_qf N i hi) :=
-- begin 
--   intros z,
--   induction z using quotient.induction_on',
--   simp_rw [inter_nth_le_to_qf, linear_map.comp_apply, linear_map.restrict_apply, 
--     submodule.mkq_apply],
--   change ∃ _, _ = submodule.quotient.mk _,
--   simp_rw [submodule.quotient.eq, submodule.mem_comap, submodule.subtype_apply,
--     submodule.coe_sub, subtype.coe_mk],
  
-- end

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
  /-
  N ⊓ s i ⋖ N ⊓ s (i + 1) as N-submodule
  N ⊓ s i ≤ N ⊓ s (i + 1) as M-submodule
  if N ⊓ s i = s i as M-submodule (i.e. s i ≤ N)
  N ⊓ s i = s i ⋖ s (i + 1) as M-submodule
  then N ⊓ s (i + 1) = s i as M-submodule or N ⊓ s (i + 1) = s (i + 1) as M-submodule

  in latter case, nothing more to prove

  in previous case, 
    N ⊓ s (i + 1) = s i as N-module
    s i = N ⊓ s i ⋖ s i as N-module contradiction
    
  -/
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
  rwa [list.nth_le_zero, list.dedup_head_of_chain_wcoby _ (inter_chain'_wcovby s N), 
    ←list.nth_le_zero, inter0_eq_bot],
end

lemma of_inter_last (s0 : s 0 = ⊥) (slast : s ⟨s.length, lt_add_one _⟩ = ⊤) 
  [decidable_eq (submodule R N)] : s.of_inter N s0 slast ⟨_, lt_add_one _⟩ = ⊤ :=
begin 
  rw [of_inter, of_list],
  dsimp,
  rw [list.nth_le_length_sub_one, list.dedup_last_of_chain_wcoby _ (inter_chain'_wcovby s N), 
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

def composition_series_of_le (s0 : s 0 = ⊥) (slast : s ⟨s.length, lt_add_one _⟩ = ⊤) : 
  Σ' (s' : composition_series (submodule R N)), s' 0 = ⊥ ∧ s' ⟨s'.length, lt_add_one _⟩  = ⊤ :=
  ⟨composition_series.of_list _ (s.inter_is_composition_series_aux N s0 slast).some_spec.some 
    (s.inter_is_composition_series_aux N s0 slast).some_spec.some_spec.1, begin 
      have := (s.inter_is_composition_series_aux N s0 slast).some_spec.some_spec.2.1,
      dsimp [composition_series.of_list],
      rwa list.nth_le_zero,
    end, begin 
      have := (s.inter_is_composition_series_aux N s0 slast).some_spec.some_spec.2.2,
      dsimp [composition_series.of_list],
      rwa list.nth_le_length_sub_one,
    end⟩

end composition_series