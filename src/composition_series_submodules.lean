import ring_theory.simple_module

import .krull_dimension

noncomputable theory

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

lemma equiv_of_equiv_submodule_qf (i : ℕ) (hi : i < s.length) 
  (X : Type*) [add_comm_group X] [module R X] (Y : submodule R (s.qf i hi)) 
  (h : nonempty (X ≃ₗ[R] Y)) : 
  nonempty (X ≃ₗ[R] punit) ∨ nonempty (X ≃ₗ[R] s.qf i hi) :=
begin 
  unfreezingI 
  { obtain (rfl|rfl) := (s.qf_is_simple i hi).2 Y },
  { left, 
    refine h.map (λ i, i.trans (_ : _ ≃ₗ[R] _)),
    { exact ⟨λ _, punit.star, λ _ _, rfl, λ _ _, rfl, λ _, 0, λ _, subsingleton.elim _ _, 
        λ _, subsingleton.elim _ _⟩, }, },
  { right,
    refine h.map (λ i, i.trans (_ : _ ≃ₗ[R] _)),
    { refine ⟨coe, λ _ _, rfl, λ _ _, rfl, λ x, ⟨x, ⟨⟩⟩, λ _, by ext; refl, λ _, rfl⟩, }, },
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

lemma inter_chain'_wcovby : (s.inter N).chain' ((⩿)) :=
list.chain'_iff_nth_le.mpr $ λ i h, s.wcovby N i $ by 
  simpa only [inter_length, nat.add_succ_sub_one, add_zero] using h

end composition_series