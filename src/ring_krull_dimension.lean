import algebraic_geometry.prime_spectrum.basic
import ring_theory.ideal.basic
import algebra.module.localized_module

import .krull_dimension
import .topological_krull_dim

noncomputable theory

/--
The ring theoretic Krull dimension is the Krull dimension of prime spectrum ordered by inclusion.
-/
def ring_krull_dim (R : Type*) [comm_ring R] : ℕ±∞ :=
krull_dim (prime_spectrum R)


namespace ring_krull_dim

lemma eq_topological_krull_dim (R : Type*) [comm_ring R] :
  ring_krull_dim R = topological_krull_dim (prime_spectrum R) :=
eq.symm $ (krull_dim_eq_order_dual _).trans $ krull_dim_eq_of_order_iso $ order_iso.symm 
{ to_fun := order_dual.to_dual ∘ λ p, ⟨prime_spectrum.zero_locus p.as_ideal, 
    prime_spectrum.is_closed_zero_locus p.as_ideal, 
    (prime_spectrum.is_irreducible_zero_locus_iff _).mpr $ 
      by simpa only [p.is_prime.radical] using p.is_prime⟩,
  inv_fun := (λ s, ⟨prime_spectrum.vanishing_ideal s.1, 
    prime_spectrum.is_irreducible_iff_vanishing_ideal_is_prime.mp s.2.2⟩ : 
    {s : set (prime_spectrum R) | is_closed s ∧ is_irreducible s} → prime_spectrum R) ∘ 
    order_dual.of_dual,
  left_inv := λ p, begin 
    ext1,
    dsimp,
    rw [prime_spectrum.vanishing_ideal_zero_locus_eq_radical, p.is_prime.radical],
  end,
  right_inv := λ s, begin 
    ext1,
    dsimp only [order_dual.to_dual, order_dual.of_dual, equiv.coe_refl, id, subtype.coe_mk, 
      function.comp_apply],
    rw [prime_spectrum.zero_locus_vanishing_ideal_eq_closure],
    exact s.2.1.closure_eq,
  end,
  map_rel_iff' := begin 
    intros p q, 
    simp only [equiv.coe_fn_mk, order_dual.to_dual_le_to_dual, subtype.mk_le_mk, set.le_eq_subset],
    rw [prime_spectrum.zero_locus_subset_zero_locus_iff, q.is_prime.radical],
    refl,
  end }

/--
If `R ⟶ S` is a surjective ring homomorphism, then `ring_krull_dim S ≤ ring_krull_dim R`.
-/
theorem le_of_surj (R S : Type*) [comm_ring R] [comm_ring S] (f : R →+* S)
  (hf : function.surjective f) : ring_krull_dim S ≤ ring_krull_dim R :=
krull_dim_le_of_strict_mono (prime_spectrum.comap f)
  (monotone.strict_mono_of_injective (λ _ _ h, ideal.comap_mono h) 
    (prime_spectrum.comap_injective_of_surjective f hf))

/--
If `I` is an ideal of `R`, then `ring_krull_dim (R ⧸ I) ≤ ring_krull_dim R`.
-/
theorem le_of_quot (R : Type*) [comm_ring R] (I : prime_spectrum R) :
  ring_krull_dim (R ⧸ I.as_ideal) ≤ ring_krull_dim R :=
le_of_surj _ _ (ideal.quotient.mk I.as_ideal) ideal.quotient.mk_surjective

/--
If `R` and `S` are isomorphic, then `krull_dim R = krull_dim S`.
-/
theorem eq_of_ring_equiv (R S : Type*) [comm_ring R] [comm_ring S] (e : R ≃+* S) :
  ring_krull_dim R = ring_krull_dim S :=
le_antisymm (le_of_surj S R (ring_equiv.symm e)
    (equiv_like.surjective (ring_equiv.symm e)))
      (le_of_surj R S e (equiv_like.surjective e))

instance (F : Type*) [field F] : unique (prime_spectrum F) :=
{ default := ⟨⊥, ideal.bot_prime⟩,
  uniq := λ p, prime_spectrum.ext _ _ $ ideal.ext $ λ x, begin
    rw [submodule.mem_bot],
    refine ⟨λ h, _, λ h, h.symm ▸ submodule.zero_mem _⟩,
    rwa [p.as_ideal.eq_bot_of_prime, submodule.mem_bot] at h,
  end }

instance (F : Type*) [field F] : order_top (strict_chain (prime_spectrum F)) :=
{ top := default,
  le_top := λ ⟨l, f, h⟩, show l ≤ 0, from decidable.by_contradiction $ λ rid, 
    ne_of_gt (@h 0 1 begin 
      simpa only [show (0 : fin (l + 1)) = ⟨0, _⟩, from rfl, 
        show (1 : fin (l + 1)) = ⟨1, lt_add_of_pos_left _ (not_le.mp rid)⟩, begin 
          rw [fin.eq_iff_veq, fin.one_val, fin.val_eq_coe, fin.coe_mk, ← nat.succ_pred_eq_of_pos 
            (not_le.mp rid), nat.one_mod],
        end] using nat.zero_lt_one,
    end) (subsingleton.elim _ _) }

lemma eq_zero_of_field (F : Type*) [field F] : ring_krull_dim F = 0 :=
krull_dim_eq_len_of_order_top (prime_spectrum F)

lemma eq_zero_of_is_artinian_ring (R : Type*) [comm_ring R] [nontrivial R] [is_artinian_ring R] :
  ring_krull_dim R = 0 :=
begin
  haveI : inhabited (prime_spectrum R) := classical.inhabited_of_nonempty infer_instance,
  rw [ring_krull_dim, krull_dim_eq_supr_height],
  suffices : ∀ (a : prime_spectrum R), height a = 0,
  { simp_rw this, rw [supr_const], },
  intros p,
  refine le_antisymm _ (krull_dim_nonneg _),
  refine supr_le (λ q, _),
  erw [with_bot.coe_le_coe, with_top.coe_le_coe],
  by_contra' r,
  haveI : fact (2 ≤ q.len + 1),
  { fconstructor, linarith, },
  have : q 0 < q 1 := q.strict_mono' begin 
    change 0 < fin.val 1,
    rw fin.one_val_eq_of_le,
    exact nat.zero_lt_one,
  end,
  haveI H0 : (q 0).1.as_ideal.is_maximal := infer_instance,
  have EQ : q 0 = q 1,
  { rw [subtype.ext_iff_val, prime_spectrum.ext_iff], 
    exact H0.eq_of_le (q 1).1.is_prime.1 (le_of_lt this) },
  exact (ne_of_lt this EQ),
end

/--
Any PID that is not a field is finite dimensional with dimension 1
-/
@[simps]
def PID_finite_dimensional (R : Type*) [comm_ring R] [is_principal_ideal_ring R] [is_domain R] 
  (hR : ¬ is_field R) :
  order_top (strict_chain (prime_spectrum R)) :=
{ top := 
  { len := 1,
    func := (fin_two_arrow_equiv $ prime_spectrum R).symm ⟨⟨⊥, ideal.bot_prime⟩, 
      ⟨(ideal.exists_maximal R).some, (ideal.exists_maximal R).some_spec.is_prime⟩⟩,
    strict_mono' := λ i j h, 
    begin 
      fin_cases i; fin_cases j;
      try { refine (ne_of_lt h rfl).elim <|> refine (not_lt_of_lt h fin.zero_lt_one).elim },
      simpa only [fin_two_arrow_equiv_symm_apply, matrix.cons_val_zero, matrix.cons_val_one, 
        matrix.head_cons] using ideal.bot_lt_of_maximal _ hR,
      exact (ideal.exists_maximal R).some_spec,
    end },
  le_top := λ ⟨l, f, m⟩, show l ≤ 1, from decidable.by_contradiction $ λ rid, begin 
    rw not_le at rid,
    haveI : fact (2 ≤ l + 1) := ⟨by linarith⟩,
    haveI : fact (3 ≤ l + 1) := ⟨by linarith⟩,
    
    let a := submodule.is_principal.generator (f 1).as_ideal,
    let b := submodule.is_principal.generator (f 2).as_ideal,
    have lt1 : ideal.span {a} < ideal.span {b},
    { rw [ideal.span_singleton_generator, ideal.span_singleton_generator],
      refine m (_ : fin.val _ < fin.val _),
      rw [fin.one_val_eq_of_le, fin.two_val_eq_of_le],
      exact one_lt_two, },
    rw ideal.span_singleton_lt_span_singleton at lt1,
    rcases lt1 with ⟨h, ⟨r, hr1, hr2⟩⟩,
    have ha : prime a := submodule.is_principal.prime_generator_of_is_prime (f 1).as_ideal _,
    have hb : prime b := submodule.is_principal.prime_generator_of_is_prime (f 2).as_ideal _,
    { obtain ⟨x, hx⟩ := (hb.dvd_prime_iff_associated ha).mp ⟨r, hr2⟩,
      rw ←hx at hr2,
      rw ← mul_left_cancel₀ h hr2 at hr1, 
      refine (hr1 x.is_unit).elim },
    { intros h,
      suffices : (0 : fin (l + 1)) < 2,
      { have : (f 0).as_ideal < (f 2).as_ideal := m this,
        rw h at this,
        refine (not_le_of_lt this bot_le).elim },
      change (0 : fin _).1 < (2 : fin _).1,
      rw [fin.val_zero, fin.two_val_eq_of_le],
      exact zero_lt_two, },
    { intros h,
      suffices : (0 : fin (l + 1)) < 1,
      { have : (f 0).as_ideal < (f 1).as_ideal := m this,
        rw h at this,
        refine (not_le_of_lt this bot_le).elim },
      change (0 : fin _).1 < (1 : fin _).1,
      rw [fin.val_zero, fin.one_val_eq_of_le],
      exact zero_lt_one, },
  end }

lemma PID_eq_one_of_not_field (R : Type*) [comm_ring R] [is_principal_ideal_ring R] [is_domain R] 
  (hR : ¬ is_field R) :
  ring_krull_dim R = 1 :=
begin 
  rw [ring_krull_dim, @@krull_dim_eq_len_of_order_top _ _ (PID_finite_dimensional _ hR)],
  refl,
end

/--
https://stacks.math.columbia.edu/tag/00KG
-/
lemma eq_sup_height_maximal_ideals (R : Type*) [comm_ring R] :
  ring_krull_dim R = ⨆ (p : prime_spectrum R) (hp : p.as_ideal.is_maximal), height p :=
(krull_dim_eq_supr_height _).trans $ le_antisymm (supr_le $ λ p, begin
  let q : prime_spectrum R := ⟨(p.as_ideal.exists_le_maximal p.is_prime.1).some, 
    (p.as_ideal.exists_le_maximal _).some_spec.1.is_prime⟩,
  refine le_trans _ (le_Sup ⟨q, supr_pos ((p.as_ideal.exists_le_maximal _).some_spec.1)⟩),
  exact height_mono (p.as_ideal.exists_le_maximal _).some_spec.2,
end) begin 
  rw [show (⨆ (a : prime_spectrum R), height a) = ⨆ (a : prime_spectrum R) (h : true), height a, 
    by simp only [csupr_pos]],
  exact supr_le_supr_of_subset (λ x _, ⟨⟩),
end

/--
Suppose `I` is a prime ideal of `R`, then there is a canonical map from
`prime_spectrum (localization.at_prime I.as_ideal)` to `set.Iic I`.
-/
def localization_prime_spectrum_comap (R : Type*) [comm_ring R] (I : prime_spectrum R) :
  prime_spectrum (localization.at_prime I.as_ideal) → (set.Iic I) :=
  λ J, ⟨⟨J.as_ideal.comap (algebra_map R (localization.at_prime I.as_ideal)), ideal.is_prime.comap _⟩,
  λ z hz, @@decidable.by_contradiction (classical.dec _) $ λ hnz, J.is_prime.ne_top $ eq_top_iff.mpr $
    false.elim $ J.is_prime.1 $ (ideal.eq_top_iff_one _).mpr begin
      rw [show (1 : localization.at_prime I.as_ideal) = localization.mk z 1 * localization.mk 1
        ⟨z, hnz⟩, from _],
      refine ideal.mul_mem_right _ _ hz,
      rw [localization.mk_mul, mul_one, one_mul, localization.mk_eq_mk', is_localization.eq_mk'_iff_mul_eq,
        one_mul, subtype.coe_mk],
    end⟩

end ring_krull_dim
