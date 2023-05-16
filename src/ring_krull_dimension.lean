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


/-
Here we aim to show that for any prime ideal `I` of a commutative ring `R`, the
height of `I` equals the krull dimension of `localization.at_prime I.as_ideal`.
-/
section about_height_and_localization

noncomputable theory

variables {R : Type*} [comm_ring R] (I : prime_spectrum R) (J : ideal R)

@[reducible] def ideal_image_span := J.map (algebra_map R (localization.at_prime I.as_ideal))

/-- The canonical map from the ideal J of R to its image JR_I in the localisation. -/
@[simps apply] def map_from_ideal_to_ideal_image_span :
  J →ₗ[R] ideal_image_span I J :=
{ to_fun := λ x, ⟨localization.mk x 1, submodule.subset_span ⟨_, x.2, rfl⟩⟩,
  map_add' := λ _ _, subtype.ext (localization.add_mk_self _ _ _).symm,
  map_smul' := λ _ _, subtype.ext (localization.smul_mk _ _ _).symm, }

@[simps] def localization_at_prime_div_by (s : I.as_ideal.prime_compl) :
  module.End (localization.at_prime I.as_ideal) (localization.at_prime I.as_ideal) :=
{ to_fun := λ x, (localization.mk 1 s) * x,
  map_add' := mul_add _,
  map_smul' := λ r x, by { dsimp, ring } }

lemma localization_at_prime_div_by_range (s) (x) (hx : x ∈ ideal_image_span I J) :
  (localization_at_prime_div_by I s) x ∈ ideal_image_span I J :=
submodule.span_induction hx (λ _ ⟨_, hx1, hx2⟩, ideal.mul_mem_left _ _
  (ideal.subset_span ⟨_, hx1, hx2⟩)) (by simpa only [map_zero] using submodule.zero_mem _)
(λ _ _ h1 h2, by simpa only [map_add] using submodule.add_mem _ h1 h2) $ λ a _ h,
  by simpa only [localization_at_prime_div_by_apply, mul_smul_comm] using ideal.mul_mem_left _ a h

variables {I}

def module.End.inv (s) : module.End R (ideal_image_span I J) :=
(linear_map.restrict _ $ localization_at_prime_div_by_range I J s).restrict_scalars R

lemma module.End.inv_left (s : I.as_ideal.prime_compl) :
  algebra_map R _ s * module.End.inv J s = 1 :=
linear_map.ext $ λ x, show (s : R) • module.End.inv J s x = x, from subtype.ext $
  show (s : R) • (localization.mk 1 s * x) = x, by rw [←smul_mul_assoc, localization.smul_mk,
    smul_eq_mul, mul_one, localization.mk_self, one_mul]

lemma module.End.inv_right (s : I.as_ideal.prime_compl) :
  (module.End.inv J s) * algebra_map R _ s = 1 :=
linear_map.ext $ λ x, subtype.ext $ show localization.mk 1 s * ((s : R) • x) = x,
  by rw [mul_smul_comm, ←smul_mul_assoc, localization.smul_mk, smul_eq_mul, mul_one,
    localization.mk_self, one_mul]

lemma map_from_ideal_to_ideal_image_span_is_surj (y) :
  ∃ (x : J × I.as_ideal.prime_compl), (x.2 : R) • y = map_from_ideal_to_ideal_image_span I J x.1 :=
begin
  rcases y with ⟨y, h⟩,
  refine submodule.span_induction' (by { rintros _ ⟨_, h, rfl⟩, refine ⟨⟨⟨_, h⟩, 1⟩, one_smul _ _⟩ })
    _ _ _ h,
  { refine ⟨⟨0, 1⟩, (_ : 1 • 0 = _)⟩, rw [one_smul, map_zero], },
  { rintros x hx y hy ⟨⟨mx, nx⟩, hmnx⟩ ⟨⟨my, ny⟩, hmny⟩,
    refine ⟨⟨(nx : R) • my + (ny : R) • mx, nx * ny⟩, subtype.ext _⟩,
    have : ↑ny • ↑nx • x + ↑nx • ↑ny • y =
      ↑ny • localization.mk ↑mx 1 + ↑nx • localization.mk ↑my 1,
    { exact subtype.ext_iff.mp (congr_arg2 (+) (congr_arg ((•) (ny : R)) hmnx)
      (congr_arg ((•) (nx : R)) hmny)) },
    rwa [smul_comm, ←smul_add, ←smul_add, localization.smul_mk, localization.smul_mk,
      localization.add_mk_self, ←mul_smul, add_comm (_ • _)] at this, },
  { rintros a x hx ⟨⟨c1, c2⟩, (hc : (c2 : R) • _ = _)⟩,
    induction a using localization.induction_on,
    induction x using localization.induction_on,
    rcases ⟨a, x⟩ with ⟨⟨d1, d2⟩, ⟨x1, x2⟩⟩,
    refine ⟨⟨⟨d1 • c1, ideal.mul_mem_left J d1 (set_like.coe_mem c1)⟩, d2 * c2⟩,
      subtype.ext (_ : (_ * _) • (localization.mk _ _ * _) = localization.mk (_ • _) _)⟩,
    rw [←localization.smul_mk (d1 : R) (c1 : R) 1, show localization.mk ↑c1 1 = ↑c2 •
      localization.mk _ _, from (subtype.ext_iff.mp hc).symm, localization.smul_mk,
      localization.smul_mk, localization.mk_mul, localization.smul_mk, smul_eq_mul,
      localization.mk_eq_mk_iff, localization.r_iff_exists],
    exact ⟨1, by dsimp; ring⟩, }
end

lemma map_from_ideal_to_ideal_image_span_apply_eq_iff (x₁ x₂) :
  (map_from_ideal_to_ideal_image_span I J) x₁ = (map_from_ideal_to_ideal_image_span I J) x₂ ↔
  ∃ (c : (I.as_ideal.prime_compl)), (c : R) • x₂ = (c : R) • x₁ :=
subtype.ext_iff.trans $ localization.mk_eq_mk_iff.trans $ localization.r_iff_exists.trans $
  exists_congr $ λ x, eq_comm.trans $ iff.symm $ subtype.ext_iff.trans $ by simp [smul_eq_mul]

instance : is_localized_module I.as_ideal.prime_compl _ :=
{ map_units := λ s, ⟨⟨_, _, module.End.inv_left _ s, module.End.inv_right _ s⟩, rfl⟩,
  surj := map_from_ideal_to_ideal_image_span_is_surj J,
  eq_iff_exists := map_from_ideal_to_ideal_image_span_apply_eq_iff _ }

variable (I)

def equiv_between_localized_module_and_ideal_image_span :
  (localized_module I.as_ideal.prime_compl J) ≃ₗ[R] ideal_image_span I J :=
is_localized_module.iso _ $ map_from_ideal_to_ideal_image_span I J

lemma equiv_between_localized_module_and_ideal_image_span_apply (a b) :
  equiv_between_localized_module_and_ideal_image_span I J (localized_module.mk a b) =
  ⟨localization.mk a b, by simpa only [show localization.mk (a : R) b =
    (localization.mk 1 b) * (localization.mk a 1), by rw [localization.mk_mul, one_mul, mul_one]]
      using ideal.mul_mem_left _ _ (ideal.apply_coe_mem_map _ J a)⟩ :=
(module.End_algebra_map_is_unit_inv_apply_eq_iff _ _ _).mpr begin
  refine subtype.ext (_ : localization.mk _ _ = _ • localization.mk (a : R) b),
  rw [localization.smul_mk, smul_eq_mul, localization.mk_eq_mk_iff, localization.r_iff_exists],
  exact ⟨1, by simp⟩,
end

@[simps]
def ideal_image_span' : ideal (localization.at_prime I.as_ideal) :=
{ carrier := {x | ∃ (a : J) (b : I.as_ideal.prime_compl), x = localization.mk a b},
  add_mem' := λ x y ⟨a1, ⟨b1, hx⟩⟩ ⟨a2, ⟨b2, hy⟩⟩, hx.symm ▸ hy.symm ▸
    ⟨⟨_, J.add_mem (J.mul_mem_left b1 (set_like.coe_mem a2))
      (J.mul_mem_left b2 (set_like.coe_mem a1))⟩, ⟨b1 * b2, localization.add_mk _ _ _ _⟩⟩,
  zero_mem' := ⟨0, ⟨1, by simp⟩⟩,
  smul_mem' := λ c, localization.induction_on c $ by { rintro ⟨c1, c2⟩ x ⟨j, ⟨a, rfl⟩⟩,
    exact ⟨⟨_, J.mul_mem_left c1 (set_like.coe_mem j)⟩, ⟨c2 * a, localization.mk_mul _ _ _ _⟩⟩ } }

lemma mem_ideal_image_span'_iff (x : localization.at_prime I.as_ideal) :
  x ∈ ideal_image_span' I J ↔ ∃ (a : J) (b : I.as_ideal.prime_compl), x = localization.mk a b :=
iff.rfl

lemma mem_ideal_image_span'_of_mem_ideal_image_span :
  ∀ x, x ∈ ideal_image_span I J → x ∈ ideal_image_span' I J :=
λ _,  submodule.span_induction' (λ _ ⟨y, hy1, hy2⟩, hy2 ▸ ⟨⟨y, hy1⟩, ⟨_, rfl⟩⟩) (ideal.zero_mem _)
  (λ _ _ _ _, ideal.add_mem _) (λ a _ _, submodule.smul_mem _ a)

lemma ideal_image_span'_eq_ideal_image_span :
  ideal_image_span' I J = ideal_image_span I J :=
le_antisymm begin
  rintros x ⟨⟨a, ha⟩, ⟨b, rfl⟩⟩,
  rw [subtype.coe_mk, ←one_mul a, ←mul_one b, ←localization.mk_mul],
  exact ideal.mul_mem_left _ _ (ideal.mem_map_of_mem _ ha),
end $ mem_ideal_image_span'_of_mem_ideal_image_span _ _

instance ideal_image_span'_is_prime (J : set.Iic I) :
  (ideal_image_span' I J.1.as_ideal).is_prime :=
{ ne_top' := λ hit, begin
    rw [ideal.eq_top_iff_one, mem_ideal_image_span'_iff] at hit,
    rcases hit with ⟨a, ⟨b, hb⟩⟩,
    exact (is_localization.at_prime.is_unit_mk'_iff (localization.at_prime I.as_ideal) _
      (a : R) b).mp (by simpa only [←localization.mk_eq_mk', ←hb] using is_unit_one) (J.2 a.2),
  end,
  mem_or_mem' := λ x y, localization.induction_on₂ x y begin
    rintros ⟨a1, a2⟩ ⟨b1, b2⟩ ⟨⟨p, hp⟩, ⟨q, h⟩⟩,
    rw [localization.mk_mul, localization.mk_eq_mk_iff, localization.r_iff_exists] at h,
    obtain ⟨c, hc⟩ := h,
    have h : ↑c * (↑q * (a1 * b1)) ∈ J.1.as_ideal := hc.symm ▸ J.1.as_ideal.mul_mem_left _
      (J.1.as_ideal.mul_mem_left _ hp),
    rw ←mul_assoc at h,
    exact (J.1.is_prime.mem_or_mem ((J.1.is_prime.mem_or_mem h).resolve_left
      (λ h, submonoid.mul_mem _ c.2 q.2 (J.2 h)))).elim (λ h, or.intro_left _ ⟨⟨a1, h⟩, ⟨_, rfl⟩⟩)
        (λ h, or.intro_right _ ⟨⟨b1, h⟩, ⟨_, rfl⟩⟩),
  end }

/--
There is a canonical map from `set.Iic I` to `prime_spectrum (localization.at_prime I.as_ideal)`.
-/
@[simp]
def localization_prime_spectrum_map :
  set.Iic I → prime_spectrum (localization.at_prime I.as_ideal) :=
  λ I', ⟨ideal_image_span' I I'.1.as_ideal, infer_instance⟩

/--
There is a canonical map from `prime_spectrum (localization.at_prime I.as_ideal)` to `set.Iic I`.
-/
@[simp]
def localization_prime_spectrum_comap :
  prime_spectrum (localization.at_prime I.as_ideal) → set.Iic I :=
  λ J, ⟨⟨_, ideal.is_prime.comap (algebra_map R (localization.at_prime I.as_ideal))⟩, λ z hz,
    @@decidable.by_contradiction (classical.dec _) $ λ hnz, J.is_prime.ne_top $ eq_top_iff.mpr $
    false.elim $ J.is_prime.1 $ (ideal.eq_top_iff_one _).mpr begin
      rw [show (1 : localization.at_prime I.as_ideal) = localization.mk z 1 * localization.mk 1
        ⟨z, hnz⟩, by simpa only [localization.mk_one_eq_algebra_map, ←algebra.smul_def,
          localization.smul_mk, smul_eq_mul, mul_one, eq_comm] using localization.mk_self
            (⟨z, hnz⟩ : I.as_ideal.prime_compl)],
      exact ideal.mul_mem_right _ _ hz,
    end⟩

/--
The canonical map from `prime_spectrum (localization.at_prime I.as_ideal)` to `set.Iic I` is a left
inverse to the canonical map from `set.Iic I` to `prime_spectrum (localization.at_prime I.as_ideal)`.
-/
lemma localization_prime_spectrum_comap_is_left_inverse : function.left_inverse
  (localization_prime_spectrum_comap I) (localization_prime_spectrum_map I) :=
begin
  intro J, ext x, split,
  { intro hx,
    simp only [localization_prime_spectrum_comap, localization_prime_spectrum_map,
      subtype.val_eq_coe, subtype.coe_mk, ideal.mem_comap] at hx,
    change localization.mk x 1 ∈ ideal_image_span' I J.val.as_ideal at hx,
    rw mem_ideal_image_span'_iff at hx,
    rcases hx with ⟨a, b, hab⟩,
    rw [localization.mk_eq_mk_iff, localization.r_iff_exists] at hab,
    simp only [submonoid.coe_one, one_mul] at hab,
    rcases hab with ⟨c, hc⟩,
    rw ←mul_assoc at hc,
    refine (or_iff_not_imp_left.1 (ideal.is_prime.mem_or_mem J.val.2 (@set.mem_of_eq_of_mem R
      (↑c * ↑b * x) (↑c * ↑a) J.val.as_ideal hc (ideal.mul_mem_left J.val.as_ideal ↑c a.2)))) _,
    intro hi,
    exact (submonoid.mul_mem I.as_ideal.prime_compl c.2 b.2) (J.2 hi), },
  { intro hx,
    simp only [localization_prime_spectrum_comap, localization_prime_spectrum_map,
      subtype.val_eq_coe, subtype.coe_mk, ideal.mem_comap],
    change localization.mk x 1 ∈ ideal_image_span' I J.val.as_ideal,
    rw mem_ideal_image_span'_iff,
    use ⟨x, hx⟩, use 1,
    refl, },
end

/--
The canonical map from `prime_spectrum (localization.at_prime I.as_ideal)` to `set.Iic I` is a right
inverse to the canonical map from `set.Iic I` to `prime_spectrum (localization.at_prime I.as_ideal)`.
-/
lemma localization_prime_spectrum_comap_is_right_inverse : function.right_inverse
  (localization_prime_spectrum_comap I) (localization_prime_spectrum_map I) :=
begin
  intro J, ext x, split,
  { intro hx,
    simp only [localization_prime_spectrum_comap, localization_prime_spectrum_map,
      subtype.val_eq_coe, subtype.coe_mk, ideal.mem_comap] at hx,
    rw mem_ideal_image_span'_iff at hx,
    rcases hx with ⟨⟨a, ha⟩, ⟨b, hab⟩⟩,
    dsimp at ha hab,
    change localization.mk a 1 ∈ J.as_ideal at ha,
    rw [←one_mul a, ←mul_one b, ←localization.mk_mul] at hab,
    rw hab,
    exact ideal.mul_mem_left J.as_ideal (localization.mk 1 b) ha, },
  { refine localization.induction_on x _,
    rintros ⟨a, b⟩ hab,
    simp only [localization_prime_spectrum_comap, localization_prime_spectrum_map,
      subtype.val_eq_coe, subtype.coe_mk, ideal.mem_comap] at *,
    rw mem_ideal_image_span'_iff,
    use a, dsimp,
    { change localization.mk a 1 ∈ J.as_ideal,
      have hab' : (localization.mk (b : R) 1) * (localization.mk a b) = localization.mk a 1 :=
        by { rw [localization.mk_mul, mul_comm, ←localization.mk_mul, localization.mk_self,
          mul_one], },
      rw ←hab',
      exact ideal.mul_mem_left J.as_ideal (localization.mk b 1) hab, },
    { use b, refl, }, },
end

/--
The canonical map from `set.Iic I` to `prime_spectrum (localization.at_prime I.as_ideal)`
is bijective (not necessary for the proof).
-/
lemma localization_prime_spectrum_map_is_bijective :
  function.bijective (localization_prime_spectrum_map I) := by
{ rw function.bijective_iff_has_inverse, exact ⟨localization_prime_spectrum_comap I,
  ⟨localization_prime_spectrum_comap_is_left_inverse I,
    localization_prime_spectrum_comap_is_right_inverse I⟩⟩, }

/--
The canonical map from `prime_spectrum (localization.at_prime I.as_ideal)` to `set.Iic I`
is bijective (not necessary for the proof).
-/
lemma localization_prime_spectrum_comap_is_bijective :
  function.bijective (localization_prime_spectrum_comap I) := by
{ rw function.bijective_iff_has_inverse, exact ⟨localization_prime_spectrum_map I,
  ⟨localization_prime_spectrum_comap_is_right_inverse I,
    localization_prime_spectrum_comap_is_left_inverse I⟩⟩, }

/--
The canonical map from `set.Iic I` to `prime_spectrum (localization.at_prime I.as_ideal)`
is monotone.
-/
lemma localization_prime_spectrum_map_is_monotone :
  monotone (localization_prime_spectrum_map I) :=
by { intros J1 J2 H, dsimp, intros x hx, rw mem_ideal_image_span'_iff at *,
  rcases hx with ⟨a, ⟨b, hab⟩⟩, use ⟨⟨a, H a.2⟩, ⟨b, hab⟩⟩, }

/--
The canonical map from `prime_spectrum (localization.at_prime I.as_ideal)` to `set.Iic I`
is monotone.
-/
lemma localization_prime_spectrum_comap_is_monotone :
  monotone (localization_prime_spectrum_comap I) :=
by { intros J1 J2 H x hx, dsimp at *, exact H hx, }

/--
We can regard the canonical map from `set.Iic I` to `prime_spectrum (localization.at_prime I.as_ideal)`
as an equivalence.
-/
--@[simp]
def localization_prime_spectrum_map_equiv :
  (set.Iic I) ≃ (prime_spectrum (localization.at_prime I.as_ideal)) :=
{ to_fun := localization_prime_spectrum_map I,
  inv_fun := localization_prime_spectrum_comap I,
  left_inv := localization_prime_spectrum_comap_is_left_inverse I,
  right_inv := localization_prime_spectrum_comap_is_right_inverse I }

/--
We can regard the canonical map from `prime_spectrum (localization.at_prime I.as_ideal)` to
`set.Iic I` as an equivalence.
-/
def localization_prime_spectrum_comap_equiv :
  (prime_spectrum (localization.at_prime I.as_ideal)) ≃ (set.Iic I) :=
{ to_fun := localization_prime_spectrum_comap I,
  inv_fun := localization_prime_spectrum_map I,
  left_inv := localization_prime_spectrum_comap_is_right_inverse I,
  right_inv := localization_prime_spectrum_comap_is_left_inverse I }

lemma localization_prime_spectrum_map_equiv_is_monotone :
  monotone (localization_prime_spectrum_map_equiv I) :=
by { change monotone (λ (I' : ↥(set.Iic I)), (localization_prime_spectrum_map I I')),
  exact localization_prime_spectrum_map_is_monotone I, }

lemma localization_prime_spectrum_comap_equiv_is_monotone :
  monotone (localization_prime_spectrum_comap_equiv I) :=
by { change monotone (λ I', localization_prime_spectrum_comap I I'),
  exact localization_prime_spectrum_comap_is_monotone I, }

lemma localization_prime_spectrum_comap_equiv_is_symm :
  localization_prime_spectrum_comap_equiv I =
    (localization_prime_spectrum_map_equiv I).symm := rfl

/--
We have a canonical order isomorphism from `set.Iic I` to
`prime_spectrum (localization.at_prime I.as_ideal`.
-/
@[simp]
def localization_prime_spectrum_map_order_iso :
  (set.Iic I) ≃o (prime_spectrum (localization.at_prime I.as_ideal)) :=
by { refine equiv.to_order_iso _ _ _,
     { exact localization_prime_spectrum_map_equiv I, },
     { exact localization_prime_spectrum_map_equiv_is_monotone I, },
     { rw ←localization_prime_spectrum_comap_equiv_is_symm I,
       exact localization_prime_spectrum_comap_equiv_is_monotone I, }, }

/--
The height of `I` is equal to the krull dimension of `localization.at_prime I.as_ideal`.
-/
theorem prime_ideal_height_eq_ring_krull_dim_of_localization :
  height I = ring_krull_dim (localization.at_prime I.as_ideal) := by
{ exact krull_dim_eq_of_order_iso (localization_prime_spectrum_map_order_iso I), }

end about_height_and_localization

end ring_krull_dim
