import algebraic_geometry.prime_spectrum.basic
import algebra.module.localized_module

noncomputable theory

variables {R : Type*} [comm_ring R] (I : prime_spectrum R) (J : ideal R)

@[reducible]
def ideal_image_span := J.map (algebra_map R (localization.at_prime I.as_ideal))

@[simps] def map_from_ideal_to_ideal_image_span :
  J →ₗ[R] ideal_image_span I J :=
{ to_fun := λ x, ⟨localization.mk x 1, submodule.subset_span ⟨x, x.2, rfl⟩⟩,
  map_add' := by { intros x y, simp, rw ←@is_localization.mk'_add R _ I.as_ideal.prime_compl
    _ _ _ _ x y 1 1, simp only [submonoid.coe_one, mul_one], },
  map_smul' := by { intros r x, rw ring_hom.id_apply, ext1, dsimp, rw localization.smul_mk,
    refl, }, }

@[simps] def localization_at_prime_div_by (s : I.as_ideal.prime_compl) :
  localization.at_prime I.as_ideal →ₗ[localization.at_prime I.as_ideal]
    localization.at_prime I.as_ideal :=
{ to_fun := λ x, (localization.mk 1 s) * x,
  map_add' := by { intros x y, exact mul_add (localization.mk 1 s) x y, },
  map_smul' := begin
      intros r x,
      rw [ring_hom.id_apply, mul_comm, mul_comm (localization.mk 1 s) x],
      have h : r • x * localization.mk 1 s = r * x * localization.mk 1 s,
        refl,
      have h' : r • (x * localization.mk 1 s) = r * (x * localization.mk 1 s),
        refl,
      rw [h, h', mul_assoc],
    end }

lemma localization_at_prime_div_by_range
  (s : I.as_ideal.prime_compl) :
  ∀ (x : localization.at_prime I.as_ideal),
    x ∈ ideal.map (algebra_map R (localization.at_prime I.as_ideal)) J →
  (localization_at_prime_div_by I s) x ∈
    ideal.map (algebra_map R (localization.at_prime I.as_ideal)) J :=
begin
  intros x hx, apply submodule.span_induction hx,
    { intros x hx, simp only [localization_at_prime_div_by_apply, localization.mk_eq_mk'],
      rw ideal.map,
      have h : x ∈ ideal.span (⇑(algebra_map R (localization.at_prime I.as_ideal)) '' ↑J),
        by { exact @ideal.subset_span (localization.at_prime I.as_ideal) _
          (⇑(algebra_map R (localization.at_prime I.as_ideal)) '' ↑J) x hx, },
      by { exact (ideal.mul_mem_left (ideal.span (⇑(algebra_map R (localization.at_prime I.as_ideal))
        '' ↑J))) (is_localization.mk' (localization I.as_ideal.prime_compl) 1 s) h, }, },
    { exact ideal.mul_mem_left (ideal.span (⇑(algebra_map R (localization.at_prime I.as_ideal))
        '' ↑J)) (localization.mk 1 s) (ideal.zero_mem (ideal.map (algebra_map R
          (localization.at_prime I.as_ideal)) J)), },
    { intros a b h1 h2, dsimp at *, rw mul_add, exact ideal.add_mem (ideal.map (algebra_map R
      (localization.at_prime I.as_ideal)) J) h1 h2, },
    { intros a b h, dsimp at *, rw [←mul_assoc, (mul_comm (localization.mk 1 s) a), mul_assoc],
      exact ideal.mul_mem_left (ideal.map (algebra_map R (localization.at_prime I.as_ideal)) J)
        a h, },
end

variables {I}

@[simps]
def module.End.inv (s : I.as_ideal.prime_compl) :
  module.End R (ideal.map (algebra_map R (localization.at_prime I.as_ideal)) J) :=
{ to_fun := (localization_at_prime_div_by _ s).restrict $
    localization_at_prime_div_by_range I J s,
  map_add' := by { intros, simp only [map_add] at *, },
  map_smul' := by { intros, simp only [linear_map.map_smul_of_tower, ring_hom.id_apply] at *, }, }

lemma module.End.inv_left (s : I.as_ideal.prime_compl) :
  (algebra_map R (module.End R (ideal.map (algebra_map R (localization.at_prime I.as_ideal)) J)) s)
  * module.End.inv J s = 1 :=
begin
  ext1 ⟨x, hx⟩,
  rw [linear_map.mul_eq_comp, linear_map.comp_apply, module.End.inv_apply,
    linear_map.restrict_apply, linear_map.one_apply],
  dsimp,
  refine submodule.span_induction' _ _ _ _ hx,
  { rintro _ ⟨y, hy, rfl⟩, ext1,
    change (s : R) • (_ * localization.mk y 1) = (localization.mk y 1),
    rw [algebra.smul_def, ←localization.mk_one_eq_algebra_map, localization.mk_mul,
      localization.mk_mul, one_mul, mul_one, one_mul, localization.mk_eq_mk', is_localization.eq],
    exact ⟨1, by simp only [submonoid.coe_one, one_mul, mul_one, mul_assoc]⟩, },
  { ext1, dsimp, simp only [mul_zero, smul_zero], },
  { intros a ha b hb iha ihb,
    have eq1 : (s : R) • (_ * _) + (s : R) • (_ * _) = a + b  :=
      subtype.ext_iff.mp (congr_arg2 (+) iha ihb),
    rw [←smul_add, ←mul_add] at eq1,
    ext1,
    exact eq1, },
  { intros d e he ihe,
    have eq1 : d • ((s : R) • (_ * _)) = d • e := subtype.ext_iff.mp (congr_arg (λ x, d • x) ihe),
    rw smul_comm at eq1,
    ext1,
    rw [subtype.coe_mk],
    conv_rhs { rw ←eq1 },
    dsimp,
    ring_nf, },
end

lemma module.End.inv_right (s : I.as_ideal.prime_compl) : module.End.inv _ s *
  algebra_map R (module.End R (ideal.map (algebra_map R (localization.at_prime I.as_ideal)) J)) s
    = 1 :=
begin
  ext1 ⟨x, hx⟩,
  rw [linear_map.mul_eq_comp, linear_map.comp_apply, module.End.inv_apply,
    linear_map.restrict_apply, linear_map.one_apply],
  dsimp,
  refine submodule.span_induction' _ _ _ _ hx,
  { intros a ha, ext1, simp_rw algebra.smul_def, simp only [localization.mk_eq_mk', subtype.coe_mk],
    have h : (algebra_map R (localization.at_prime I.as_ideal)) s = localization.mk s 1,
      refl,
    have h1 : is_localization.mk' (localization I.as_ideal.prime_compl) 1 s = localization.mk 1 s,
      simp only [localization.mk_eq_mk'],
    rw [h, ←mul_assoc, h1, localization.mk_mul, one_mul, mul_one, localization.mk_self], ring, },
  { simp only [smul_zero, mul_zero, subtype.mk_eq_mk], },
  { intros a ha b hb h1 h2, simp_rw [algebra.smul_def],
    have h : (algebra_map R (localization.at_prime I.as_ideal)) s = localization.mk s 1,
      refl,
    simp_rw [h, ←mul_assoc, localization.mk_mul, one_mul, mul_one, localization.mk_self, one_mul],
      refl, },
  { intros a b hb heq, simp_rw [algebra.smul_def],
    have h : (algebra_map R (localization.at_prime I.as_ideal)) s = localization.mk s 1,
      refl,
    simp_rw [h, ←mul_assoc, localization.mk_mul, one_mul, mul_one, localization.mk_self, one_mul], },
end

lemma map_from_ideal_to_ideal_image_span_is_surj
  (y : ideal.map (algebra_map R (localization.at_prime I.as_ideal)) J) :
    ∃ (x : J × I.as_ideal.prime_compl),
      (x.snd : R) • y = map_from_ideal_to_ideal_image_span I J x.fst :=
begin
  rcases y with ⟨y, hy⟩,
  refine submodule.span_induction' _ _ _ _ hy;
  clear hy y,
  { rintros _ ⟨y, hy, rfl⟩,
    refine ⟨⟨⟨y, hy⟩, 1⟩, _⟩,
    dsimp only,
    rw [submonoid.coe_one, one_smul],
    refl, },
  { refine ⟨⟨0, 1⟩, _⟩,
    dsimp only,
    rw [submonoid.coe_one, one_smul, map_zero],
    refl, },
  { rintros x hx y hy ⟨⟨mx, nx⟩, hmnx⟩ ⟨⟨my, ny⟩, hmny⟩,
    dsimp only at *,
    refine ⟨⟨(nx : R) • my + (ny : R) • mx, nx * ny⟩, _⟩,
    dsimp only,
    rw [map_add, linear_map.map_smul, ← hmny, linear_map.map_smul, ← hmnx],
    ext1,
    change ((nx : R) * (ny : R)) • (x + y) = (nx : R) • (ny : R) • y + (ny : R) • (nx : R) • x,
    rw [mul_smul, add_comm, smul_add, smul_add],
    congr' 1, rw smul_comm, },
  { rintros a x hx ⟨⟨c1, c2⟩, hc⟩,
    induction a using localization.induction_on,
    rcases a with ⟨d1, d2⟩,
    dsimp only at *,
    refine ⟨⟨⟨d1 * c1, _⟩, d2 * c2⟩, _⟩,
    { refine ideal.mul_mem_left J d1 _, exact set_like.coe_mem c1, },
    { dsimp at *, ext1,
      change (↑d2 * ↑c2 : R) • (localization.mk d1 d2 * x) = localization.mk (d1 * c1) _,
      rw show x = localization.mk c1 c2,
      { have eq1 := congr_arg ((*) (localization.mk 1 c2)) (subtype.ext_iff.mp hc),
        change localization.mk 1 c2 * (_ • x) = _ * localization.mk _ _ at eq1,
        rwa [algebra.smul_def, ←localization.mk_one_eq_algebra_map, ←mul_assoc, localization.mk_mul,
          localization.mk_mul, one_mul, mul_one, localization.mk_self, one_mul, one_mul] at eq1, },
      rw algebra.smul_def,
      change (localization.mk (↑d2 * ↑c2) 1) * ((localization.mk d1 d2) * (localization.mk c1 c2))
        = localization.mk (d1 * ↑c1) 1,
      simp only [localization.mk_mul, one_mul, mul_one],
      rw [localization.mk_eq_mk', is_localization.eq],
      refine ⟨1, _⟩,
      simp only [submonoid.coe_one, one_mul, mul_one, submonoid.coe_mul], }, },
end

lemma map_from_ideal_to_ideal_image_span_apply_eq_iff (x₁ x₂ : J) :
    (map_from_ideal_to_ideal_image_span I J) x₁ =
        (map_from_ideal_to_ideal_image_span I J) x₂ ↔
          ∃ (c : (I.as_ideal.prime_compl)), (c : R) • x₂ = (c : R) • x₁ :=
begin
  split,
  { intro h1,
    rw [map_from_ideal_to_ideal_image_span, linear_map.coe_mk, subtype.ext_iff, subtype.coe_mk,
      subtype.coe_mk, localization.mk_eq_mk_iff, localization.r_iff_exists] at h1,
    rcases h1 with ⟨c, hc⟩,
    exact ⟨c, by { ext, simpa using hc.symm }⟩, },
  { rintros ⟨c, hc⟩,
    rw [map_from_ideal_to_ideal_image_span, linear_map.coe_mk, subtype.ext_iff, subtype.coe_mk,
      subtype.coe_mk, localization.mk_eq_mk_iff, localization.r_iff_exists],
    rw subtype.ext_iff at hc,
    exact ⟨c, by simpa using hc.symm⟩, },
end

instance : is_localized_module I.as_ideal.prime_compl (map_from_ideal_to_ideal_image_span I J) :=
{ map_units := λ s, ⟨⟨_, module.End.inv _ s, module.End.inv_left _ s, module.End.inv_right _ s⟩, rfl⟩,
   surj := map_from_ideal_to_ideal_image_span_is_surj J,
   eq_iff_exists := map_from_ideal_to_ideal_image_span_apply_eq_iff _, }

variable (I)

def equiv_between_localized_module_and_ideal_image_span :
  (localized_module I.as_ideal.prime_compl J)
    ≃ₗ[R] ideal_image_span I J :=
  is_localized_module.iso _ $ map_from_ideal_to_ideal_image_span I J

lemma equiv_between_localized_module_and_ideal_image_span_apply
  (a : J) (b : I.as_ideal.prime_compl) :
    equiv_between_localized_module_and_ideal_image_span I J
      (localized_module.mk a b) = ⟨localization.mk a b, begin
          have h : localization.mk ↑a b = (localization.mk 1 b) * (localization.mk ↑a 1),
            rw [localization.mk_mul, one_mul, mul_one],
          have h1 : (localization.mk ↑a 1) ∈ ideal_image_span I J,
            change algebra_map R (localization.at_prime I.as_ideal) a ∈
              J.map (algebra_map R (localization.at_prime I.as_ideal)),
            exact ideal.apply_coe_mem_map (algebra_map R (localization.at_prime I.as_ideal)) J a,
          rw h,
          exact ideal.mul_mem_left (ideal_image_span I J) (localization.mk 1 b) h1,
        end⟩ :=
begin 
  rw [equiv_between_localized_module_and_ideal_image_span, is_localized_module.iso_apply_mk],
  generalize_proofs _ _ _ h1,
  apply_fun h1.unit,
  work_on_goal 2
  { rw function.injective_iff_has_left_inverse,
    refine ⟨h1.unit.inv, _⟩,
    intros x,
    change (h1.unit.inv * h1.unit.1) x = x,
    simp only [units.inv_eq_coe_inv, units.val_eq_coe, is_unit.unit_spec, is_unit.coe_inv_mul,
      linear_map.one_apply], },
  { change h1.unit.1 (h1.unit.inv _) = _ • _,
    rw [←linear_map.comp_apply, ←linear_map.mul_eq_comp, h1.unit.3, linear_map.one_apply,
      map_from_ideal_to_ideal_image_span, linear_map.coe_mk, linear_map.one_apply],
    ext1,
    change localization.mk _ _ = _ • localization.mk (a : R) b,
    rw [algebra.smul_def, ←localization.mk_one_eq_algebra_map, localization.mk_mul, one_mul,
      localization.mk_eq_mk_iff, localization.r_iff_exists],
    use 1,
    simp, },
end 

@[simps]
def ideal_image_span' : ideal (localization.at_prime I.as_ideal) :=
{ carrier := {x | ∃ (a : J) (b : I.as_ideal.prime_compl), x = localization.mk a b},
  add_mem' := begin
      rintros x y ⟨a1, ⟨b1, hx⟩⟩ ⟨a2, ⟨b2, hy⟩⟩,
      fconstructor,
      { exact ⟨(↑b1 * ↑a2) + (↑b2 * ↑a1), ideal.add_mem J (ideal.mul_mem_left J ↑b1
        (set_like.coe_mem a2)) (ideal.mul_mem_left J ↑b2 (set_like.coe_mem a1))⟩, },
      { use ↑b1 * ↑b2,
        exact submonoid.mul_mem I.as_ideal.prime_compl (set_like.coe_mem b1) (set_like.coe_mem b2),
        rw [hx, hy, localization.add_mk],
        refl, },
    end,
  zero_mem' := begin
      fconstructor, use 0, use 1,
      simp only [submodule.coe_zero, localization.mk_eq_mk', is_localization.mk'_zero],
    end,
  smul_mem' := begin
      refine localization.ind _,
      rintros ⟨c1, c2⟩ x ⟨j, ⟨a, ha⟩⟩,
      fconstructor,
      { use c1 * ↑j,
        exact ideal.mul_mem_left J c1 (set_like.coe_mem j), },
      { use c2 * a,
        change (localization.mk c1 c2) * x = localization.mk ↑(c1 * ↑j) (c2 * a),
        rw [ha, localization.mk_mul],
        refl, },
    end }

@[simp]
lemma mem_ideal_image_span'_iff (x : localization.at_prime I.as_ideal) :
  x ∈ ideal_image_span' I J ↔ ∃ (a : J) (b : I.as_ideal.prime_compl), x = localization.mk a b := 
    iff.rfl

@[simp]
lemma mem_ideal_image_span'_of_mem_ideal_image_span : ∀ (x : localization.at_prime I.as_ideal),
  x ∈ ideal_image_span I J → x ∈ ideal_image_span' I J :=
begin
  intros a ha,
  refine submodule.span_induction' _ _ _ _ ha,
  { intros x hx,
    rcases hx with ⟨y, ⟨hy1, hy2⟩⟩,
    change localization.mk y 1 = x at hy2,
    rw [←hy2, mem_ideal_image_span'_iff],
    use ⟨y, hy1⟩, use 1, refl, },
  { exact (ideal_image_span' I J).zero_mem, },
  { intros _ _ _ _ h1 h2, exact ideal.add_mem (ideal_image_span' I J) h1 h2, },
  { intros a b _ h1, exact submodule.smul_mem (ideal_image_span' I J) a h1, },
end

lemma ideal_image_span'_eq_ideal_image_span :
  ideal_image_span' I J = ideal_image_span I J :=
begin
  ext1 x,
  split,
  { rw mem_ideal_image_span'_iff,
    rintros ⟨⟨a, ha⟩, ⟨b, hb⟩⟩,
    change x = localization.mk a b at hb,
    rw [←one_mul a, ←mul_one b, ←localization.mk_mul] at hb,
    rw hb,
    exact ideal.mul_mem_left (ideal_image_span I J) (localization.mk 1 b)
      (ideal.mem_map_of_mem (algebra_map R (localization.at_prime I.as_ideal)) ha), },
  { apply mem_ideal_image_span'_of_mem_ideal_image_span, },
end

instance ideal_image_span'_is_prime (J : set.Iic I) :
  (ideal_image_span' I J.1.as_ideal).is_prime :=
{ ne_top' := begin
      intro hit,
      rw [ideal.eq_top_iff_one, ←localization.mk_one, mem_ideal_image_span'_iff] at hit,
      rcases hit with ⟨a, ⟨b, hb⟩⟩,
      have his : is_unit (@is_localization.mk' R _ (I.as_ideal.prime_compl)
        (localization.at_prime I.as_ideal) _ _ _ a b), begin
          simp only [localization.mk_eq_mk'] at hb,
          rw [←hb, is_localization.mk'_one],
          norm_num,
        end,
      rw is_localization.at_prime.is_unit_mk'_iff at his,
      exact his (J.2 a.2),
    end,
  mem_or_mem' := begin
      refine localization.ind _, rintros ⟨a1, a2⟩,
      refine localization.ind _, rintros ⟨b1, b2⟩,
      change (localization.mk a1 a2) * (localization.mk b1 b2)
        ∈ ideal_image_span' I J.val.as_ideal →
          localization.mk a1 a2 ∈ ideal_image_span' I J.val.as_ideal
            ∨ localization.mk b1 b2 ∈ ideal_image_span' I J.val.as_ideal,
      rw [localization.mk_mul, mem_ideal_image_span'_iff],
      rintros ⟨p, ⟨q, h⟩⟩,
      rw [localization.mk_eq_mk_iff, localization.r_iff_exists] at h,
      simp only [submonoid.coe_mul] at h, cases h with c hc,
      rw [←mul_assoc ↑c (↑a2 * ↑b2) ↑p] at hc,
      have h1 : ↑c * (↑q * (a1 * b1)) ∈ J.val.as_ideal := by { rw hc,
        exact ideal.mul_mem_left J.val.as_ideal (↑c * (↑a2 * ↑b2)) p.2, },
      rw ←mul_assoc ↑c ↑q (a1 * b1) at h1,
      have h2 : ↑c * ↑q ∉ J.val.as_ideal := by { intro h2',
        exact (submonoid.mul_mem I.as_ideal.prime_compl c.2 q.2) (J.2 h2'), },
      have h3 : a1 ∈ J.val.as_ideal ∨ b1 ∈ J.val.as_ideal := by
        { refine ideal.is_prime.mem_or_mem J.val.is_prime _,
          have h3' : ↑c * ↑q ∈ J.val.as_ideal ∨ a1 * b1 ∈ J.val.as_ideal,
            exact ideal.is_prime.mem_or_mem J.val.is_prime h1,
          rw or_iff_not_imp_left at h3',
          exact h3' h2, },
      cases h3 with h3l h3r,
      left, rw mem_ideal_image_span'_iff, use ⟨a1, h3l⟩, use a2, refl,
      right, rw mem_ideal_image_span'_iff, use ⟨b1, h3r⟩, use b2, refl,
    end }

/--
There is a canonical map from `set.Iic I` to `prime_spectrum (localization.at_prime I.as_ideal)`.
-/
def localization_prime_spectrum_map :
  (set.Iic I) → prime_spectrum (localization.at_prime I.as_ideal) :=
  λ I', ⟨ideal_image_span' I I'.1.as_ideal, infer_instance⟩

/--
There is a canonical map from `prime_spectrum (localization.at_prime I.as_ideal)` to `set.Iic I`.
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