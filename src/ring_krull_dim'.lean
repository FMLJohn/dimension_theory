import algebraic_geometry.prime_spectrum.basic
import algebra.module.localized_module
import krull_dimension'

noncomputable theory

variables {R : Type*} [comm_ring R] (I : prime_spectrum R) (J : ideal R)

@[reducible] def ideal_image_span := J.map (algebra_map R (localization.at_prime I.as_ideal))

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
    rcases hx with ⟨a, ⟨b, hab⟩⟩,
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
is bijective.
-/
lemma localization_prime_spectrum_map_is_bijective :
  function.bijective (localization_prime_spectrum_map I) := by
{ rw function.bijective_iff_has_inverse, exact ⟨localization_prime_spectrum_comap I,
  ⟨localization_prime_spectrum_comap_is_left_inverse I,
    localization_prime_spectrum_comap_is_right_inverse I⟩⟩, }

/--
The canonical map from `prime_spectrum (localization.at_prime I.as_ideal)` to `set.Iic I`
is bijective.
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
@[simp]
def localization_prime_spectrum_map_equiv :
  (set.Iic I) ≃ (prime_spectrum (localization.at_prime I.as_ideal)) :=
begin
  fconstructor,
  { exact localization_prime_spectrum_map I, },
  { exact localization_prime_spectrum_comap I, },
  { exact localization_prime_spectrum_comap_is_left_inverse I, },
  { exact localization_prime_spectrum_comap_is_right_inverse I, },
end

/--
We can regard the canonical map from `prime_spectrum (localization.at_prime I.as_ideal)` to
`set.Iic I` as an equivalence.
-/
@[simp]
def localization_prime_spectrum_comap_equiv :
  (prime_spectrum (localization.at_prime I.as_ideal)) ≃ (set.Iic I) :=
begin
  fconstructor,
  { exact localization_prime_spectrum_comap I, },
  { exact localization_prime_spectrum_map I, },
  { exact localization_prime_spectrum_comap_is_right_inverse I, },
  { exact localization_prime_spectrum_comap_is_left_inverse I, },
end

/--
`localization_prime_spectrum_map_equiv I` is monotone.
-/
lemma localization_prime_spectrum_map_equiv_is_monotone :
  monotone (localization_prime_spectrum_map_equiv I) :=
by { change monotone (λ (I' : ↥(set.Iic I)), (localization_prime_spectrum_map I I')),
  exact localization_prime_spectrum_map_is_monotone I, }

/--
`localization_prime_spectrum_comap_equiv I` is monotone.
-/
lemma localization_prime_spectrum_comap_equiv_is_monotone :
  monotone (localization_prime_spectrum_comap_equiv I) :=
by { change monotone (λ I', localization_prime_spectrum_comap I I'),
  exact localization_prime_spectrum_comap_is_monotone I, }

lemma localization_prime_spectrum_comap_equiv_is_symm :
  localization_prime_spectrum_comap_equiv I =
    (localization_prime_spectrum_map_equiv I).symm :=
by { fconstructor, }

/--
We have a canonical order isomorphism from `set.Iic I` to
`prime_spectrum (localization.at_prime I.as_ideal`.
-/
@[simp]
def localization_prime_spectrum_map_order_iso :
  (set.Iic I) ≃o (prime_spectrum (localization.at_prime I.as_ideal)) :=
begin
  refine equiv.to_order_iso _ _ _,
  { exact localization_prime_spectrum_map_equiv I, },
  { exact localization_prime_spectrum_map_equiv_is_monotone I, },
  { rw ←localization_prime_spectrum_comap_equiv_is_symm I,
    exact localization_prime_spectrum_comap_equiv_is_monotone I, },
end

/--
The height of `I` is equal to the krull dimension of `localization.at_prime I.as_ideal`.
-/
theorem prime_ideal_height_eq_ring_krull_dim_of_localization :
  height I = ring_krull_dim (localization.at_prime I.as_ideal) := by
{ exact krull_dim_eq_of_order_iso (localization_prime_spectrum_map_order_iso I), }