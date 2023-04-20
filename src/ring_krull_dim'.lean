import algebraic_geometry.prime_spectrum.basic
import algebra.module.localized_module

noncomputable theory

variables {R : Type*} [comm_ring R] (I : prime_spectrum R) (J : ideal R)

/--

`J' := J.map (algebra_map R (localization.at_prime I.as_ideal))`
ideal of `R_I`
not submodule of `R`

we need `J' →ₗ[R] J'` by `div s`
we can have `J' →ₗ[R_I] J'`
-/

@[simps] def map_from_ideal_to_ideal_image_span :
  J →ₗ[R] J.map (algebra_map R (localization.at_prime I.as_ideal)) :=
{ to_fun := λ x, ⟨localization.mk x 1, submodule.subset_span ⟨x, x.2, rfl⟩⟩,
  map_add' := by { intros x y, simp, rw ←@is_localization.mk'_add R _ I.as_ideal.prime_compl
    _ _ _ _ x y 1 1, simp, },
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

lemma localization_at_prime_div_by_range (I : prime_spectrum R)
  (J : ideal R)
  (s : I.as_ideal.prime_compl) :
  ∀ (x : localization.at_prime I.as_ideal),
    x ∈ ideal.map (algebra_map R (localization.at_prime I.as_ideal)) J →
    (localization_at_prime_div_by I s) x ∈
      ideal.map (algebra_map R (localization.at_prime I.as_ideal)) J :=
begin
  intros x hx, apply submodule.span_induction hx,
    { intros x hx, simp, rw ideal.map,
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

@[simps]
def module.End.inv {I : prime_spectrum R} (s : I.as_ideal.prime_compl) :
  module.End R (ideal.map (algebra_map R (localization.at_prime I.as_ideal)) J) :=
{ to_fun := (localization_at_prime_div_by _ s).restrict $ localization_at_prime_div_by_range I J s,
    map_add' := by sorry { intros, simp at *, },
    map_smul' := by sorry { intros, simp at *, }, }

example : true := ⟨⟩.

lemma module.End.inv_left {I : prime_spectrum R} (s : I.as_ideal.prime_compl) :
  algebra_map R (module.End R (ideal.map (algebra_map R (localization.at_prime I.as_ideal)) J)) s * 
  module.End.inv _ s = 1 :=
begin 
  --   ext1 ⟨x, hx⟩,
  --   rw [linear_map.mul_eq_comp, linear_map.comp_apply, module.End.inv_apply, 
  --     linear_map.restrict_apply, linear_map.one_apply],
  --   dsimp,
  --   refine submodule.span_induction hx _ _ _ _,
  -- { rintro _ ⟨y, hy, rfl⟩,
  --   ext1,
  --   change (s : R) • (_ * localization.mk y 1) = (localization.mk y 1),
  --   rw [algebra.smul_def, ← localization.mk_one_eq_algebra_map, localization.mk_mul,
  --     localization.mk_mul, one_mul, mul_one, one_mul, localization.mk_eq_mk',
  --     is_localization.eq],
  --   exact ⟨1, by simp only [submonoid.coe_one, one_mul, mul_one, mul_assoc]⟩, };
  sorry
end


lemma module.End.inv_right {I : prime_spectrum R} (s : I.as_ideal.prime_compl) :
  module.End.inv _ s * 
  algebra_map R (module.End R (ideal.map (algebra_map R (localization.at_prime I.as_ideal)) J)) s = 1 :=
begin
  -- ext1 ⟨x, hx⟩,
  -- rw [linear_map.mul_eq_comp, linear_map.comp_apply, module.End.inv_apply, 
  --   linear_map.restrict_apply, linear_map.one_apply],
  -- dsimp,
  -- refine submodule.span_induction hx _ _ _ _;
  sorry
end

lemma map_from_ideal_to_ideal_image_span_is_surj
  (y : ideal.map (algebra_map R (localization.at_prime I.as_ideal)) J) :
    ∃ (x : J × I.as_ideal.prime_compl),
      (x.snd : R) • y = map_from_ideal_to_ideal_image_span I J x.fst :=
begin
  admit,
end
--    begin
--      extract_goal,
--      rintros ⟨y, hy⟩,

-- --       y ∈ J' -> ∃ (a : J, b ∉ I), y = a / b

--     --  refine submodule.span_induction hy _ _ _ _;
--     --   y = j / 1 -> ∃ (a : J, b ∉ I), y = a / b true take a = j b = 1
--     --  y = 0 -> a = 0 b = 1
--     --   y₁ = a₁ / b₁ y₂ = a₂ / b₂ -> y₁ + y₂ = (a₁ • b₂ + a₂ • b₁) / (b₁ b₂)
--      sorry
--    end,

-- --     /-
-- --       x₁, x₂ ∈ J,
-- --       x₁ / 1 = x₂ / 1 ↔ ∃ (s ∉ I), s • x₁ = s * x₂

-- --       -- Integral domain
-- --       x₁ / 1 = x₂ / 1 ↔ x₁ = x₂
-- --       -- in general a / b = c / d ↔ ∃ (s ∉ I), s * (ad - bc) = 0
-- --     -/
lemma map_from_ideal_to_ideal_image_span_apply_eq_iff (x₁ x₂ : J) :
    (map_from_ideal_to_ideal_image_span I J) x₁ =
        (map_from_ideal_to_ideal_image_span I J) x₂ ↔
      ∃ (c : (I.as_ideal.prime_compl)), (c : R) • x₂ = (c : R) • x₁ :=
begin
  admit,
end

instance : is_localized_module I.as_ideal.prime_compl (map_from_ideal_to_ideal_image_span I J) :=
{ map_units := λ s, ⟨⟨_, module.End.inv _ s, module.End.inv_left _ s, module.End.inv_right _ s⟩, rfl⟩,
   surj := map_from_ideal_to_ideal_image_span_is_surj I J,
   eq_iff_exists := map_from_ideal_to_ideal_image_span_apply_eq_iff _ _ }

def map_from_localized_module_to_ideal_image_span :
  (localized_module I.as_ideal.prime_compl J) ≃ₗ[R]
  J.map (algebra_map R (localization.at_prime I.as_ideal)) :=
is_localized_module.iso _ $ map_from_ideal_to_ideal_image_span I J