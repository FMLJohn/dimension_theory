import ring_theory.artinian

section is_artinian_ring

variables {R : Type*} [comm_ring R] [is_artinian_ring R] 
variables (p : ideal R) [ideal.is_prime p]

instance ideal.is_prime.is_maximal_of_is_artinian_ring : p.is_maximal :=
ideal.quotient.maximal_of_is_field _ 
{ exists_pair_ne := ⟨0, 1, zero_ne_one⟩,
  mul_comm := mul_comm,
  mul_inv_cancel := λ x hx, begin 
    haveI ins1 : is_artinian_ring (R ⧸ p) := (@ideal.quotient.mk_surjective R _ p).is_artinian_ring,
    obtain ⟨n, hn⟩ : ∃ (n : ℕ), ideal.span {x^n} = ideal.span {x^(n+1)},
    { obtain ⟨n, h⟩ := @@is_artinian.monotone_stabilizes _ _ _ ins1 
        ⟨λ m, order_dual.to_dual (ideal.span {x^m}), λ m n h y hy, begin 
          dsimp [order_dual.to_dual] at *, 
          rw [ideal.mem_span_singleton] at hy ⊢,
          obtain ⟨z, rfl⟩ := hy,
          exact dvd_mul_of_dvd_left (pow_dvd_pow _ h) _,
        end⟩,
      specialize h (n + 1) (by norm_num),
      dsimp at h,
      exact ⟨n, h⟩, },
    have H : x^n ∈ ideal.span {x^(n+1)},
    { rw ← hn, refine submodule.subset_span (set.mem_singleton _), },
    rw ideal.mem_span_singleton at H,
    obtain ⟨y, hy⟩ := H,
    rw [pow_add, mul_assoc, pow_one] at hy,
    conv_lhs at hy { rw [←mul_one (x^n)] },
    exact ⟨y, mul_left_cancel₀ (pow_ne_zero _ hx) hy.symm⟩,
  end }

end is_artinian_ring