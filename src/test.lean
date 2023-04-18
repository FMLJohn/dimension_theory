import linear_algebra.contraction
import group_theory.order_of_element
import linear_algebra.bilinear_form
import linear_algebra.quadratic_form.basic

lemma _root_.quadratic_form.pos_def.sum_induction {k V ι : Type*} [finite ι] [nonempty ι] [fintype ι]
  [linear_ordered_field k] [add_comm_group V] [module k V] (q : ι → quadratic_form k V)
  (hq : ∀ i, (q i).pos_def) :
  (finset.univ.sum q).pos_def :=
begin
  -- use `finset.sum_induction_nonempty`?
  refine finset.sum_induction_nonempty _ _ _ finset.univ_nonempty (λ _ _, hq _),
  sorry,
end
