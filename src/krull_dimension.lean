import ring_theory.ideal.basic
import ring_theory.localization.at_prime

noncomputable theory

variables (R : Type*) [comm_ring R]

/--

-/
structure prime_ideal_chain :=
(len : ℕ)
(chain : fin (len + 1) → ideal R)
(is_chain : strict_mono chain)
[is_prime : ∀ i, (chain i).is_prime]

namespace prime_ideal_chain

instance [nontrivial R] : nonempty (prime_ideal_chain R) :=
nonempty.intro
{ len := 0,
  chain := λ _, (ideal.exists_maximal R).some,
  is_chain := by { rintros ⟨i, (hi : i < 1)⟩ ⟨j, (hj : j < 1)⟩ (hij : i < j), exfalso, linarith, },
  is_prime := λ _, (ideal.exists_maximal R).some_spec.is_prime }

instance [nontrivial R] : inhabited (prime_ideal_chain R) :=
{ default :=
  { len := 0,
    chain := λ _, (ideal.exists_maximal R).some,
    is_chain := by { rintros ⟨i, (hi : i < 1)⟩ ⟨j, (hj : j < 1)⟩ (hij : i < j), exfalso, linarith, },
    is_prime := λ _, (ideal.exists_maximal R).some_spec.is_prime } }

@[ext]
lemma ext (M N : prime_ideal_chain R)
(len_eq : M.len = N.len)
(chain_eq : ∀ (i : fin (M.len + 1)), M.chain i = N.chain i) :
M = N :=
begin
cases M with h l m,
cases N with h' l' m',
dsimp at *,
subst len_eq,
congr,
ext,
rw chain_eq,
norm_num,
end

end prime_ideal_chain


class finite_dimensional_ring : Prop :=
(fin_dim : ∃ (M : prime_ideal_chain R), ∀ (N : prime_ideal_chain R), N.len ≤ M.len)

lemma finite_dimensional_ring.iff_len_bounded [nontrivial R] : 
  finite_dimensional_ring R ↔ 
  ∃ (n : ℕ), ∀ (N : prime_ideal_chain R), N.len ≤ n :=
{ mp := λ h, ⟨h.fin_dim.some.len, h.fin_dim.some_spec⟩,
  mpr := λ h, 
  { fin_dim := ⟨(@nat.Sup_mem (set.range (prime_ideal_chain.len : prime_ideal_chain R → ℕ))
      ⟨(default : prime_ideal_chain R).len, ⟨_, rfl⟩⟩ ⟨h.some, begin 
        rintros _ ⟨x, rfl⟩,
        exact h.some_spec _,
      end⟩).some, λ N, begin 
        classical,
        generalize_proofs H,
        rw H.some_spec,
        rw nat.Sup_def ⟨h.some, _⟩,
        swap,
        { rintros _ ⟨m, rfl⟩,
          refine h.some_spec _, },
        generalize_proofs H2,
        exact nat.find_spec H2 _ ⟨_, rfl⟩,
      end⟩ } }


variable [decidable $ finite_dimensional_ring R]

def krull_dim : ℕ := 
if H : finite_dimensional_ring R
then H.fin_dim.some.len
else 0

def maximal_chain [finite_dimensional_ring R] : prime_ideal_chain R :=
finite_dimensional_ring.fin_dim.some

lemma maximal_chain_is_maximal [finite_dimensional_ring R] (M : prime_ideal_chain R) :
  M.len ≤ (maximal_chain R).len :=
finite_dimensional_ring.fin_dim.some_spec M

def krull_dim_eq_len [finite_dimensional_ring R] : krull_dim R = (maximal_chain R).len :=
begin 
  dunfold krull_dim,
  split_ifs,
  refl,
end

def krull_dim_eq_zero (not_finite : ¬ finite_dimensional_ring R) : krull_dim R = 0 :=
begin 
  dunfold krull_dim,
  split_ifs,
  refl,
end

instance finite_dimensional_of_surj [finite_dimensional_ring R] 
  (S : Type*) [comm_ring S] [nontrivial S]
  (f : R →+* S) (hf : function.surjective f) : finite_dimensional_ring S :=
begin
  rw finite_dimensional_ring.iff_len_bounded,
  refine ⟨krull_dim R, _⟩,
  intros N,
  let N' : prime_ideal_chain R := 
  { len := N.len, 
    chain := λ j, (N.chain j).comap f, 
    is_chain := λ i j h, begin 
      dsimp,
      rw lt_iff_le_and_ne,
      split,
      { refine ideal.comap_mono _,
        refine le_of_lt (N.is_chain h), },
      { have neq := ne_of_lt (N.is_chain h),
        contrapose! neq,
        ext1 s,
        obtain ⟨r, rfl⟩:= hf s,
        rw [← ideal.mem_comap, neq, ideal.mem_comap], },
    end, 
    is_prime := λ j, begin 
      haveI := N.is_prime j,
      refine ideal.comap_is_prime _ _,
    end },
  rw [show N.len = N'.len, from rfl, krull_dim_eq_len],
  apply maximal_chain_is_maximal,
end


theorem all_chain_length_bounded [finite_dimensional_ring R] 
  (S : Type*) [comm_ring S] [nontrivial S]
  (f : R →+* S) (hf : function.surjective f) : ∀ (N : prime_ideal_chain S), N.len ≤ krull_dim R :=
begin
  intros N,
  let N' : prime_ideal_chain R := 
  { len := N.len,
    chain := λ j, (N.chain j).comap f,
    is_chain := λ i j h, begin 
      dsimp,
      rw lt_iff_le_and_ne,
      split,
      { refine ideal.comap_mono _,
        refine le_of_lt (N.is_chain h), },
      { have neq := ne_of_lt (N.is_chain h),
        contrapose! neq,
        ext1 s,
        obtain ⟨r, rfl⟩:= hf s,
        rw [← ideal.mem_comap, neq, ideal.mem_comap], },
    end,
    is_prime := λ j, begin
      haveI := N.is_prime j,
      refine ideal.comap_is_prime _ _,
    end },
  rw [show N.len = N'.len, from rfl, krull_dim_eq_len],
  apply maximal_chain_is_maximal,
end


open_locale classical

theorem krull_dim_bounded [finite_dimensional_ring R]
  (S : Type*) [comm_ring S] [ nontrivial S]
  (f : R →+* S) (hf : function.surjective f) : krull_dim S ≤ krull_dim R :=
begin
  haveI : finite_dimensional_ring S,
    exact finite_dimensional_of_surj R S f hf,
  rw krull_dim_eq_len,
  exact all_chain_length_bounded R S f hf (maximal_chain S),
end



section height

variables {R} 
variable [∀ (p : ideal R) [hp : p.is_prime], decidable $ finite_dimensional_ring (localization.at_prime p)]

def ideal.height (p : ideal R) [p.is_prime] : ℕ :=
krull_dim (localization.at_prime p)

example (p : ideal R) [p.is_prime] : ℕ := p.height

end height
