import .krull_dimension
import topology.subset_properties

noncomputable theory

/--
Krull dimension of a topological space is the supremum of length of chains of closed irreducible 
sets.
-/
def topological_krull_dim (T : Type*) [topological_space T] : ℕ±∞ :=
krull_dim { s : set T | is_closed s ∧ is_irreducible s }
