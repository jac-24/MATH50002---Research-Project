import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Basis
import Mathlib.RingTheory.Ideal.Span
--- Needed for Hilbert Basis Theorem
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

noncomputable section

namespace AlgebraicGeometry
variable {K : Type*} [Field K]
variable {σ : Type*} [Fintype σ]


def affineVariety (Funcs : Set (MvPolynomial σ K)): Set (σ → K) :=
    {x : σ → K | ∀ p ∈ Funcs, p.eval x = 0}



theorem isAffineVariety (I : Ideal (MvPolynomial σ K)):
  ∃ funcs : Set (MvPolynomial σ K), funcs.Finite ∧ MvPolynomial.zeroLocus K I = affineVariety funcs := by
  have finitely_gen: I.FG := by --- Hilbert Basis theorem holds as MvPolynomial σ K a Noetherian ring
    apply isNoetherian_def.1
    apply MvPolynomial.isNoetherianRing
  --- Get the finite basis for the ideal as an ideal is a submodule of the module of the ring of MvPolynomial σ K
  --- over itself. Also, need indexing set σ to be finite
  have fin_basis : ∃ f : Set (MvPolynomial σ K), f.Finite ∧ Submodule.span (MvPolynomial σ K) f = I := by
    apply Submodule.fg_def.mp
    exact finitely_gen
  rcases fin_basis with ⟨f, fin, span⟩ --- Extract the finite basis
  use f
  constructor
  · exact fin
  · ext x
    constructor
    · intro h p hp --- Get MvPolynomial p that we need to evaluate to 0 at x
      apply h --- Suffices to show it is in the ideal as all functions in here are 0 at x
      subst span --- I = <f1,...,fs> so showing p in the ideal equivalent to showing it is in the set spanned by these fi
      apply Submodule.mem_span_of_mem --- p is actually a member of the generating set and this is by definition in the set spanned
      exact hp
    · intro h p hp
      subst span  --- I = <f1,...,fs>
      --- This gives us that p ∈ I = <f1,...,fs> means that it is a linear combination of these generators
      have in_span: ∃ (l : ↑f →₀ MvPolynomial σ K), (Finsupp.linearCombination (MvPolynomial σ K) Subtype.val) l = p := by
        apply (Finsupp.mem_span_iff_linearCombination (MvPolynomial σ K) (f) (p)).1
        exact hp
      rcases in_span with ⟨coeffs, is_lin_comb⟩ --- Extract the coefficients
      subst is_lin_comb
      have eval_zero : ∀ f' ∈ f, (MvPolynomial.eval x) f' = 0 := by
        intro f' hf'
        apply h; exact hf'
      rw [Finsupp.linearCombination_apply (MvPolynomial σ K) (coeffs)] --- Writes the linear combination as an actual linear combination
      simp only [Finsupp.sum, smul_eq_mul, map_sum, MvPolynomial.aeval_eq_eval, map_mul,
        Subtype.coe_prop, eval_zero, mul_zero, Finset.sum_const_zero]

end AlgebraicGeometry
