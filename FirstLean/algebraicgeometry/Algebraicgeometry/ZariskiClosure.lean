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

namespace algebraicGeometryZariski
variable {K : Type*} [Field K]
variable {σ : Type*} [Fintype σ]


def affineVariety (Funcs : Set (MvPolynomial σ K)): Set (σ → K) :=
    {x : σ → K | ∀ p ∈ Funcs, p.eval x = 0}



omit [Fintype σ]
theorem notInZeroLocus {x : σ → K} {I : Ideal (MvPolynomial σ K)} :
  x ∉ MvPolynomial.zeroLocus K I ↔ ∃ f ∈ I, (MvPolynomial.eval x) f ≠ 0 := by
  contrapose!
  exact MvPolynomial.mem_zeroLocus_iff


#check mt inZeroLocus.1


omit [Fintype σ] --- Don't need a finite index set for the variables in the polynomial
theorem sumZeroLocus (I J : Ideal (MvPolynomial σ K)) :
  MvPolynomial.zeroLocus K (I + J) = MvPolynomial.zeroLocus K I ∩ MvPolynomial.zeroLocus K J := by
    ext x
    constructor
    · intro h
      constructor
      · intro p hp --- p is the polynomial we need to evaluate to 0
        apply h
        apply Ideal.mem_sup_left --- Have that p ∈ I implies p ∈ I + J
        exact hp --- So as all polynomials in I + J vanish at x we are done
      · intro p hp --- Analogous to the above
        apply h
        apply Ideal.mem_sup_right
        exact hp
    · intro h p hp --- p is the polynomial we need to evaluate to 0
      have is_sum : ∃ f ∈ I, ∃ g ∈ J, f + g = p := by
        simp only [add_eq_sup] at hp --- I + J = I ⊔ J, this is how the sum is represented in Mathlib, as supremum of the ideals
        apply Submodule.mem_sup.mp --- By definition if an element is in the sum of ideals it can be written as a sum of two elements, each one in one of the ideals
        exact hp
      simp only [Set.mem_inter_iff, MvPolynomial.mem_zeroLocus_iff, MvPolynomial.aeval_eq_eval] at h --- Unpacks the defintion of x being in the set given by h
      rcases is_sum with ⟨f, hf, g, hg, f_g_sum⟩ --- Get the MvPolynomials that p can be written as a sum of
      subst f_g_sum --- Substitute them in
      simp only [MvPolynomial.aeval_eq_eval, map_add]
      simp [h, hf, hg]

theorem productZeroLocus (I J : Ideal (MvPolynomial σ K)) :
  MvPolynomial.zeroLocus K (I * J) = MvPolynomial.zeroLocus K I ∪ MvPolynomial.zeroLocus K J := by
  ext x
  constructor
  · intro h
    have product_zero : ∀ f ∈ I, ∀ g ∈ J, (MvPolynomial.eval x) (f * g) = 0 := by --- This is essentially trivial as f * g ∈ I * J, ∀ f ∈ I, ∀ g ∈ J
        intro f hf g hg
        apply h
        apply Ideal.mul_mem_mul --- f * g ∈ I * J
        exact hf
        exact hg
    by_cases h' : x ∈ MvPolynomial.zeroLocus K I --- Split into cases as easier to get use contradiction like this
    · left
      exact h'
    · right
      by_contra h'' --- Suppose for contradiction that we also have x ∉ MvPolynomial.zeroLocus K J
      have get_contra : ¬(∀ f ∈ I, ∀ g ∈ J, (MvPolynomial.eval x) (f * g) = 0) := by --- Write statement like this so contradiction tactic works
        push Not
        rw [notInZeroLocus] at h' h''
        rcases h' with ⟨f, inI, hf⟩
        rcases h'' with ⟨g, inJ, hg⟩
        use f --- Verifying that f * g does not evaluate to 0 at x
        constructor
        · exact inI
        · use g
          constructor
          · exact inJ
          · simp only [map_mul]
            simp [hf, hg]
      contradiction
  · intro h p hp
    rcases h with inI | inJ
    --- Looks the same as in the previous part part but true for a different reason, x ∈ MvPolynomial.zeroLocus K I, so
    --- any product including a function in I will evaluate to 0 at x
    · have product_zero : ∀ f ∈ I, ∀ g ∈ J, (MvPolynomial.eval x) (f * g) = 0 := by
        intro f hf g hg
        simp only [map_mul, mul_eq_zero]
        left
        apply inI
        exact hf
      #check Submodule.mul_induction_on
      sorry
    sorry

      -- have h' : p ∈ I * J := by exact hp
      -- rw [ Submodule.mul_eq_span_mul_set] at hp
      -- have : ∃ (l : I*J →₀ MvPolynomial σ K), (Finsupp.linearCombination (MvPolynomial σ K) Subtype.val) l = p := by
      --   apply (Finsupp.mem_span_iff_linearCombination (MvPolynomial σ K) (I*J) (p)).1
      --   simp only [Submodule.span_coe_eq_restrictScalars, Submodule.restrictScalars_self]
      --   exact h'
      -- rcases this with ⟨a, b⟩
      -- subst b
      -- rw [ Finsupp.linearCombination_apply]
      -- simp [ Finsupp.sum]


#check Submodule.mul_induction_on










end algebraicGeometryZariski
