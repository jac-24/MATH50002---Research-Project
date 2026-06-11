import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Basis
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Ideal.Prime
--- Needed for Hilbert Basis Theorem
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Algebraicgeometry.FormFundRes
import Algebraicgeometry.ZariskiTop

noncomputable section

namespace FromTopToAlg
open ZariskiTop
open FiniteGenSets
open Pointwise
open Set

variable {K : Type*} [Field K]
variable {σ : Type*}


theorem idealGeneratesItself (I : Ideal (MvPolynomial σ K)) :
  Ideal.span I = I := by
  simp only [Submodule.span_coe_eq_restrictScalars, Submodule.restrictScalars_self]


--- This theorem states that affine varieties are closed under intersections and in fact
--- the intersection of two affine varieties is the affine variety of their union
theorem closedUnderIntersection (F G : Set (MvPolynomial σ K)) :
    affineVariety F ∩ affineVariety G = affineVariety (F ∪ G) := by
    ext x --- Introduces the x for the subset inclusion
    constructor --- Splits the goal
    · intro h --- Introduces the hypothesis that x is in the LHS of the inclusion
      rcases h with ⟨h₀, h₁⟩ --- Gives us that either x is is the first AV or the second (or both)
      intro p hp --- Introduces the p in the union of the sets of functions that we need to evaluate to 0 at x
      rcases hp with a | b --- Gives us that either p ∈ Func₀ or p ∈ Func₁
      · apply h₀; exact a
      · apply h₁; exact b
    · intro h --- Introduces the hypothesis that x is in the RHS of the inclusion
      constructor --- Need to prove x is in the intersection so this splits the goal
      · intro p hp --- Introduces the function we want to evaluate to 0
        apply h; exact Set.mem_union_left G hp --- Have x in the affine variety of the union so just need to prove p is in the union
      · intro p hp --- Analogous to above
        apply h; exact Set.mem_union_right F hp


theorem sumZeroLocus (I J : Ideal (MvPolynomial σ K)) :
  MvPolynomial.zeroLocus K (I + J) = MvPolynomial.zeroLocus K I ∩ MvPolynomial.zeroLocus K J := by
  rw [Submodule.add_eq_sup] --- I + J = I ⊔ J in Lean
  nth_rw 1 [← idealGeneratesItself I, ← idealGeneratesItself J] --- Replace all instances of I and J by <I> and <J>
  rw [← Ideal.span_union]
  rw [zeroLocusOfGenSetIsVariety]
  symm
  apply closedUnderIntersection


theorem productZeroLocus (I J : Ideal (MvPolynomial σ K)) :
  MvPolynomial.zeroLocus K (I * J) = MvPolynomial.zeroLocus K I ∪ MvPolynomial.zeroLocus K J := by
  rw [Submodule.mul_def]
  rw [← idealGeneratesItself I, ← idealGeneratesItself J]
  rw [zeroLocusOfGenSetIsVariety, zeroLocusOfGenSetIsVariety, zeroLocusOfGenSetIsVariety]
  simp only [Submodule.span_coe_eq_restrictScalars, Submodule.restrictScalars_self,
    closedUnderUnion]


lemma inAffVarUnion {x : σ → K} (V: Set (σ → K)) (f : MvPolynomial σ K)
  (V_var : isAffineVariety V) (h : x ∈ V) (h' : (MvPolynomial.eval x) f = 0) :
  x ∈ V ∩ affineVariety {f} := by
  rcases V_var with ⟨F, hF⟩ --- Extract the set V is defined to be the set of zeroes of
  subst hF
  rw [closedUnderIntersection] --- V(F) ∩ V({f}) = V(F ∪ {f})
  intro p hp
  rcases hp with inF | isf --- p ∈ F ∪ {f} so is either in F or p = f, either way goes to zero at x
  · apply h
    exact inF
  · simp only [mem_singleton_iff] at isf
    symm at isf
    subst isf
    exact h'


lemma varietyEqualUnion {V : Set (σ → K)} {f g : MvPolynomial σ K}
  (V_var : isAffineVariety V) (h : f * g ∈ MvPolynomial.vanishingIdeal K V) :
  V = (V ∩ affineVariety {f}) ∪ (V ∩ affineVariety {g}) := by
  --- (f * g)(x) = 0 for x ∈ V(F) so must have f(x) = 0 ∨ g(x) = 0
  simp only [MvPolynomial.mem_vanishingIdeal_iff, MvPolynomial.aeval_eq_eval, map_mul, mul_eq_zero] at h
  ext x
  constructor
  · intro h'
    specialize h x h'
    rcases h with f_zero | g_zero --- Either f(x) = 0 or g(x) = 0 so will split by cases
    · left
      exact inAffVarUnion V f V_var h' f_zero
    · right
      exact inAffVarUnion V g V_var h' g_zero
  · intro h'
    rcases h' with inFf | inFg
    · rw [Set.mem_inter_iff x V (affineVariety {f})] at inFf --- x ∈ V ∩ affineVariety {f} so is clearly in V
      simp [inFf]
    · rw [Set.mem_inter_iff x V (affineVariety {g})] at inFg --- Analogous to above
      simp [inFg]


@[simp]
lemma strictVanishingIdealAntiMono {V W : Set (σ → K)} {V_var : isAffineVariety V} {W_var : isAffineVariety W} :
  W < V → MvPolynomial.vanishingIdeal K V
  < MvPolynomial.vanishingIdeal K W := by
  intro h
  simp only [Set.lt_eq_ssubset, Set.ssubset_iff_exists] at h
  rcases h with ⟨is_subset, y, in_V, notin_W⟩
  simp only [SetLike.lt_iff_le_and_exists]
  constructor
  · apply MvPolynomial.vanishingIdeal_anti_mono
    exact is_subset
  · rcases V_var with ⟨F, hF⟩; rcases W_var with ⟨G, hG⟩ --- V = V(F), W = V(G) as are affine varieties
    subst hF hG
    simp at notin_W --- y ∉ V(G) so there exists some f ∈ G that doesn't vanish at y
    rcases notin_W with ⟨f, f_inG, f_eval_nonzero⟩ --- Extract this f
    use f --- This will be the f ∈ I(V(G)) but not in I(V(F))
    constructor
    · intro x hx --- f ∈ I(V(G)) as f ∈ G so vanishes on V(G) by definition
      apply hx
      exact f_inG
    · simp --- To show f ∉ I(V(F)) need to show there is some x ∈ V(F) that f doesn't vanish on
      use y --- y ∈ V(F) but by definition f(y) ≠ 0 so we're done
      constructor
      · exact in_V
      · exact f_eval_nonzero



lemma equalityVanishingIdeal {V U W : Set (σ → K)} {V_var : isAffineVariety V}
  {U_var : isAffineVariety U} {W_var : isAffineVariety W}
  (h : V = U ∪ W) (h' : V ≠ U) (h'' : (MvPolynomial.vanishingIdeal K V).IsPrime) :
  MvPolynomial.vanishingIdeal K V = MvPolynomial.vanishingIdeal K W := by
  apply le_antisymm
  · apply MvPolynomial.vanishingIdeal_anti_mono --- By anti-monotonicity as W ≤ V (as V = U ∪ W) we're done
    simp [h]
  · intro g hg
    have strict_ineq : MvPolynomial.vanishingIdeal K V < MvPolynomial.vanishingIdeal K U := by
      apply strictVanishingIdealAntiMono (V_var := V_var) (W_var := U_var)
      simp only [lt_eq_ssubset]
      rw [Set.ssubset_iff_subset_ne]
      constructor
      · simp [h]
      · symm at h'
        exact h'
    --- An equivalent definition for one set (here ideals are treated as sets) being included in another is that
    --- there exists an element in one but not the other and we have a weak inequality between the sets
    rw [SetLike.lt_iff_le_and_exists] at strict_ineq
    rcases strict_ineq with ⟨is_subset, f, inG, not_inF⟩ --- Extract the function f ∉ I(V) with f ∈ I(U)
    have in_van_ideal_F : (f * g) ∈ MvPolynomial.vanishingIdeal K V := by
      intro x hx
      simp only [MvPolynomial.aeval_eq_eval, map_mul, mul_eq_zero] --- Need to show either f(x) = 0 or g(x) = 0
      rw [MvPolynomial.mem_vanishingIdeal_iff] at hg
      rw [MvPolynomial.mem_vanishingIdeal_iff] at inG
      rw [h] at hx --- x ∈ U ∪ W
      rcases hx with a | b --- Either x ∈ U or x ∈ W
      · left --- Either way product will vanish as either f or g will vanish at x
        apply inG
        exact a
      · right
        apply hg
        exact b
    have prime : f ∈ MvPolynomial.vanishingIdeal K V ∨ g ∈ MvPolynomial.vanishingIdeal K V := by
      rw [Ideal.isPrime_iff] at h'' --- Apply definition of prime ideal to get that either f or g is in I(V)
      rcases h'' with ⟨not_top, product⟩ --- Get I(V) ≠ ⊤ and that either f or g is in I(V) which is what we really want
      apply product
      exact in_van_ideal_F
    simp only [not_inF, false_or] at prime --- Cannot have f ∈ I(V) as f is chosen such that f ∉ I(V)
    exact prime


lemma vanishingIdealNotTopIff {S : Set (σ → K)} :
  MvPolynomial.vanishingIdeal K S ≠ ⊤ ↔ S ≠ ∅ := by
  constructor
  · contrapose
    intro h
    simp [h, MvPolynomial.vanishingIdeal_empty]
  · intro h
    symm at h
    rw [← Set.nonempty_iff_empty_ne, Set.nonempty_def] at h --- A set is non-empty if it contains an element
    rcases h with ⟨x, hx⟩
    intro h'
    have ex_not_zero : ∃ f : MvPolynomial σ K, (MvPolynomial.eval x) f ≠ 0 := by
      use 1 --- The constant function 1 is non-zero for all elements of σ → K
      simp
    rcases ex_not_zero with ⟨f, not_zero⟩
    apply not_zero
    have in_van_ideal : f ∈ MvPolynomial.vanishingIdeal K S := by --- f vanishes at x as the whole space does by assumption
      rw [h']
      simp
    apply in_van_ideal
    exact hx


lemma interIsAffine {V : Set (σ → K)} {f : MvPolynomial σ K} (V_var : isAffineVariety V) :
  isAffineVariety (V ∩ affineVariety {f}) := by
  rcases V_var with ⟨F, hF⟩ --- Get the set V is defined on
  subst hF
  use F ∪ {f} --- This the right set to use by an earlier proposition
  exact closedUnderIntersection F {f}


theorem irreduciblePrimeIdeal (V : Set (σ → K)) (V_var : isAffineVariety V):
  isIrreducible V ↔ (MvPolynomial.vanishingIdeal K V).IsPrime := by
  constructor
  · intro h
    rw [Ideal.isPrime_iff]
    constructor
    · apply vanishingIdealNotTopIff.mpr --- Need to show I(V) is proper in this part so need V ≠ ∅
      exact h.2.2
    · intro f g hfg
      --- This is the right union to apply irreducibility to
      --- Have either of these equalities as V equal to the union of these varieties so can use irreducibility
      have : (V = V ∩ affineVariety {f}) ∨ (V = V ∩ affineVariety {g}) := by
        apply h.2.1 --- Use the union property of irreducibility as V is equal to this union
        apply interIsAffine V_var --- The intersection is an affine variety as both sets are affine varieties
        apply interIsAffine V_var
        apply varietyEqualUnion V_var hfg --- V equal to the union by a previous lemma
      rcases this with with_f | with_g --- Split on which member of the union V is equal to
      · left
        rw [with_f]
        simp
      · right
        rw [with_g]
        simp
  · intro h
    constructor
    · exact V_var
    constructor
    · intro U W U_var W_var eq_union --- Introduce the affine varieties V is equal to the union of
      by_cases h' : V = U
      · simp [h']
      · push Not at h'
        right
        apply vanishingIdealOneToOne V_var W_var --- Suffices to prove the vanishing ideals are equal
        apply equalityVanishingIdeal eq_union h' h --- Can just use a previous lemma as all hypotheses are satisfied
        apply V_var; apply U_var; apply W_var
    · rw [Ideal.isPrime_iff] at h
      apply vanishingIdealNotTopIff.mp
      exact h.1


end FromTopToAlg
