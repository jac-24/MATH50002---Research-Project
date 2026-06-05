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


lemma inAffVarUnion {x : σ → K} (F : Set (MvPolynomial σ K)) (f : MvPolynomial σ K)
  (h : x ∈ affineVariety F) (h' : (MvPolynomial.eval x) f = 0) :
  x ∈ affineVariety (F ∪ {f}) := by
  intro p hp
  rcases hp with inF | isf --- p ∈ F ∪ {f} so is either in F or p = f, either way goes to zero at x
  · apply h
    exact inF
  · simp only [mem_singleton_iff] at isf
    symm at isf
    subst isf
    exact h'


lemma varietyEqualUnion (F : Set (MvPolynomial σ K)) (f g : MvPolynomial σ K)
  (h : f * g ∈ MvPolynomial.vanishingIdeal K (affineVariety F)) :
  affineVariety F = (affineVariety (F ∪ {f})) ∪ (affineVariety (F ∪ {g})) := by
  --- (f * g)(x) = 0 for x ∈ V(F) so must have f(x) = 0 ∨ g(x) = 0
  simp only [MvPolynomial.mem_vanishingIdeal_iff, MvPolynomial.aeval_eq_eval, map_mul, mul_eq_zero] at h
  ext x
  constructor
  · intro h'
    specialize h x h'
    rcases h with f_zero | g_zero --- Either f(x) = 0 or g(x) = 0 so will split by cases
    · left
      exact inAffVarUnion F f h' f_zero
    · right
      exact inAffVarUnion F g h' g_zero
  · intro h'
    rcases h' with inFf | inFg
    · intro p hp --- x ∈ affineVariety (F ∪ {f}) so any function in F will vanish at x
      apply inFf
      simp [hp]
    · intro p hp --- Analogous to above case
      apply inFg
      simp [hp]


@[simp]
lemma strictVanishingIdealAntiMono {F G : Set (MvPolynomial σ K)} :
  affineVariety G < affineVariety F → MvPolynomial.vanishingIdeal K (affineVariety F)
  < MvPolynomial.vanishingIdeal K (affineVariety G) := by
  intro h
  --- The definition of being a strict subset is that one set is contained in the other and
  --- the larger set has an element that is not in the smaller one
  simp only [Set.lt_eq_ssubset, Set.ssubset_iff_exists] at h
  rcases h with ⟨is_subset, y, in_varF, not_in_varG⟩ --- Extract the element in V(F) but not in V(G)
  simp only [SetLike.lt_iff_le_and_exists] --- Treat the ideal as a set (as proving an inclusion) and use definition already used above
  constructor
  · apply MvPolynomial.vanishingIdeal_anti_mono
    exact is_subset --- Use anti-monotonicity to prove the weak inequality
  · simp at not_in_varG --- y ∉ V(G) so there exists some f ∈ G that doesn't vanish at y
    rcases not_in_varG with ⟨f, f_inG, f_eval_nonzero⟩ --- Extract this f
    use f --- This will be the f ∈ I(V(G)) but not in I(V(F))
    constructor
    · intro x hx --- f ∈ I(V(G)) as f ∈ G so vanishes on V(G) by definition
      apply hx
      exact f_inG
    · simp --- To show f ∉ I(V(F)) need to show there is some x ∈ V(F) that f doesn't vanish on
      use y --- y ∈ V(F) but by definition f(y) ≠ 0 so we're done
      constructor
      · exact in_varF
      · exact f_eval_nonzero


lemma equalityVanishingIdeal {F G H : Set (MvPolynomial σ K)}
  (h : affineVariety F = affineVariety G ∪ affineVariety H) (h' : affineVariety F ≠ affineVariety G)
  (h'' : (MvPolynomial.vanishingIdeal K (affineVariety F)).IsPrime) :
  MvPolynomial.vanishingIdeal K (affineVariety F) = MvPolynomial.vanishingIdeal K (affineVariety H) := by
  apply le_antisymm
  · apply MvPolynomial.vanishingIdeal_anti_mono --- By anti-monotonicity as V(H) ≤ V(F) (as V(F) = V(G) ∪ V(H)) we're done
    simp [h]
  · intro g hg
    have strict_ineq : MvPolynomial.vanishingIdeal K (affineVariety F) < MvPolynomial.vanishingIdeal K (affineVariety G) := by
      apply strictVanishingIdealAntiMono --- Just need to show V(G) < V(F) using the anti-monotonicity result
      apply Set.ssubset_iff_subset_ne.2 --- This strict inequality results from V(G) ≤ V(F) by the union, and V(F) ≠ V(G) by another hypothesis
      constructor
      · simp [h]
      · symm at h'
        exact h'
    --- An equivalent definition for one set (here ideals are treated as sets) being included in another is that
    --- there exists an element in one but not the other and we have a weak inequality between the sets
    rw [SetLike.lt_iff_le_and_exists] at strict_ineq
    rcases strict_ineq with ⟨is_subset, f, inG, not_inF⟩ --- Extract the function f ∉ I(V(F)) with f ∈ I(V(G))
    have in_van_ideal_F : (f * g) ∈ MvPolynomial.vanishingIdeal K (affineVariety F) := by
      intro y hy
      simp only [MvPolynomial.aeval_eq_eval, map_mul, mul_eq_zero] --- Need to show either f(y) = 0 or g(y) = 0
      rw [MvPolynomial.mem_vanishingIdeal_iff] at hg
      rw [MvPolynomial.mem_vanishingIdeal_iff] at inG
      rw [h] at hy --- y ∈ V(G) ∪ V(H)
      rcases hy with a | b --- Either y ∈ V(G) or y ∈ V(H)
      · left --- Either way product will vanish as either f or g will vanish at y
        apply inG
        exact a
      · right
        apply hg
        exact b
    have prime : f ∈ MvPolynomial.vanishingIdeal K (affineVariety F) ∨ g ∈ MvPolynomial.vanishingIdeal K (affineVariety F) := by
      rw [Ideal.isPrime_iff] at h'' --- Apply definition of prime ideal to get that either f or g is in I(V(F))
      rcases h'' with ⟨not_top, product⟩ --- Get I(V(F)) ≠ ⊤ and the either f or g is in I(V(F)) which is what we really want
      apply product
      exact in_van_ideal_F
    simp only [not_inF, false_or] at prime --- Cannot have f ∈ I(V(F)) as f is chosen such that f ∉ I(V(F))
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


--- How to include non-emptiness of V(F) as this is required for I(V(F)) to be proper
theorem irreduciblePrimeIdeal (F : Set (MvPolynomial σ K)):
  isIrreducible F ↔ (MvPolynomial.vanishingIdeal K (affineVariety F)).IsPrime := by
  constructor
  · intro h
    rw [Ideal.isPrime_iff]
    constructor
    · apply vanishingIdealNotTopIff.mpr --- Need to show I(V(F)) is proper in this part so need V(F) ≠ ∅
      exact h.2
    · intro f g hfg
      --- This is the right union to apply irreducibility to
      --- Have either of these equalities as V(F) equal to the union of these varieties so can use irreducibility
      have eq_union : affineVariety F = affineVariety (F ∪ {f}) ∨ affineVariety F = affineVariety (F ∪ {g}) := by
        apply h.1
        exact varietyEqualUnion F f g hfg
      rcases eq_union with with_f | with_g --- Either V(F) = V(F ∪ {f}) or V(F) = V(F ∪ {g})
      · left
        intro x hx
        simp only [with_f, union_singleton, FiniteGenSets.memAffineVariety, mem_insert_iff,
          forall_eq_or_imp] at hx --- x ∈ V(F) = V(F ∪ {f}) so f vanishes at x as required
        simp only [MvPolynomial.aeval_eq_eval, hx]
      · right --- Analogous to the above
        intro x hx
        simp only [with_g, union_singleton, FiniteGenSets.memAffineVariety, mem_insert_iff,
          forall_eq_or_imp] at hx
        simp only [MvPolynomial.aeval_eq_eval, hx]
  · intro h
    constructor
    · intro G H h' --- Introduce the affine varieties V(F) is equal to a union of
      by_cases in_affvar_G : affineVariety F = affineVariety G
      · simp [in_affvar_G] --- We are immediately done if V(F) = V(G)
      · right --- Want to show V(F) = V(H) as know V(F) ≠ V(G)
        apply vanishingIdealOneToOne --- Suffices to show I(V(F)) = I(V(H)) as I one-to-one on varieties
        exact equalityVanishingIdeal h' in_affvar_G h
      --- Also need to show that V(F) ≠ ∅
    · rw [Ideal.isPrime_iff] at h
      apply vanishingIdealNotTopIff.mp
      exact h.1


end FromTopToAlg
