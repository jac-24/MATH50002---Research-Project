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
import Algebraicgeometry.FromTopToAlg

noncomputable section

namespace OtherTheorems
open FiniteGenSets
open ZariskiTop
open FromTopToAlg
open Pointwise
open Set

variable {K : Type*} [Field K]
variable {σ : Type*}


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
        

theorem closedUnderArbitraryIntersection (Func : σ → Set (MvPolynomial σ K)) :
  ⋂ i, (affineVariety (Func i)) = affineVariety (⋃ i, Func i) := by
  ext x
  constructor
  · intro h
    have in_every_set : ∀ i : σ, x ∈ affineVariety (Func i) := by
      rw [Set.mem_iInter] at h
      exact h
    intro p hp
    have in_some_set : ∃ j : σ, p ∈ Func j := by
      rw [Set.mem_iUnion] at hp
      exact hp
    rcases in_some_set with ⟨index, h_index⟩
    have in_index : x ∈ affineVariety (Func index) := by
      apply in_every_set
    apply in_index
    exact h_index
  · intro h
    rw [Set.mem_iInter]
    intro index p hp
    apply h
    rw [Set.mem_iUnion]
    use index


theorem vanishingIdealZariskiClosure (S : Set (σ → K)) :
  MvPolynomial.vanishingIdeal K (zariskiClosure S) = MvPolynomial.vanishingIdeal K S := by
  ext f --- Introduce the function in the ideal
  constructor
  · apply MvPolynomial.vanishingIdeal_anti_mono --- This direction is trivial as S ⊆ zariskiClosure S
    apply setContainedInVariety
  · intro h x hx
    have in_affine : S ⊆ affineVariety {f} := by --- f ∈ I(S) so vanishes at all points in S so by definition S ∈ V({f})
      intro y hy
      simp only [ZariskiTop.memAffineVariety, Set.mem_singleton_iff, forall_eq]
      apply h
      exact hy
    have zar_closure_contain : zariskiClosure S ≤ affineVariety {f} := by --- zariskiClosure S = V(I(S)), V({f})  = V(I(V({f}))) so apply anti-monotonicity twice
      rw [← zeroLocusOfVanAffineIsAffine, zariskiClosure]
      apply MvPolynomial.zeroLocus_anti_mono
      apply MvPolynomial.vanishingIdeal_anti_mono
      exact in_affine
    apply zar_closure_contain --- zariskiClosure S ≤ V({f}) so f will obviously vanish on zariskiClosure S
    apply hx
    simp only [Set.mem_singleton_iff]


--- This is essentially by definition using anti-monotonicity
theorem zariskiClosureSubset {S T : Set (σ → K)} :
  S ≤ T → zariskiClosure S ≤ zariskiClosure T := by
  intro h
  rw [zariskiClosure, zariskiClosure]
  apply MvPolynomial.zeroLocus_anti_mono
  apply MvPolynomial.vanishingIdeal_anti_mono
  exact h


theorem vanishingIdealIntersectionUnion (S T : Set (σ → K)) :
  MvPolynomial.vanishingIdeal K S ⊓ MvPolynomial.vanishingIdeal K T = MvPolynomial.vanishingIdeal K (S ∪ T) := by
  ext f
  constructor
  · intro h x hx
    simp only [Submodule.mem_inf, MvPolynomial.mem_vanishingIdeal_iff,
      MvPolynomial.aeval_eq_eval] at h --- f vanishes on both S and T as in the intersection of their zero loci
    rcases h with ⟨vanish_S, vanish_T⟩ --- As x ∈ S ∪ T this means that f will vanish at x, just split by whether in S or T
    by_cases inS : x ∈ S
    · apply vanish_S
      exact inS
    · simp only [Set.mem_union, inS, false_or] at hx
      apply vanish_T
      exact hx
  · intro h --- f vanishes on S ∪ T so will vanish on both S and T
    constructor
    · intro x hx
      apply h
      apply Set.mem_union_left
      exact hx
    · intro x hx
      apply h
      apply Set.mem_union_right
      exact hx


--- This is true by putting by just rewriting some of theorems have already proved
theorem zariskiClosureUnion (S T : Set (σ → K)) :
  zariskiClosure (S ∪ T) = zariskiClosure S ∪ zariskiClosure T := by
  rw [zariskiClosure, zariskiClosure, zariskiClosure]
  rw [← intersectionInsideGivesUnion]
  congr
  symm
  exact vanishingIdealIntersectionUnion S T


theorem intersectionInsideGivesUnion (I J : Ideal (MvPolynomial σ K)) :
  MvPolynomial.zeroLocus K (I ⊓ J) = MvPolynomial.zeroLocus K I ∪ MvPolynomial.zeroLocus K J := by
  ext x
  constructor
  · intro h
    have inter_le_product : MvPolynomial.zeroLocus K (I ⊓ J) ⊆ MvPolynomial.zeroLocus K (I * J) := by
      apply MvPolynomial.zeroLocus_anti_mono
      exact Ideal.mul_le_inf
    rw [productZeroLocus] at inter_le_product --- zeroLocus K (I * J) = zeroLocus K I ∪ zeroLocus K J from earlier theorem
    apply inter_le_product
    exact h
  · intro h p hp --- This is essentially trivial as p ∈ I ⊓ J so is p ∈ I ∧ p ∈ J, so will be 0 ∀ x ∈ zeroLocus K I, ∀ x ∈ zeroLocus K J
    simp only [Submodule.mem_inf] at hp
    rcases hp with ⟨p_inI, p_inJ⟩
    rcases h with inI | inJ
    · rw [MvPolynomial.mem_zeroLocus_iff] at inI
      apply inI
      exact p_inI
    · rw [MvPolynomial.mem_zeroLocus_iff] at inJ
      apply inJ
      exact p_inJ
