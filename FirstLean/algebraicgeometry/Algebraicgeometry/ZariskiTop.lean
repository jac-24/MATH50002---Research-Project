import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Basis
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Topology.Defs.Basic
import Algebraicgeometry.FormFundRes

noncomputable section

namespace ZariskiTop
open FiniteGenSets
open Set
open Pointwise

variable {K : Type*} [Field K]
variable {σ : Type*}


def isAffineVariety (V : Set (σ → K)) : Prop :=
  ∃ F : Set (MvPolynomial σ K), V = affineVariety F


theorem closedUnderUnion (F G : Set (MvPolynomial σ K)) :
  affineVariety F ∪ affineVariety G = affineVariety (F * G) := by
  ext x -- Introduces the x for dual inclusion
  constructor -- Splits the inclusion
  · rintro (h | h') -- Splits into either x ∈ affineVariety F or x ∈ affineVariety G
    · intro p hp -- Introduces the polynomial we must show evaluates to 0 at x
      rw [mem_mul] at hp
      rcases hp with ⟨f, hf, g, hg, prod_eq⟩ -- Applies definition of product of two sets to extract concrete functions p can be written in terms of
      subst prod_eq -- Substitute the product in for p
      simp only [map_mul, mul_eq_zero]
      left
      apply h
      exact hf
    · intro p hp -- This case is analogous to above
      rw [mem_mul] at hp
      rcases hp with ⟨f, hf, g, hg, prod_eq⟩
      subst prod_eq
      simp only [map_mul, mul_eq_zero]
      right
      apply h'
      exact hg
  · intro h
    by_cases h' : x ∈ affineVariety F -- Split on whether x ∈ affineVariety F or not
    · left -- In the case it is then the conclusion is immediate
      exact h'
    · right -- Now consider the case where we don't have this membership
      by_contra h'' -- Will use contradiction so also assume x ∉ affineVariety G
      -- The following gives us the existence of a function in F and one in G which
      -- doesn't evaluate to 0 at x
      rw [memAffineVariety] at h' h''
      push Not at h' h''
      -- Now extract these functions which don't evaluate to 0 at x
      rcases h' with ⟨f, hypf, non_zerof⟩
      rcases h'' with ⟨g, hypg, non_zerog⟩
      -- This product doesn't evaluate to 0 as we're in a field
      have non_zero : (MvPolynomial.eval x) (f * g) ≠ 0 := by
        rw [MvPolynomial.eval_mul]
        apply mul_ne_zero
        exact non_zerof; exact non_zerog
      -- But we also get it does evaluate to 0 as x ∈ affineVariety (F * G)
      have zero : (MvPolynomial.eval x) (f * g) = 0 := by
        apply h
        rw [mem_mul]
        use f
        constructor
        · exact hypf
        · use g
      -- So we get our contradiction
      contradiction


instance affineTopology : TopologicalSpace (σ → K) where
  IsOpen s := ∃ P : Set (MvPolynomial σ K), affineVariety P = sᶜ

  isOpen_univ := by
    use {1}
    rw [affineVariety]
    simp

  isOpen_inter := by
    intro s t hs ht
    obtain ⟨P1, h1⟩ := hs
    obtain ⟨P2, h2⟩ := ht
    use (P1 * P2)
    rw [← closedUnderUnion]
    rw [h1, h2]
    rw [compl_inter]

  isOpen_sUnion := by
    intro S hS
    use ⋃₀ {P | ∃ t ∈ S, affineVariety P = tᶜ}
    ext x
    constructor
    · intro LHS p
      obtain ⟨t', t'S, xt⟩ := p
      obtain ⟨P', hP'⟩ := hS t' t'S
      have x_in_compl : x ∈ t'ᶜ := by
        rw [← hP']
        intro f hf
        apply LHS
        exact ⟨P', ⟨t', t'S, hP'⟩, hf⟩
      apply x_in_compl
      exact xt
    · intro xsUnion p hp
      simp only [mem_compl_iff, mem_sUnion, not_exists, not_and] at xsUnion
      simp only [mem_sUnion, mem_setOf_eq] at hp
      obtain ⟨P', hP', hP''⟩ := hp
      rw [affineVariety] at hP'
      obtain ⟨t', ht'S, ht'⟩ := hP'
      have x_notin_t' : x ∈ t'ᶜ := by
        apply xsUnion t' ht'S
      rw [← ht'] at x_notin_t'
      apply x_notin_t'
      exact hP''


-- V(I(V)) = V where V is an affine variety
theorem zeroLocusOfVanAffineIsAffine (V : Set (σ → K)) (h : isAffineVariety V) :
  MvPolynomial.zeroLocus K (MvPolynomial.vanishingIdeal K V) = V := by
  rcases h with ⟨F, hF⟩
  subst hF
  apply le_antisymm
  · nth_rw 2 [← zeroLocusOfGenSetIsVariety F]
    apply MvPolynomial.zeroLocus_anti_mono
    intro p hp y hy
    apply inSpanAffineVarietyGenerators F hy
    exact hp
  · intro x hx p hp
    apply hp
    exact hx


-- Just apply the fact that V(I(V)) = V
theorem vanishingIdealOneToOne {V W : Set (σ → K)} (V_var : isAffineVariety V) (W_var : isAffineVariety W) :
  MvPolynomial.vanishingIdeal K (V) = MvPolynomial.vanishingIdeal K (W)
   → V = W := by
  intro h
  rw [← zeroLocusOfVanAffineIsAffine V V_var, ← zeroLocusOfVanAffineIsAffine W W_var]
  congr


theorem setContainedInVariety (S : Set (σ → K)) :
  S ≤ MvPolynomial.zeroLocus K (MvPolynomial.vanishingIdeal K S) := by
  intro x hx p hp
  apply hp
  exact hx


-- V(I(S)) is the smallest variety containing S
-- Need to include the fact that S ≤ V(I(S)) and that any other affine variety containing S contains V(I(S))
theorem smallestVariety {σ : Type*} [Fintype σ] (S : Set (σ → K)) :
  (∀ V : Set (σ → K), isAffineVariety V → S ≤ V → MvPolynomial.zeroLocus K (MvPolynomial.vanishingIdeal K S) ≤ V) ∧
  (S ≤ MvPolynomial.zeroLocus K (MvPolynomial.vanishingIdeal K S)) ∧
  (isAffineVariety (MvPolynomial.zeroLocus K (MvPolynomial.vanishingIdeal K S))) := by
  constructor
  · intro V is_aff S_subset
    rw [← zeroLocusOfVanAffineIsAffine V] -- V(I(V)) = V where V is affine variety
    apply MvPolynomial.zeroLocus_anti_mono
    apply MvPolynomial.vanishingIdeal_anti_mono
    apply S_subset
    exact is_aff
  · constructor
    · exact setContainedInVariety S
    · rcases idealGivesVariety (σ := σ) (I := (MvPolynomial.vanishingIdeal K S)) with ⟨F, finite, eq⟩
      use F


-- Zariski closure of a set S is V(I(S))
def zariskiClosure (S : Set (σ → K)) : Set (σ → K) :=
  MvPolynomial.zeroLocus K (MvPolynomial.vanishingIdeal K S)


end ZariskiTop
