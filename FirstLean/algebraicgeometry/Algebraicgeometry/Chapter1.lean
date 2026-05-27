import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Basis
import Mathlib.RingTheory.Ideal.Span
--- Needed for Hilbert Basis Theorem
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Topology.Defs.Basic

noncomputable section

namespace algebraicGeometry
variable {K : Type*} [Field K]
variable {σ : Type*}

open Set
open Pointwise

--- Set of points that are zero for every multivariate function
--- over K in a given set of functions

--- Funcs says that AffineVariety takes in a set of MvPolynomials
--- Set (σ → K) says that Affine Variety will be compose of points in K^σ
def affineVariety (Funcs : Set (MvPolynomial σ K)): Set (σ → K) :=
    {x : σ → K | ∀ p ∈ Funcs, p.eval x = 0}


--- This theorem states that affine varieties are closed under intersections and in fact
--- the intersection of two affine varieties is the affine variety of their union
theorem closedUnderIntersection (Func₀ Func₁ : Set (MvPolynomial σ K)) :
    affineVariety Func₀ ∩ affineVariety Func₁ = affineVariety (Func₀ ∪ Func₁) := by
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
        apply h; exact Set.mem_union_left Func₁ hp --- Have x in the affine variety of the union so just need to prove p is in the union
      · intro p hp --- Analogous to above
        apply h; exact Set.mem_union_right Func₀ hp


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


theorem closedUnderUnion (Func₀ Func₁ : Set (MvPolynomial σ K)) :
  affineVariety Func₀ ∪ affineVariety Func₁ = affineVariety (Func₀ * Func₁) := by
  ext x --- Introduces the x for dual inclusion
  constructor --- Splits the inclusion
  · rintro (h₀ | h₁) --- Splits into either x ∈ affineVariety Func₀ or x ∈ affineVariety Func₁
    · intro p hp --- Introduces the polynomial we must show evaluates to 0 at x
      have proddef: ∃ f₀ ∈ Func₀, ∃ f₁ ∈ Func₁, f₀ * f₁ = p := by apply mem_mul.mp; apply hp --- Applies definition of product of two sets to extract concrete functions p can be written in terms of
      rcases proddef with ⟨a, ha, b, hb, c⟩ --- Extract the polynomials that p can be written as a product of
      have h' : (MvPolynomial.eval x) (a*b) = 0 := by
        rw [MvPolynomial.eval_mul]
        simp
        left
        apply h₀
        exact ha --- Have that the product of these polynomials evaluates to 0 using definition of polynomial multiplication
      subst c --- Substitute the product in for p
      exact h'
    · intro p hp --- This case is analogous to above
      have proddef: ∃ f₀ ∈ Func₀, ∃ f₁ ∈ Func₁, f₀ * f₁ = p := by apply mem_mul.mp; apply hp --- Applies definition of product of two sets to extract concrete functions p can be written in terms of
      rcases proddef with ⟨a, ha, b, hb, c⟩ --- Extract the polynomials that p can be written as a product of
      have h' : (MvPolynomial.eval x) (a*b) = 0 := by
        rw [MvPolynomial.eval_mul]
        simp
        right
        apply h₁
        exact hb --- Have that the product of these polynomials evaluates to 0 using definition of polynomial multiplication
      subst c --- Substitute the product in for p
      exact h'
  · intro h
    by_cases h' : x ∈ affineVariety Func₀ --- Split on whether x ∈ affineVariety Func₀ or not
    · left --- In the case it is then the conclusion is immediate
      exact h'
    · right --- Now consider the case where we don't have this membership
      by_contra h'' --- Will use contradiction so also assume x ∉ affineVariety Func₁
      --- The following gives us the existence of a function in Func₀ and one in Func₁ which
      --- doesn't evaluate to 0 at x using a contradiction
      have existf₀ : ∃ f₀ ∈ Func₀, (MvPolynomial.eval x) f₀ ≠ 0 := by
        by_contra hf₀
        apply h'
        push Not at hf₀
        exact hf₀
      have existf₁ : ∃ f₁ ∈ Func₁, (MvPolynomial.eval x) f₁ ≠ 0 := by
        by_contra hf₁
        apply h''
        push Not at hf₁
        exact hf₁
      --- Now extract these functions which don't evaluate to 0 at x
      rcases existf₀ with ⟨f₀, hypf₀, nonzerof₀⟩
      rcases existf₁ with ⟨f₁, hypf₁, nonzerof₁⟩
      --- The product of these function belongs to Func₀ * Func₁ by definition
      have membership : f₀ * f₁ ∈ Func₀ * Func₁ := by
        apply mem_mul.mpr
        use f₀
        constructor
        · exact hypf₀
        · use f₁
      --- This product doesn't evaluate to 0 as we're in a field
      have nonzero : (MvPolynomial.eval x) (f₀ * f₁) ≠ 0 := by
        rw [MvPolynomial.eval_mul]
        apply mul_ne_zero
        exact nonzerof₀; exact nonzerof₁
      --- But we also get it does evaluate to 0 as x ∈ affineVariety (Func₀ * Func₁)
      have zero : (MvPolynomial.eval x) (f₀ * f₁) = 0 := by
        apply h
        exact membership
      --- So we get our contradiction
      contradiction

theorem basisSameVariety (Func₀ Func₁ : Set (MvPolynomial σ K)) :
  Ideal.span Func₀ = Ideal.span Func₁ → affineVariety Func₀ = affineVariety Func₁ := by
  intro h
  ext x
  constructor
  · intro h'
    intro f hf
    have idealf : f ∈ Ideal.span Func₀ := by
      rw [h] --- Suffices to show p ∈ Ideal.span Func₁ by h
      exact Submodule.mem_span_of_mem hf --- An ideal is a submodule of the module of a ring over itself so can apply theorem about submodules
    have : ∀ f ∈ Ideal.span Func₀, (MvPolynomial.eval x) f = 0 := by
      intro g hg
      rw [Ideal.mem_span] at hg
      sorry
    · sorry
  · sorry


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
        rw [affineVariety, mem_setOf_eq]
        intro f hf
        rw [affineVariety] at LHS
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


end algebraicGeometry
