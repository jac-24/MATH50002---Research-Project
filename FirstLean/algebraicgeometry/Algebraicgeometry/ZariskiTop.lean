import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Basis
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.Ideal.Quotient.Basic
--- Needed for Hilbert Basis Theorem
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


@[simp]
theorem memAffineVariety {F : Set (MvPolynomial σ K)} {x : σ → K} :
  x ∈ affineVariety F ↔ ∀ p ∈ F, (MvPolynomial.eval x) p = 0 := by
  rfl


@[simp]
theorem notInZeroLocus {x : σ → K} {I : Ideal (MvPolynomial σ K)} :
  x ∉ MvPolynomial.zeroLocus K I ↔ ∃ f ∈ I, (MvPolynomial.eval x) f ≠ 0 := by
  contrapose!
  exact MvPolynomial.mem_zeroLocus_iff


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


theorem closedUnderUnion (F G : Set (MvPolynomial σ K)) :
  affineVariety F ∪ affineVariety G = affineVariety (F * G) := by
  ext x --- Introduces the x for dual inclusion
  constructor --- Splits the inclusion
  · rintro (h | h') --- Splits into either x ∈ affineVariety F or x ∈ affineVariety G
    · intro p hp --- Introduces the polynomial we must show evaluates to 0 at x
      rw [mem_mul] at hp
      rcases hp with ⟨f, hf, g, hg, prod_eq⟩ --- Applies definition of product of two sets to extract concrete functions p can be written in terms of
      subst prod_eq --- Substitute the product in for p
      simp only [map_mul, mul_eq_zero]
      left
      apply h
      exact hf
    · intro p hp --- This case is analogous to above
      rw [mem_mul] at hp
      rcases hp with ⟨f, hf, g, hg, prod_eq⟩
      subst prod_eq
      simp only [map_mul, mul_eq_zero]
      right
      apply h'
      exact hg
  · intro h
    by_cases h' : x ∈ affineVariety F --- Split on whether x ∈ affineVariety F or not
    · left --- In the case it is then the conclusion is immediate
      exact h'
    · right --- Now consider the case where we don't have this membership
      by_contra h'' --- Will use contradiction so also assume x ∉ affineVariety G
      --- The following gives us the existence of a function in F and one in G which
      --- doesn't evaluate to 0 at x
      rw [memAffineVariety] at h' h''
      push Not at h' h''
      --- Now extract these functions which don't evaluate to 0 at x
      rcases h' with ⟨f, hypf, non_zerof⟩
      rcases h'' with ⟨g, hypg, non_zerog⟩
      --- This product doesn't evaluate to 0 as we're in a field
      have non_zero : (MvPolynomial.eval x) (f * g) ≠ 0 := by
        rw [MvPolynomial.eval_mul]
        apply mul_ne_zero
        exact non_zerof; exact non_zerog
      --- But we also get it does evaluate to 0 as x ∈ affineVariety (F * G)
      have zero : (MvPolynomial.eval x) (f * g) = 0 := by
        apply h
        rw [mem_mul]
        use f
        constructor
        · exact hypf
        · use g
      --- So we get our contradiction
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


--- This is essentially true because of Hilbert's Basis Theorem
@[simp]
theorem zeroLocusOfVanishingIsVariety {σ : Type*} [Fintype σ] {S : Set (σ → K)} :
  ∃ F : Set (MvPolynomial σ K), F.Finite ∧ MvPolynomial.zeroLocus K (MvPolynomial.vanishingIdeal K S) = affineVariety F := by
  exact isAffineVariety (MvPolynomial.vanishingIdeal K S)


--- V(I(V(F))) = V(F)
theorem zeroLocusOfVanAffineIsAffine (F : Set (MvPolynomial σ K)) :
  MvPolynomial.zeroLocus K (MvPolynomial.vanishingIdeal K (affineVariety F)) = affineVariety F := by
  apply le_antisymm
  · nth_rw 2 [← zeroLocusOfGenSetIsVariety F]
    apply MvPolynomial.zeroLocus_anti_mono
    intro p hp y hy
    apply inSpanAffineVarietyGenerators F hy
    exact hp
  · intro x hx p hp
    apply hp
    exact hx


--- Just apply the fact that V(I(V(F))) = V(F)
theorem vanishingIdealOneToOne {F G : Set (MvPolynomial σ K)} :
  MvPolynomial.vanishingIdeal K (affineVariety F) = MvPolynomial.vanishingIdeal K (affineVariety G)
   → affineVariety F = affineVariety G := by
  intro h
  rw [← zeroLocusOfVanAffineIsAffine F, ← zeroLocusOfVanAffineIsAffine G]
  congr


theorem setContainedInVariety (S : Set (σ → K)) :
  S ≤ MvPolynomial.zeroLocus K (MvPolynomial.vanishingIdeal K S) := by
  intro x hx p hp
  apply hp
  exact hx


--- V(I(S)) is the smallest variety containing S
--- Need to include the fact that S ≤ V(I(S)) and that any other affine variety containing S contains V(I(S))
theorem smallestVariety {σ : Type*} [Fintype σ] (S : Set (σ → K)) :
  (∀ F : Set (MvPolynomial σ  K), S ⊆ affineVariety F → MvPolynomial.zeroLocus K (MvPolynomial.vanishingIdeal K S) ⊆ affineVariety F) ∧
  (S ⊆ MvPolynomial.zeroLocus K (MvPolynomial.vanishingIdeal K S)) ∧
  (∃ G : Set (MvPolynomial σ K), MvPolynomial.zeroLocus K (MvPolynomial.vanishingIdeal K S) = affineVariety G) := by
  constructor
  · intro F s_contain
    rw [← zeroLocusOfVanAffineIsAffine F] --- V(I(V(F))) = F where V(F) is affine variety on F not zero locus
    apply MvPolynomial.zeroLocus_anti_mono
    apply MvPolynomial.vanishingIdeal_anti_mono
    exact s_contain
  · constructor
    · exact setContainedInVariety S
    · rcases isAffineVariety (σ := σ) (I := (MvPolynomial.vanishingIdeal K S)) with ⟨F, finite, eq⟩
      use F


--- Zariski closure of a set S is V(I(S))
def zariskiClosure (S : Set (σ → K)) : Set (σ → K) :=
  MvPolynomial.zeroLocus K (MvPolynomial.vanishingIdeal K S)


def zariskiDense (F : Set (MvPolynomial σ K)) (S : Set (σ → K)) : Prop :=
  (S ≤ affineVariety F) ∧ (zariskiClosure S = affineVariety F)


def isIrreducible (F : Set (MvPolynomial σ K)) : Prop :=
  (∀ G H : Set (MvPolynomial σ K),
  affineVariety F = affineVariety G ∪ affineVariety H → (affineVariety F = affineVariety G ∨
  affineVariety F = affineVariety H)) ∧ (affineVariety F ≠ ∅)






-- Chapter 4 §4 Prop 7 ii)
theorem varietyZariskiUnion [Fintype σ] {F G : Set (MvPolynomial σ K)} :
  affineVariety F = (affineVariety F ∩ affineVariety G)
          ∪ zariskiClosure (affineVariety F \ affineVariety G) := by
  apply Set.Subset.antisymm
  · have h₀: (affineVariety F) \ (affineVariety G)
        ⊆ zariskiClosure (affineVariety F \ affineVariety G) := by
        rw [zariskiClosure]
        apply setContainedInVariety
    conv_lhs =>
      rw [← inter_union_diff (affineVariety F) (affineVariety G)]
    gcongr

  · apply union_subset
    · exact inter_subset_left
    · rw [zariskiClosure]
      -- apply Prop 1
      have h₁: (affineVariety F) \ (affineVariety G) ⊆ affineVariety F := by
        simp

      apply (smallestVariety (affineVariety F \ affineVariety G)).left
      exact h₁



-- Chapter 4 §4 Prop 7 iii)
theorem zariskiClosureSubsetOfIdeal [Fintype σ] {I J : Ideal (MvPolynomial σ K)} :
  zariskiClosure (affineVariety I \ affineVariety J) ≤ MvPolynomial.zeroLocus K (I.colon J) := by
  have h: I.colon J ≤ MvPolynomial.vanishingIdeal K
          (MvPolynomial.zeroLocus K I \ MvPolynomial.zeroLocus K J) := by
    intro f hf a ha

    -- a is in V(I), since a is in V(I) \ V(J)
    have h₁: a ∈ MvPolynomial.zeroLocus K I := by
      exact mem_of_mem_inter_left ha

    -- therefore, for all g in J, f(a)g(a) = 0
    have h₂ : ∀ g ∈ J, MvPolynomial.eval a f * MvPolynomial.eval a g = 0 := by
      intro g hg

      -- disclaimer, hfg and h_eval were written by AI, I was very stuck
      -- f * g is in I
      have hfg : f * g ∈ I := by
        apply hf
        exact mem_leftCoset f hg
      -- f (a) * g (a) = 0
      have h_eval := by
        apply h₁ (f * g)
        apply hfg

      rw [map_mul] at h_eval
      exact h_eval

    -- there exists a g such that g(a) ≠ 0
    have h₃ : ∃ g ∈ J, MvPolynomial.eval a g ≠ 0 := by
      apply notInZeroLocus.mp
      exact notMem_of_mem_diff ha

    -- AI code alert sorry I was very tired
    -- however, (f a) * (g a) = 0 for all f. therefore, (f a) must equal 0 for all f
    rcases h₃ with ⟨g, hg, hg_ne_zero⟩
    have h_mul := h₂ g hg
    cases mul_eq_zero.mp h_mul with
    | inl hf_zero =>
      rw [MvPolynomial.aeval_def]
      exact hf_zero
    | inr hg_zero =>
      exact False.elim (hg_ne_zero hg_zero)




  sorry







end ZariskiTop


--- Some alternative formalizations
-- theorem sumZeroLocus (I J : Ideal (MvPolynomial σ K)) :
--   MvPolynomial.zeroLocus K (I + J) = MvPolynomial.zeroLocus K I ∩ MvPolynomial.zeroLocus K J := by
--     ext x
--     constructor
--     · intro h
--       constructor
--       · intro p hp --- p is the polynomial we need to evaluate to 0
--         apply h
--         apply Ideal.mem_sup_left --- Have that p ∈ I implies p ∈ I + J
--         exact hp --- So as all polynomials in I + J vanish at x we are done
--       · intro p hp --- Analogous to the above
--         apply h
--         apply Ideal.mem_sup_right
--         exact hp
--     · intro h p hp --- p is the polynomial we need to evaluate to 0
--       have is_sum : ∃ f ∈ I, ∃ g ∈ J, f + g = p := by
--         simp only [ add_eq_sup] at hp --- I + J = I ⊔ J, this is how the sum is represented in Mathlib, as supremum of the ideals
--         apply Submodule.mem_sup.mp --- By definition if an element is in the sum of ideals it can be written as a sum of two elements, each one in one of the ideals
--         exact hp
--       simp only [Set.mem_inter_iff, MvPolynomial.mem_zeroLocus_iff, MvPolynomial.aeval_eq_eval] at h --- Unpacks the defintion of x being in the set given by h
--       rcases is_sum with ⟨f, hf, g, hg, f_g_sum⟩ --- Get the MvPolynomials that p can be written as a sum of
--       subst f_g_sum --- Substitute them in
--       simp only [MvPolynomial.aeval_eq_eval, map_add]
--       simp [h, hf, hg]


-- theorem inProductIsZero {x : σ → K} {I J : Ideal (MvPolynomial σ K)}
--   (h : ∀ f ∈ I, ∀ g ∈ J, (MvPolynomial.eval x) (f * g) = 0) :
--   ∀ p ∈ I * J, (MvPolynomial.eval x) p = 0 := by
--   intro p hp
--   refine Submodule.mul_induction_on (R := MvPolynomial σ K) (C := fun f : MvPolynomial σ K => (MvPolynomial.eval x) f = 0) hp ?_ ?_
--   · exact h --- Need to show that any product m * n where m ∈ I, n ∈ J evaluates to 0 at x as I * J consists of finite sums of these products
--   · intro a b ha hb --- Need to show that adding two functions that are 0 at x gives a function that is 0 at x
--     simp only [map_add, ha, hb, add_zero]


-- theorem productZeroLocus (I J : Ideal (MvPolynomial σ K)) :
--   MvPolynomial.zeroLocus K (I * J) = MvPolynomial.zeroLocus K I ∪ MvPolynomial.zeroLocus K J := by
--   ext x
--   constructor
--   · intro h
--     have product_zero : ∀ f ∈ I, ∀ g ∈ J, (MvPolynomial.eval x) (f * g) = 0 := by --- This is essentially trivial as f * g ∈ I * J, ∀ f ∈ I, ∀ g ∈ J
--         intro f hf g hg
--         apply h
--         apply Ideal.mul_mem_mul --- f * g ∈ I * J
--         exact hf
--         exact hg
--     by_cases h' : x ∈ MvPolynomial.zeroLocus K I --- Split into cases as easier to get use contradiction like this
--     · left
--       exact h'
--     · right
--       by_contra h'' --- Suppose for contradiction that we also have x ∉ MvPolynomial.zeroLocus K J
--       have get_contra : ¬(∀ f ∈ I, ∀ g ∈ J, (MvPolynomial.eval x) (f * g) = 0) := by --- Write statement like this so contradiction tactic works
--         push Not
--         rw [ notInZeroLocus] at h' h''
--         rcases h' with ⟨f, inI, hf⟩
--         rcases h'' with ⟨g, inJ, hg⟩
--         use f --- Verifying that f * g does not evaluate to 0 at x
--         constructor
--         · exact inI
--         · use g
--           constructor
--           · exact inJ
--           · simp only [ map_mul]
--             simp [hf, hg]
--       contradiction
--   · intro h p hp
--     rcases h with inI | inJ
--     --- Looks the same as in the previous part part but true for a different reason, x ∈ MvPolynomial.zeroLocus K I, so
--     --- any product including a function in I will evaluate to 0 at x
--     · have product_zero : ∀ f ∈ I, ∀ g ∈ J, (MvPolynomial.eval x) (f * g) = 0 := by
--         intro f hf g hg
--         simp only [map_mul, mul_eq_zero]
--         left
--         apply inI
--         exact hf
--       apply inProductIsZero product_zero --- As any element in I * J is a finite sum of product i * j, i ∈ I, j ∈ J we're done
--       exact hp
--     --- Analogous to above
--     · have product_zero : ∀ f ∈ I, ∀ g ∈ J, (MvPolynomial.eval x) (f * g) = 0 := by
--         intro f hf g hg
--         simp only [map_mul, mul_eq_zero]
--         right
--         apply inJ
--         exact hg
--       apply inProductIsZero product_zero
--       exact hp


-- theorem zeroLocusOfVanAffineIsAffine (F : Set (MvPolynomial σ K)) :
--   MvPolynomial.zeroLocus K (MvPolynomial.vanishingIdeal K (affineVariety F)) = affineVariety F := by
--   ext x
--   constructor
--   · intro h
--     --- Basically if f ∈ <f1,...,fs> then it will vanish at any point where all these generators vanish
--     have gen_set_inclusion : Ideal.span F ≤ MvPolynomial.vanishingIdeal K (affineVariety F) := by
--       intro p hp y hy
--       apply inSpanAffineVarietyGenerators F hy
--       exact hp
--     --- Use anti-monotonicity of zero loci
--     have affine_variety_reversed :
--     MvPolynomial.zeroLocus K (MvPolynomial.vanishingIdeal K (affineVariety F)) ≤ MvPolynomial.zeroLocus K (Ideal.span F) := by
--       apply MvPolynomial.zeroLocus_anti_mono
--       exact gen_set_inclusion
--     rw [zeroLocusOfGenSetIsVariety F] at affine_variety_reversed --- Go from V(<f1,...,fs>) to V(f1,...,fs) as they are equal
--     apply affine_variety_reversed
--     exact h
--   · intro h p hp
--     apply hp
--     exact h
