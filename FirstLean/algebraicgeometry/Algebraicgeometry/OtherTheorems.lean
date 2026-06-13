import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Basis
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Ideal.Prime
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


@[simp]
theorem notInZeroLocus {x : σ → K} {I : Ideal (MvPolynomial σ K)} :
  x ∉ MvPolynomial.zeroLocus K I ↔ ∃ f ∈ I, (MvPolynomial.eval x) f ≠ 0 := by
  contrapose!
  exact MvPolynomial.mem_zeroLocus_iff


-- This theorem states that affine varieties are closed under intersections and in fact
-- the intersection of two affine varieties is the affine variety of their union
theorem closedUnderIntersection (F G : Set (MvPolynomial σ K)) :
    affineVariety F ∩ affineVariety G = affineVariety (F ∪ G) := by
    ext x -- Introduces the x for the subset inclusion
    constructor -- Splits the goal
    · intro h -- Introduces the hypothesis that x is in the LHS of the inclusion
      rcases h with ⟨h₀, h₁⟩ -- Gives us that either x is is the first AV or the second (or both)
      intro p hp -- Introduces the p in the union of the sets of functions that we need to evaluate to 0 at x
      rcases hp with a | b -- Gives us that either p ∈ Func₀ or p ∈ Func₁
      · apply h₀; exact a
      · apply h₁; exact b
    · intro h -- Introduces the hypothesis that x is in the RHS of the inclusion
      constructor -- Need to prove x is in the intersection so this splits the goal
      · intro p hp -- Introduces the function we want to evaluate to 0
        apply h; exact Set.mem_union_left G hp -- Have x in the affine variety of the union so just need to prove p is in the union
      · intro p hp -- Analogous to above
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


-- This is essentially by definition using anti-monotonicity
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
      MvPolynomial.aeval_eq_eval] at h -- f vanishes on both S and T as in the intersection of their zero loci
    rcases h with ⟨vanish_S, vanish_T⟩ -- As x ∈ S ∪ T this means that f will vanish at x, just split by whether in S or T
    by_cases inS : x ∈ S
    · apply vanish_S
      exact inS
    · simp only [Set.mem_union, inS, false_or] at hx
      apply vanish_T
      exact hx
  · intro h -- f vanishes on S ∪ T so will vanish on both S and T
    constructor
    · intro x hx
      apply h
      apply Set.mem_union_left
      exact hx
    · intro x hx
      apply h
      apply Set.mem_union_right
      exact hx


theorem intersectionInsideGivesUnion (I J : Ideal (MvPolynomial σ K)) :
  MvPolynomial.zeroLocus K (I ⊓ J) = MvPolynomial.zeroLocus K I ∪ MvPolynomial.zeroLocus K J := by
  ext x
  constructor
  · intro h
    have inter_le_product : MvPolynomial.zeroLocus K (I ⊓ J) ⊆ MvPolynomial.zeroLocus K (I * J) := by
      apply MvPolynomial.zeroLocus_anti_mono
      exact Ideal.mul_le_inf
    rw [productZeroLocus] at inter_le_product -- zeroLocus K (I * J) = zeroLocus K I ∪ zeroLocus K J from earlier theorem
    apply inter_le_product
    exact h
  · intro h p hp -- This is essentially trivial as p ∈ I ⊓ J so is p ∈ I ∧ p ∈ J, so will be 0 ∀ x ∈ zeroLocus K I, ∀ x ∈ zeroLocus K J
    simp only [Submodule.mem_inf] at hp
    rcases hp with ⟨p_inI, p_inJ⟩
    rcases h with inI | inJ
    · rw [MvPolynomial.mem_zeroLocus_iff] at inI
      apply inI
      exact p_inI
    · rw [MvPolynomial.mem_zeroLocus_iff] at inJ
      apply inJ
      exact p_inJ


-- This is true by putting by just rewriting some of theorems have already proved
theorem zariskiClosureUnion (S T : Set (σ → K)) :
  zariskiClosure (S ∪ T) = zariskiClosure S ∪ zariskiClosure T := by
  rw [zariskiClosure, zariskiClosure, zariskiClosure]
  rw [← intersectionInsideGivesUnion]
  congr
  symm
  exact vanishingIdealIntersectionUnion S T


-- not included in the text yet! add it. And maybe also do I:J subset of I:J∞
theorem idealLeqSaturation {I J : Ideal (MvPolynomial σ K)} :
  I ≤ saturationIdeal I J := by
  intro f hf g hg
  use 1
  simp only [pow_one]
  exact Ideal.IsTwoSided.mul_mem_of_left g hf


--theorem quotientIsSubsetOfSaturation [Fintype σ] {I J: Ideal (MvPolynomial σ K)}:
--      MvPolynomial.zeroLocus K (I.colon J) ⊆
--      MvPolynomial.zeroLocus K (saturationIdeal I J) := by
--  have h₀: saturationIdeal I J ≥ I := by


-- Some alternative formalisations
-- theorem sumZeroLocus (I J : Ideal (MvPolynomial σ K)) :
--   MvPolynomial.zeroLocus K (I + J) = MvPolynomial.zeroLocus K I ∩ MvPolynomial.zeroLocus K J := by
--     ext x
--     constructor
--     · intro h
--       constructor
--       · intro p hp -- p is the polynomial we need to evaluate to 0
--         apply h
--         apply Ideal.mem_sup_left -- Have that p ∈ I implies p ∈ I + J
--         exact hp -- So as all polynomials in I + J vanish at x we are done
--       · intro p hp -- Analogous to the above
--         apply h
--         apply Ideal.mem_sup_right
--         exact hp
--     · intro h p hp -- p is the polynomial we need to evaluate to 0
--       have is_sum : ∃ f ∈ I, ∃ g ∈ J, f + g = p := by
--         simp only [ add_eq_sup] at hp -- I + J = I ⊔ J, this is how the sum is represented in Mathlib, as supremum of the ideals
--         apply Submodule.mem_sup.mp -- By definition if an element is in the sum of ideals it can be written as a sum of two elements, each one in one of the ideals
--         exact hp
--       simp only [Set.mem_inter_iff, MvPolynomial.mem_zeroLocus_iff, MvPolynomial.aeval_eq_eval] at h -- Unpacks the defintion of x being in the set given by h
--       rcases is_sum with ⟨f, hf, g, hg, f_g_sum⟩ -- Get the MvPolynomials that p can be written as a sum of
--       subst f_g_sum -- Substitute them in
--       simp only [MvPolynomial.aeval_eq_eval, map_add]
--       simp [h, hf, hg]


-- theorem inProductIsZero {x : σ → K} {I J : Ideal (MvPolynomial σ K)}
--   (h : ∀ f ∈ I, ∀ g ∈ J, (MvPolynomial.eval x) (f * g) = 0) :
--   ∀ p ∈ I * J, (MvPolynomial.eval x) p = 0 := by
--   intro p hp
--   refine Submodule.mul_induction_on (R := MvPolynomial σ K) (C := fun f : MvPolynomial σ K => (MvPolynomial.eval x) f = 0) hp ?_ ?_
--   · exact h -- Need to show that any product m * n where m ∈ I, n ∈ J evaluates to 0 at x as I * J consists of finite sums of these products
--   · intro a b ha hb -- Need to show that adding two functions that are 0 at x gives a function that is 0 at x
--     simp only [map_add, ha, hb, add_zero]


-- theorem productZeroLocus (I J : Ideal (MvPolynomial σ K)) :
--   MvPolynomial.zeroLocus K (I * J) = MvPolynomial.zeroLocus K I ∪ MvPolynomial.zeroLocus K J := by
--   ext x
--   constructor
--   · intro h
--     have product_zero : ∀ f ∈ I, ∀ g ∈ J, (MvPolynomial.eval x) (f * g) = 0 := by -- This is essentially trivial as f * g ∈ I * J, ∀ f ∈ I, ∀ g ∈ J
--         intro f hf g hg
--         apply h
--         apply Ideal.mul_mem_mul -- f * g ∈ I * J
--         exact hf
--         exact hg
--     by_cases h' : x ∈ MvPolynomial.zeroLocus K I -- Split into cases as easier to get use contradiction like this
--     · left
--       exact h'
--     · right
--       by_contra h'' -- Suppose for contradiction that we also have x ∉ MvPolynomial.zeroLocus K J
--       have get_contra : ¬(∀ f ∈ I, ∀ g ∈ J, (MvPolynomial.eval x) (f * g) = 0) := by -- Write statement like this so contradiction tactic works
--         push Not
--         rw [ notInZeroLocus] at h' h''
--         rcases h' with ⟨f, inI, hf⟩
--         rcases h'' with ⟨g, inJ, hg⟩
--         use f -- Verifying that f * g does not evaluate to 0 at x
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
--     -- Looks the same as in the previous part part but true for a different reason, x ∈ MvPolynomial.zeroLocus K I, so
--     -- any product including a function in I will evaluate to 0 at x
--     · have product_zero : ∀ f ∈ I, ∀ g ∈ J, (MvPolynomial.eval x) (f * g) = 0 := by
--         intro f hf g hg
--         simp only [map_mul, mul_eq_zero]
--         left
--         apply inI
--         exact hf
--       apply inProductIsZero product_zero -- As any element in I * J is a finite sum of product i * j, i ∈ I, j ∈ J we're done
--       exact hp
--     -- Analogous to above
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
--     -- Basically if f ∈ <f1,...,fs> then it will vanish at any point where all these generators vanish
--     have gen_set_inclusion : Ideal.span F ≤ MvPolynomial.vanishingIdeal K (affineVariety F) := by
--       intro p hp y hy
--       apply inSpanAffineVarietyGenerators F hy
--       exact hp
--     -- Use anti-monotonicity of zero loci
--     have affine_variety_reversed :
--     MvPolynomial.zeroLocus K (MvPolynomial.vanishingIdeal K (affineVariety F)) ≤ MvPolynomial.zeroLocus K (Ideal.span F) := by
--       apply MvPolynomial.zeroLocus_anti_mono
--       exact gen_set_inclusion
--     rw [zeroLocusOfGenSetIsVariety F] at affine_variety_reversed -- Go from V(<f1,...,fs>) to V(f1,...,fs) as they are equal
--     apply affine_variety_reversed
--     exact h
--   · intro h p hp
--     apply hp
--     exact h

-- -- Chapter 4 §4 Prop 7 (ii)
-- theorem varietyZariskiUnion [Fintype σ] {F G : Set (MvPolynomial σ K)} :
--  affineVariety F = (affineVariety F ∩ affineVariety G)
--          ∪ zariskiClosure (affineVariety F \ affineVariety G) := by
--  apply Set.Subset.antisymm
--  · have h₀: (affineVariety F) \ (affineVariety G)
--        ⊆ zariskiClosure (affineVariety F \ affineVariety G) := by
--        rw [zariskiClosure]
--        apply setContainedInVariety
--    conv_lhs =>
--      rw [← inter_union_diff (affineVariety F) (affineVariety G)]
--    gcongr

--  · apply union_subset
--    · exact inter_subset_left
--    · rw [zariskiClosure]
--      -- apply Prop 1
--      have h₁: (affineVariety F) \ (affineVariety G) ⊆ affineVariety F := by
--        simp

--      apply (smallestVariety (affineVariety F \ affineVariety G)).left
--      exact h₁


-- Some alternative formalisations
-- theorem inSpanAffineVarietyGenerators {x : σ → K} (F : Set (MvPolynomial σ K)) (h : x ∈ affineVariety F) :
--   ∀ p ∈ Ideal.span F, (MvPolynomial.eval x) p = 0 := by
--   intro p hp
--   -- This gives us that p ∈ I = <F> means that it is a linear combination of a finite number of these generators
--   have in_span: ∃ (l : ↑F →₀ MvPolynomial σ K), (Finsupp.linearCombination (MvPolynomial σ K) Subtype.val) l = p := by
--     apply (Finsupp.mem_span_iff_linearCombination (MvPolynomial σ K) (F) (p)).mp
--     exact hp
--   rcases in_span with ⟨coeffs, is_lin_comb⟩ -- Extract the coefficients
--   subst is_lin_comb
--   rw [Finsupp.linearCombination_apply (MvPolynomial σ K) (coeffs)] -- Writes the linear combination as an actual linear combination
--   simp [Finsupp.sum, memAffineVariety.mp h]


-- Ideal generated by a finite generating set
-- theorem basisSameVariety (F G : Finset (MvPolynomial σ K)) :
--   Ideal.span (F : Set (MvPolynomial σ K)) = Ideal.span (G : Set (MvPolynomial σ K)) →
--   affineVariety (F : Set (MvPolynomial σ K)) = affineVariety (G : Set (MvPolynomial σ K)) := by
--   intro h
--   ext x
--   constructor
--   · intro hx p hp
--     apply inSpanAffineVarietyGenerators F hx -- All functions in F vanish at x which implies all functions in ideal generated by F do to
--     rw [ h] -- As ideals are equal all functions in ideal spanned by G vanish at x
--     exact Submodule.mem_span_of_mem hp -- p ∈ G the generating set so vanishes at x
--   · intro hx p hp -- Analogus to above
--     apply inSpanAffineVarietyGenerators G hx
--     rw [← h]
--     exact Submodule.mem_span_of_mem hp
