import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Ideal.Quotient.Basic


import Algebraicgeometry.FormFundRes
import Algebraicgeometry.FromTopToAlg
import Algebraicgeometry.ZariskiTop

open FiniteGenSets
open FromTopToAlg
open ZariskiTop

noncomputable section

variable {K : Type*} [Field K]
variable {σ : Type*}
variable {τ : Type*}


-- φ takes as an input a point in the affine variety V ⊆ K^m
-- and returns a point in the affine variety W ⊆ K^n
def isPolynomialMapping (V : Set (σ → K)) (W : Set (τ → K)) (φ : V → (τ → K)) : Prop :=
  ∃ F : τ → (MvPolynomial σ K), ∀ x : V, ∀ t : τ, (φ x) t  = (MvPolynomial.eval x) (F t)
  ∧ ∀ x : V , φ x ∈ W --checks that image of φ is a subset of W
  ∧ isAffineVariety V  ∧ isAffineVariety W --checks that V and W are affine varieties

/- Let V ⊆ K^m, W ⊆ K^n be affine varieties
  A function φ : V → W is a polynomial mapping
  iff there exist polynomials f_1,...,f_n ∈ k[x1,...,xm] s.t.
  φ (a_1,..,a_m) = (f_1(a_1,..,a_m),...,f_n(a_1,..,a_m))
-/
-- polynomialMapping takes a set of polynomials and returns the polynomial map
def polynomialMapping (F : τ → (MvPolynomial σ K)) (V : Set (σ → K)) (isVar : isAffineVariety V)
    : V → (τ → K) :=
  fun (x : V) (t : τ) => (MvPolynomial.eval x) (F t)


-- because isPolynomialMapping takes φ : K^n → K^m and in Lean K is not the same as (Fin 1) → K
-- I had to create a new function isScalarPolynomialMap
-- isScalarPolynomialMap checks if φ : V → K is a polynomial map
def isScalarPolynomialMap (V : Set (σ → K)) (φ : V → K) : Prop :=
  ∃ f : MvPolynomial σ K, ∀ x : V, φ x = (MvPolynomial.eval x) f
   ∧ isAffineVariety V

-- Define the coordinate ring k[V] = {φ : V → K | φ is a polynomial map}
def coordinateRing (V : Set (σ → K)) (isVar : isAffineVariety V) : Subring (V → K) where
  carrier := { φ : V → K | isScalarPolynomialMap V φ }
  add_mem' := by
    sorry
  mul_mem' := by
    sorry
  one_mem' := by
    use 1
    intro x
    constructor
    · simp
    · exact isVar

  neg_mem' := by
    sorry

  zero_mem' := by
    use 0
    intro x
    constructor
    · simp
    · exact isVar

-- similarly, to define the lemma below I need a version of polynomialMapping from V → K
def scalarPolynomialMap (f : MvPolynomial σ K) (V : Set (σ → K)) (isVar : isAffineVariety V) : V → K :=
  fun (x : V) => (MvPolynomial.eval x) f


-- Two polynomials f,g ∈ K[x1,...,xn] represent the same polynomial map φ : V → K  iff  f - g ∈ I(V)
-- where I(V) = MvPolynomial.vanishingIdeal V from Mathlib
------////////////////////////NEED TO THINK OF A BETTER NAME//////////////////////////-----------------/
lemma scalarPolynomialMapEquivalence (f : MvPolynomial σ K) (g : MvPolynomial σ K)
    (V : Set (σ → K)) (isVar : isAffineVariety V) :
    scalarPolynomialMap f V = scalarPolynomialMap g V ↔ (f - g) ∈ MvPolynomial.vanishingIdeal K V  := by
  sorry


lemma polynomialMapEquivalence (F : τ → (MvPolynomial σ K)) (G : τ → (MvPolynomial σ K))
    (V : Set (σ → K)) (isVar : isAffineVariety V) :
    ∀ t : τ , scalarPolynomialMap (F t) V = scalarPolynomialMap (G t) V
    ↔ (F t - G t) ∈ MvPolynomial.vanishingIdeal K V := by
  sorry


-- Goal: Show that k[V] is isomorphic to k[x1,...,xn]/I(V)
-- 1) Create map ϕ : k[x1,...,xn] → k[V] defined as f
-- 2) Show that ϕ is a homomorphism
-- 3) Apply 1st isomorphism theorem to ϕ



theorem coordinateRingEquivQuotientVanishingIdeal (V : Set (σ → K)) (isVar : isAffineVariety V) :
    ∃ ψ : (coordinateRing V isVar ≃+* (MvPolynomial σ K) ⧸ (MvPolynomial.vanishingIdeal K V)), true := by

  sorry




-- V is irreducible <=> I(V) is a prime ideal already proved by Jibreel
-- I(V) is a prime ideal <=> k[V] is an integral domain follows from ring theory and k[V] ≅ k[x1,...,xn]/I(V) see mathlib below
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/Quotient/Basic.html#Ideal.Quotient.isDomain_iff_prime
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Ring/Defs.html#IsDomain
theorem irred_iff_coordinateRing_isIntegralDomain (V : Set (σ → K))  (isVar : isAffineVariety V) :
    isIrreducible V ↔ (coordinateRing V isVar).IsDomain := by
  -- apply irreduciblePrimeIdeal theorem
  -- apply isDomain_iff_prime to coordRing and I(V)
  sorry
