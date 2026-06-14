import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations


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
  (∃ F : τ → (MvPolynomial σ K), ∀ x : V, ∀ t : τ, (φ x) t  = (MvPolynomial.eval x) (F t))
  ∧ (∀ x : V , φ x ∈ W) --checks that image of φ is a subset of W
  ∧ isAffineVariety V  ∧ isAffineVariety W --checks that V and W are affine varieties


-- because isPolynomialMapping takes φ : K^n → K^m and in Lean K is not the same as (Fin 1) → K
-- I had to create a new function isScalarPolynomialMap
-- isScalarPolynomialMap checks if φ : V → K is a polynomial map
def isScalarPolynomialMap (V : Set (σ → K)) (φ : V → K) : Prop :=
  ∃ f : MvPolynomial σ K, ∀ x : V, φ x = (MvPolynomial.eval x) f
  ∧ isAffineVariety V

-- Define the coordinate ring k[V] = {φ : V → K | φ is a polynomial map}
-- since the set of all functions from V → K with + and * is a ring
-- we can define k[V] as a subring so that we don't have to prove all the ring axioms from scratch
def coordinateRing (V : Set (σ → K)) (isVar : isAffineVariety V) : Subring (V → K) where
  carrier := { φ : V → K | isScalarPolynomialMap V φ }
  -- proving the axioms
  add_mem' := by
    intro a b ha hb
    rcases ha with ⟨pa,hpa⟩
    rcases hb with ⟨pb,hpb⟩
    use pa + pb
    intro x
    constructor
    · simp only [Pi.add_apply, map_add]
      rw[(hpa x).left,(hpb x).left]
    · exact isVar

  mul_mem' := by
    intro a b ha hb
    rcases ha with ⟨pa,hpa⟩
    rcases hb with ⟨pb,hpb⟩
    use pa * pb
    intro x
    constructor
    · simp only [Pi.mul_apply, map_mul]
      rw[(hpa x).left,(hpb x).left]
    · exact isVar

  one_mem' := by
    use 1
    intro x
    constructor
    · simp only [Pi.one_apply, map_one]
    · exact isVar

  neg_mem' := by
    intro ψ h
    rcases h with ⟨p,hp⟩
    use -p
    intro x
    constructor
    · simp only [Pi.neg_apply, map_neg, neg_inj]
      exact (hp x).left
    · exact isVar

  zero_mem' := by
    use 0
    intro x
    constructor
    · simp only [Pi.zero_apply, map_zero]
    · exact isVar


-- define a homomorphism K[x1,...,xn] → K[V] so that f
def polynomialHomomorphism (V : Set (σ → K)) (isVar : isAffineVariety V) : (MvPolynomial σ K) →+* (V → K) := {
  -- the map takes polynomials in K[σ] and restricts their domain to V resulting in a polynomial in k[V]
  toFun := fun p => (fun (x : V) => (MvPolynomial.eval x) p)
  -- prove that this map is a homomorphism
  -- show that f(0) = 0
  map_zero' := by
    simp only [map_zero]
    rfl
  -- show that f(1) = 1
  map_one' := by
    simp only [map_one]
    rfl
  -- show that f(x+y) = f(x) + f(y)
  map_add' := by
    intro x y
    simp only [map_add]
    rfl
  -- show that f(xy) = f(x)f(y)
  map_mul' := by
    intro x y
    simp only [map_mul]
    rfl
  }


-- ker(hom) = I(V)
lemma ker_eq_vanishingIdeal (V : Set (σ → K)) (isVar : isAffineVariety V) :
    (MvPolynomial.vanishingIdeal K V) = RingHom.ker (polynomialHomomorphism V isVar) := by
  ext p
  -- ⊢ p ∈ MvPolynomial.vanishingIdeal K V ↔ p ∈ RingHom.ker (polynomialHomomorphism V isVar)
  constructor
  -- show that I(V) ⊆ ker(hom)
  · intro inIdeal
    simp only [RingHom.mem_ker]
    rw[MvPolynomial.mem_vanishingIdeal_iff] at inIdeal
    -- define f = image of poly p under homomorphism
    let f := (polynomialHomomorphism V isVar).toFun p
    have h : f = 0 := by
      ext x
      apply inIdeal
      simp
    exact h
  -- show that ker(hom) ⊆ I(V)
  · intro inKer x hx
    simp only [MvPolynomial.aeval_eq_eval]
    rw[RingHom.mem_ker] at inKer
    simp [polynomialHomomorphism] at inKer
    -- theorem congr_fun (h : f = g) (a : α) : f a = g a := (from Mathlib)
    exact congr_fun inKer ⟨x,hx⟩


-- im(hom) = K[V]
lemma range_eq_coordinateRing (V : Set (σ → K)) (isVar : isAffineVariety V) :
    RingHom.range (polynomialHomomorphism V isVar) = (coordinateRing V isVar) := by
  ext f
  -- ⊢ f ∈ (polynomialHomomorphism V isVar).range ↔ f ∈ coordinateRing V isVar
  constructor
  -- im(hom) ⊆ K[V]
  · intro inRange -- f ∈ (polynomialHomomorphism V isVar).range
    simp [polynomialHomomorphism] at inRange
    obtain ⟨p,hp⟩ := inRange -- p : MvPolynomial σ K, hp : (fun x => (MvPolynomial.eval ↑x) p) = f
    -- to show that f ∈ coordinateRing V isVar we just need to prove that f is a scalar poly map
    have h : isScalarPolynomialMap V f := by
      unfold isScalarPolynomialMap
      use p
      intro x
      -- use refine tactic with theorem congr_fun (h : f = g) (a : α) : f a = g a := (from Mathlib)
      refine ⟨congr_fun hp.symm x, isVar⟩
    exact h
  -- K[V] ⊆ im(hom)
  · intro inCoordRing
    simp [coordinateRing] at inCoordRing
    simp [isScalarPolynomialMap] at inCoordRing
    obtain ⟨p,h⟩ := inCoordRing -- p : MvPolynomial σ K, h : ∀ (a : σ → K) (b : a ∈ V), f ⟨a, b⟩ = (MvPolynomial.eval a) p ∧ isAffineVariety V
    simp [polynomialHomomorphism] -- unfold polynomialHomomorphism
    use p
    ext x -- using extensionality to unpack lambda function in the goal
    exact (h x x.2).1.symm -- evaluate h at x and pass in x.2 which is the proof that x ∈ V, then use .1 to take the first part of AND and .symm because the goal equality is the other way around


def coordinateRingIsomorphism (V : Set (σ → K)) (isVar : isAffineVariety V) :
    ((MvPolynomial σ K) ⧸ (MvPolynomial.vanishingIdeal K V) ≃+* coordinateRing V isVar) :=
  -- I(V) = ker(hom) => K[σ]/I(V) ≃+* K[σ]/ker(hom) using Mathlib Ideal.quotEquivOfEq
  let equiv1 : (MvPolynomial σ K) ⧸ (MvPolynomial.vanishingIdeal K V) ≃+* (MvPolynomial σ K) ⧸ (RingHom.ker (polynomialHomomorphism V isVar)) :=
    (Ideal.quotEquivOfEq (ker_eq_vanishingIdeal V isVar))
  -- K[σ]/ker(hom) ≃+* im(hom) by 1st isomorphism theorem defined as RingHom.quotientKerEquivRange in Mathlib
  let equiv2 : (MvPolynomial σ K) ⧸ (RingHom.ker (polynomialHomomorphism V isVar)) ≃+* (polynomialHomomorphism V isVar).range :=
     (RingHom.quotientKerEquivRange (polynomialHomomorphism V isVar))
  --  im(hom) ≃+* k[V] by range_eq_coordinateRing
  let equiv3 : (polynomialHomomorphism V isVar).range ≃+* (coordinateRing V isVar) :=
    -- we need to use the typecasting tactic A = B ▸ A ≃+* B to rewrite A ≃+* B as A ≃+* A and then apply reflexivity
    (range_eq_coordinateRing V isVar) ▸ RingEquiv.refl (polynomialHomomorphism V isVar).range
  -- chain all the isomorphisms together using transitivity
  (equiv1.trans equiv2).trans equiv3


-- V is irreducible <=> I(V) is a prime ideal already proved by Jibreel
-- I(V) is a prime ideal <=> k[V] is an integral domain follows from ring theory and k[V] ≅ k[x1,...,xn]/I(V) see mathlib below
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/Quotient/Basic.html#Ideal.Quotient.isDomain_iff_prime
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Ring/Defs.html#IsDomain
theorem irred_iff_coordRing_isDomain (V : Set (σ → K))  (isVar : isAffineVariety V) :
    isIrreducible V ↔ IsDomain (coordinateRing V isVar) := by
  -- apply V is irreducible <=> I(V) is a prime ideal
  rw[irreduciblePrimeIdeal]
  -- apply isomorphism definition and use theorem .isDomain_iff that says if A ≃+* B then isDomain A iff isDomain B
  rw[(coordinateRingIsomorphism V isVar).symm.isDomain_iff]
  -- apply IsDomain (R ⧸ I) ↔ I.IsPrime
  rw[Ideal.Quotient.isDomain_iff_prime]
  -- only goal left is to confirm V is an affine variety
  exact isVar



/- EXTRA CODE

  Let V ⊆ K^m, W ⊆ K^n be affine varieties
  A function φ : V → W is a polynomial mapping
  iff there exist polynomials f_1,...,f_n ∈ k[x1,...,xm] s.t.
  φ (a_1,..,a_m) = (f_1(a_1,..,a_m),...,f_n(a_1,..,a_m))

-- polynomialMapping takes a set of polynomials and returns the polynomial map
def polynomialMapping (F : τ → (MvPolynomial σ K)) (V : Set (σ → K)) (isVar : isAffineVariety V)
    : V → (τ → K) :=
  fun (x : V) (t : τ) => (MvPolynomial.eval x) (F t)


-- similarly, to define the lemma below I need a version of polynomialMapping from V → K
def scalarPolynomialMap (f : MvPolynomial σ K) (V : Set (σ → K)) (isVar : isAffineVariety V) : V → K :=
  fun (x : V) => (MvPolynomial.eval x) f


-- Two polynomials f,g ∈ K[x1,...,xn] represent the same polynomial map φ : V → K  iff  f - g ∈ I(V)
-- where I(V) = MvPolynomial.vanishingIdeal V from Mathlib
lemma scalarPolynomialMapEquivalence (f : MvPolynomial σ K) (g : MvPolynomial σ K)
    (V : Set (σ → K)) (isVar : isAffineVariety V) :
    scalarPolynomialMap f V = scalarPolynomialMap g V ↔ (f - g) ∈ MvPolynomial.vanishingIdeal K V  := by
  sorry


lemma polynomialMapEquivalence (F : τ → (MvPolynomial σ K)) (G : τ → (MvPolynomial σ K))
    (V : Set (σ → K)) (isVar : isAffineVariety V) :
    ∀ t : τ , scalarPolynomialMap (F t) V = scalarPolynomialMap (G t) V
    ↔ (F t - G t) ∈ MvPolynomial.vanishingIdeal K V := by
  sorry

-/
