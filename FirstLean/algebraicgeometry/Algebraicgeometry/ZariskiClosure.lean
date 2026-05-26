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


