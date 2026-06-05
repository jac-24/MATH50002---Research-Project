import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
open Polynomial Set Pointwise

variable {K : Type*} [Field K] [DecidableEq K]


-- /-- Specification bridge. Can be noncomputable — it exists only for proofs.
--     Little-endian: index i ↦ coefficient of X^i. Trailing zeros are ignored. -/
-- noncomputable def ofCoeffs (cs : List K) : K[X] :=
--   ∑ i ∈ Finset.range cs.length, C (cs.getD i 0) * X ^ i

-- /-- The correctness spec, stated entirely in the abstract world. -/
-- theorem divModCoeffs_spec {p q : List K} (hq : ofCoeffs q ≠ 0) :
--     ofCoeffs p
--       = ofCoeffs (divModCoeffs p q).1 * ofCoeffs q + ofCoeffs (divModCoeffs p q).2
--     ∧ (ofCoeffs (divModCoeffs p q).2).degree < (ofCoeffs q).degree := sorry




-- A conceptual helper function you would need to write
def dropTrailingZeros (xs : List K) : List K :=
  (xs.reverse.dropWhile (fun x => x = 0)).reverse



variable {K : Type} [Field K] [Inhabited K] [DecidableEq K]

-- Assuming you have your dropTrailingZeros function defined above
-- def dropTrailingZeros (l : List K) : List K := ...

partial def divModCoeffs (f g : List K) : List K × List K :=
  if g = [] ∨ g = [(0 : K)] ∨ f.length < g.length then
    ([], f)
  else
    let initialQ : List K := (List.range (f.length - g.length + 1)).map (fun _ => (0 : K))

    let rec loop (q r : List K) : List K × List K :=
      if r = [(0 : K)] ∨ r.length < g.length then
        (dropTrailingZeros q, r)
      else
        let rlen := r.length
        let glen := g.length
        let currIndex := rlen - glen

        let currItem := r.getLastD (0 : K) / g.getLastD (0 : K)

        let newQ := q.set currIndex currItem

        let scaledG := g.map (fun c => currItem * c)
        let shiftedG := List.replicate currIndex (0 : K) ++ scaledG
        let newR_raw := List.zipWith (fun a b => a - b) r shiftedG

        let newR := dropTrailingZeros newR_raw

        loop newQ newR
    loop initialQ f

#eval divModCoeffs [(0 : ℚ), (0 : ℚ), (1 : ℚ)] [(0 : ℚ), (1 : ℚ)]
