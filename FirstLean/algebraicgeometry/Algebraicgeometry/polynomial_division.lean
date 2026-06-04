import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
open Polynomial Set Pointwise

variable {K : Type*} [Field K] [DecidableEq K]


/-- Specification bridge. Can be noncomputable — it exists only for proofs.
    Little-endian: index i ↦ coefficient of X^i. Trailing zeros are ignored. -/
noncomputable def ofCoeffs (cs : List K) : K[X] :=
  ∑ i ∈ Finset.range cs.length, C (cs.getD i 0) * X ^ i

-- A conceptual helper function you would need to write
def dropTrailingZeros (xs : List K) : List K :=
  (xs.reverse.dropWhile (fun x => x = 0)).reverse

/-- Executable long division on coefficient lists. (Sketch — fill in the
    recursion; terminate by well-founded recursion on the dividend's length,
    or with fuel = p.length. Internally locate the leading term by skipping
    trailing zeros.) -/
partial def divModCoeffs (f g : List K) : List K × List K :=
  let q := (List.range g.length).map (fun _ => (0 : K))
  let r := f
  if h : r = [(0 : K)] ∨ r.length < g.length then
    (q, r)
  else
    have h' : q.length = g.length := by
      simp [q]
    have h'' : q.length ≤ r.length := by
      push Not at h
      obtain ⟨h1, h2⟩ := h
      rw [← h'] at h2
      exact h2
    let rlen := r.length
    let glen := g.length
    let currIndex := rlen - glen
    let currItem := q.getD currIndex (0 : K) + (r.getLastD (0 : K) / g.getLastD (0 : K))
    let newQ_raw := q.set (currIndex) (currItem)
    let newQ := dropTrailingZeros newQ_raw
    let scaledG := g.map (fun c => currItem * c)
    let shiftedG := List.replicate currIndex (0 : K) ++ scaledG
    let newR_raw := List.zipWith (fun a b => a - b) r shiftedG
    let newR := dropTrailingZeros newR_raw
    divModCoeffs newQ newR

    -- have decreasing : newR = [(0 : K)] ∨ newR.length < r.length := by
    --   by_cases hp : newR = [(0 :K)]
    --   · left
    --     exact hp
    --   · right
    --     simp [newR, newR_raw, shiftedG, scaledG, currItem]
    --     have hq_zero : q[currIndex]?.getD (0 : K) = (0 : K) := by
    --       simp [q]
    --       rw [List.getElem?_replicate]
    --       split
    --       · rfl
    --       · rfl
    --     rw [hq_zero, zero_add]

    --     -- 1. Assert the length of the raw zipped list
    --     have h_raw_len : newR_raw.length = r.length := by
    --       simp [newR_raw, shiftedG, scaledG, currIndex, rlen, glen, le_tsub_add]

    --     -- 2. Assert that the highest degree terms mathematically cancelled to 0
    --     have h_raw_last : newR_raw.getLast? = some (0 : K) := by
    --       sorry -- Prove this using the field division axioms (div_mul_cancel₀)

    --     -- 3. Assert the generic property of your dropTrailingZeros function
    --     have h_drop_shrinks : (dropTrailingZeros newR_raw).length < newR_raw.length := by
    --       sorry -- Prove that dropping trailing zeros on a list ending in 0 shrinks it

    --     -- Now, simply chain these facts together to close the main goal!
    --     -- Because drop(raw) < raw, and raw = r, drop(raw) < r.



#eval divModCoeffs [(0 : ℚ), (0 : ℚ), (1 : ℚ)] [(0 : ℚ), (1 : ℚ)]

/-- The correctness spec, stated entirely in the abstract world. -/
theorem divModCoeffs_spec {p q : List K} (hq : ofCoeffs q ≠ 0) :
    ofCoeffs p
      = ofCoeffs (divModCoeffs p q).1 * ofCoeffs q + ofCoeffs (divModCoeffs p q).2
    ∧ (ofCoeffs (divModCoeffs p q).2).degree < (ofCoeffs q).degree := sorry
