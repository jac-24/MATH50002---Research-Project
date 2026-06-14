import mv_division_template
import Mathlib

/-!
# Bridge: MPoly n ⟶ MvPolynomial (Fin n) ℚ

Constructs the ring homomorphism

    φ : MPoly n → MvPolynomial (Fin n) ℚ

and establishes its key properties, connecting the executable multivariate division
algorithm in `mv_division_template` to the Gröbner basis theory in `poly_division`.
-/

open MvPolynomial
open scoped MonomialOrder

variable {n : Nat}

-- ── §1  Exponent vector conversion ───────────────────────────────────────────

/-- Convert `Exp n = Fin n → ℕ` to `Fin n →₀ ℕ` as a sum of single-variable Finsupps.
Since `Fin n` is finite, this gives the unique Finsupp with value `e i` at each `i`. -/
noncomputable def expToFinsupp (e : Exp n) : Fin n →₀ ℕ :=
  ∑ i : Fin n, Finsupp.single i (e i)

@[simp]
lemma expToFinsupp_apply (e : Exp n) (i : Fin n) :
    expToFinsupp e i = e i := by
  simp [expToFinsupp, Finsupp.finset_sum_apply, Finsupp.single_apply,
        Finset.mem_univ]

/-- `expToFinsupp` turns pointwise addition (`expMul`) into Finsupp addition. -/
lemma expToFinsupp_expMul (a b : Exp n) :
    expToFinsupp (expMul a b) = expToFinsupp a + expToFinsupp b := by
  ext i; simp [expMul, Finsupp.add_apply]

/-- `expToFinsupp` turns pointwise truncated subtraction (`expDiv`) into Finsupp subtraction. -/
lemma expToFinsupp_expDiv (a b : Exp n) :
    expToFinsupp (expDiv a b) = expToFinsupp a - expToFinsupp b := by
  ext i; simp [expDiv]

-- ── §2  The homomorphism ─────────────────────────────────────────────────────

/-- The ring homomorphism φ : MPoly n → MvPolynomial (Fin n) ℚ.
Each term `(c, e)` maps to the monomial `c · X^(expToFinsupp e)`;
the result is the sum in `MvPolynomial (Fin n) ℚ`. -/
noncomputable def toMvPoly (p : MPoly n) : MvPolynomial (Fin n) ℚ :=
  (p.toList.map fun (c, e) => MvPolynomial.monomial (expToFinsupp e) (c : ℚ)).sum

-- ── §3  Basic evaluations ─────────────────────────────────────────────────────

@[simp]
theorem toMvPoly_empty : toMvPoly (n := n) #[] = 0 := by
  simp [toMvPoly]

theorem toMvPoly_singleton (c : Rat) (e : Exp n) :
    toMvPoly #[(c, e)] = MvPolynomial.monomial (expToFinsupp e) (c : ℚ) := by
  simp [toMvPoly]

@[simp]
theorem toMvPoly_monom (c : Rat) (e : Exp n) :
    toMvPoly (monom c e) = MvPolynomial.monomial (expToFinsupp e) (c : ℚ) := by
  by_cases hc : c = 0
  · subst hc; simp [monom, toMvPoly]
  · simp only [monom, show (c == 0) = false from by simp [hc]]
    exact toMvPoly_singleton c e

-- ── §4  Concatenation ─────────────────────────────────────────────────────────

lemma toMvPoly_append (p q : MPoly n) :
    toMvPoly (p ++ q) = toMvPoly p + toMvPoly q := by
  simp [toMvPoly, Array.toList_append, List.map_append, List.sum_append]

-- ── §5  Simplify compatibility ───────────────────────────────────────────────

-- §5 helpers: BEq correctness for Exp n
private lemma exp_beq_true_iff_eq : ∀ {n : Nat} (a b : Exp n), (a == b) = true ↔ a = b := by
  intro n; induction n with
  | zero =>
    intro a b
    exact ⟨fun _ => funext (fun i => i.elim0), fun _ => rfl⟩
  | succ n ih =>
    intro a b
    have key : (a == b) =
        ((a ⟨0, Nat.zero_lt_succ n⟩ == b ⟨0, Nat.zero_lt_succ n⟩) &&
         ((fun i : Fin n => a i.succ) == (fun i => b i.succ))) := rfl
    simp only [key, Bool.and_eq_true, beq_iff_eq, ih]
    constructor
    · rintro ⟨h0, htail⟩
      funext i
      cases i using Fin.cases with
      | zero => simpa using h0
      | succ i => exact congr_fun htail i
    · intro h
      exact ⟨congr_fun h ⟨0, _⟩, funext (fun i => congr_fun h i.succ)⟩

-- §5 helpers: findIdx? spec lemmas
private lemma findIdx?_some_lt {α : Type*} {p : α → Bool} {as : Array α} {i : Nat}
    (h : as.findIdx? p = some i) : i < as.size := by
  rw [Array.findIdx?_eq_some_iff_getElem] at h; exact h.1

private lemma findIdx?_some_pred {α : Type*} {p : α → Bool} {as : Array α} {i : Nat}
    (h : as.findIdx? p = some i) : p (as[i]'(findIdx?_some_lt h)) = true := by
  rw [Array.findIdx?_eq_some_iff_getElem] at h; exact h.2.1

-- §5 helpers: filter, push, and update lemmas
private lemma toMvPoly_filter_zero (arr : MPoly n) :
    toMvPoly (arr.filter (fun (c, _) => c != 0)) = toMvPoly arr := by
  simp only [toMvPoly, Array.toList_filter]
  induction arr.toList with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨c, e⟩ := hd
    simp only [List.filter_cons]
    by_cases hc : c = 0
    · simp only [hc, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
                 List.map_cons, List.sum_cons, map_zero, zero_add, ih]
    · have : (c != 0) = true := by simp [hc]
      simp [this, ih]

private lemma toMvPoly_push' (acc : MPoly n) (c : Rat) (e : Exp n) :
    toMvPoly (acc.push (c, e)) = toMvPoly acc + MvPolynomial.monomial (expToFinsupp e) (c : ℚ) := by
  simp only [toMvPoly, Array.toList_push, List.map_append, List.sum_append,
             List.map_singleton, List.sum_singleton]

private lemma list_sum_set_update (l : List (Rat × Exp n)) (i : Nat) (hi : i < l.length) (r : Rat) :
    ((l.set i ((l[i]'hi).1 + r, (l[i]'hi).2)).map
        (fun (d, f) => MvPolynomial.monomial (expToFinsupp f) (d : ℚ))).sum =
    (l.map (fun (d, f) => MvPolynomial.monomial (expToFinsupp f) (d : ℚ))).sum +
    MvPolynomial.monomial (expToFinsupp (l[i]'hi).2) (r : ℚ) := by
  induction l generalizing i with
  | nil => simp at hi
  | cons hd tl ih =>
    obtain ⟨d₀, f₀⟩ := hd
    cases i with
    | zero =>
      simp only [List.set, List.getElem_cons_zero, List.map_cons, List.sum_cons, map_add]
      ring
    | succ k =>
      have hk : k < tl.length := Nat.lt_of_succ_lt_succ hi
      simp only [List.set_cons_succ, List.getElem_cons_succ, List.map_cons, List.sum_cons]
      rw [ih k hk]; ring

private lemma toMvPoly_mapIdx_update (acc : MPoly n) (i : Nat) (hi : i < acc.size) (r : Rat)
    (e : Exp n) (he : (acc[i]'hi).2 = e) :
    toMvPoly (acc.mapIdx fun j t => if j == i then (t.1 + r, t.2) else t) =
    toMvPoly acc + MvPolynomial.monomial (expToFinsupp e) (r : ℚ) := by
  have hset : acc.mapIdx (fun j t => if j == i then (t.1 + r, t.2) else t) =
      acc.set i ((acc[i]'hi).1 + r, (acc[i]'hi).2) := by
    apply Array.ext (by simp)
    intro j hj _
    simp only [Array.getElem_mapIdx, Array.getElem_set]
    by_cases hjk : j = i
    · subst hjk; simp
    · simp [show (j == i) = false from by simp [hjk], show ¬(i = j) from fun h => hjk h.symm]
  simp only [toMvPoly, hset, Array.toList_set]
  have hli : i < acc.toList.length := by simp [hi]
  have hget : acc[i]'hi = acc.toList[i]'hli := by simp [Array.getElem_toList]
  rw [hget, list_sum_set_update _ i hli r, ← hget, he]

-- §5 helpers: mergeStep and foldl invariant
private def mergeStep' (n : Nat) : MPoly n → Rat × Exp n → MPoly n :=
  fun acc (c, e) =>
    match acc.findIdx? (fun (_, f) => f == e) with
    | some i => acc.mapIdx fun j t => if j == i then (t.1 + c, t.2) else t
    | none   => acc.push (c, e)

private lemma foldl_merge_toMvPoly :
    ∀ (l : List (Rat × Exp n)) (acc : MPoly n),
    toMvPoly (l.foldl (mergeStep' n) acc) =
    toMvPoly acc + (l.map fun (c, e) => MvPolynomial.monomial (expToFinsupp e) (c : ℚ)).sum := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons hd tl ih =>
    obtain ⟨c, e⟩ := hd
    intro acc
    rcases h : acc.findIdx? (fun (_, f) => f == e) with _ | i
    · have step : mergeStep' n acc (c, e) = acc.push (c, e) := by simp [mergeStep', h]
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, step]
      rw [ih, toMvPoly_push']; ring
    · have step : mergeStep' n acc (c, e) =
          acc.mapIdx fun j t => if j == i then (t.1 + c, t.2) else t := by
        simp [mergeStep', h]
      have hlt := findIdx?_some_lt h
      have hpred := findIdx?_some_pred h
      have he : (acc[i]'hlt).2 = e := (exp_beq_true_iff_eq _ _).mp hpred
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, step]
      rw [ih, toMvPoly_mapIdx_update acc i hlt c e he]; ring

private lemma simplify_eq' (p : MPoly n) :
    simplify p = (p.toList.foldl (mergeStep' n) #[]).filter (fun (c, _) => c != 0) := by
  unfold mergeStep'
  rw [Array.foldl_toList]
  rfl

/-- The key compatibility: `simplify` merges same-exponent coefficients and removes
zeros, but neither operation changes the algebraic value in `MvPolynomial`.
Proof: the merged foldl is a rearrangement of the original sum (by
`MvPolynomial.monomial_add`), and zero terms vanish by `monomial_zero`. -/
theorem toMvPoly_simplify (p : MPoly n) :
    toMvPoly (simplify p) = toMvPoly p := by
  rw [simplify_eq', toMvPoly_filter_zero, foldl_merge_toMvPoly]
  simp [toMvPoly]

-- ── §5.5  flatMap helper ──────────────────────────────────────────────────────

/-- `toMvPoly` distributes over `Array.flatMap`:
each element of `p` contributes `toMvPoly (f t)` to the total sum. -/
lemma toMvPoly_flatMap (p : MPoly n) (f : Rat × Exp n → MPoly n) :
    toMvPoly (p.flatMap f) =
    (p.toList.map fun t => toMvPoly (f t)).sum := by
  simp only [toMvPoly, Array.toList_flatMap]
  generalize p.toList = l
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append,
               List.map_cons, List.sum_cons, ih]

-- ── §6  Ring homomorphism properties ─────────────────────────────────────────

theorem toMvPoly_add (p q : MPoly n) :
    toMvPoly (mAdd p q) = toMvPoly p + toMvPoly q := by
  simp only [mAdd, toMvPoly_simplify, toMvPoly_append]

/-- Helper: negating coefficients in a list negates the MvPolynomial sum. -/
private lemma list_neg_sum (l : List (Rat × Exp n)) :
    (l.map fun (c, e) => MvPolynomial.monomial (expToFinsupp e) (-c : ℚ)).sum =
    -(l.map fun (c, e) => MvPolynomial.monomial (expToFinsupp e) (c : ℚ)).sum := by
  induction l with
  | nil => simp
  | cons hd xs ih =>
    obtain ⟨c, e⟩ := hd
    simp only [List.map_cons, List.sum_cons]
    rw [ih, map_neg (MvPolynomial.monomial (expToFinsupp e))]
    ring

theorem toMvPoly_neg (p : MPoly n) :
    toMvPoly (p.map fun (c, e) => (-c, e)) = -toMvPoly p := by
  simp only [toMvPoly, Array.toList_map, List.map_map]
  exact list_neg_sum p.toList

theorem toMvPoly_sub (p q : MPoly n) :
    toMvPoly (mSub p q) = toMvPoly p - toMvPoly q := by
  simp [mSub, toMvPoly_add, toMvPoly_neg, sub_eq_add_neg]

/-- Helper: scaling a list by a monomial distributes over the sum. -/
private lemma list_scale_sum (c : Rat) (e : Exp n) (l : List (Rat × Exp n)) :
    (l.map fun (d, f) => MvPolynomial.monomial (expToFinsupp (expMul e f)) (c * d : ℚ)).sum =
    MvPolynomial.monomial (expToFinsupp e) (c : ℚ) *
    (l.map fun (d, f) => MvPolynomial.monomial (expToFinsupp f) (d : ℚ)).sum := by
  induction l with
  | nil => simp
  | cons hd xs ih =>
    obtain ⟨d, f⟩ := hd
    simp only [List.map_cons, List.sum_cons]
    rw [ih, expToFinsupp_expMul, ← MvPolynomial.monomial_mul]
    ring

/-- Scaling by `c · X^e` multiplies the polynomial by `monomial e c`. -/
theorem toMvPoly_scale (c : Rat) (e : Exp n) (p : MPoly n) :
    toMvPoly (mScale c e p) =
    MvPolynomial.monomial (expToFinsupp e) (c : ℚ) * toMvPoly p := by
  simp only [mScale, toMvPoly, Array.toList_map, List.map_map]
  exact list_scale_sum c e p.toList

private lemma list_mul_sum (l : List (Rat × Exp n)) (q : MvPolynomial (Fin n) ℚ) :
    (l.map fun (c, e) => MvPolynomial.monomial (expToFinsupp e) (c : ℚ) * q).sum =
    (l.map fun (c, e) => MvPolynomial.monomial (expToFinsupp e) (c : ℚ)).sum * q := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨c, e⟩ := hd
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    ring

theorem toMvPoly_mul (p q : MPoly n) :
    toMvPoly (mMul p q) = toMvPoly p * toMvPoly q := by
  simp only [mMul, toMvPoly_simplify, toMvPoly_flatMap]
  simp_rw [toMvPoly_scale]
  exact list_mul_sum p.toList (toMvPoly q)

-- ── §7  MonomialOrder from expGrlexLt ────────────────────────────────────────

-- Goal: construct `grlexMonomialOrder : MonomialOrder (Fin n)` so that the
-- abstract theorems in poly_division.lean (parameterised over any MonomialOrder)
-- can be applied to our executable division.
--
-- Strategy:
--   (a) Promote expGrlexLt to a LinearOrder on Exp n.
--   (b) Show expToFinsupp : Exp n ≃ Fin n →₀ ℕ is an order isomorphism.
--       (Fin n is finite, so every function Fin n → ℕ has finite support ⇒ bijection.)
--   (c) Transfer to a LinearOrder on Fin n →₀ ℕ.
--   (d) Show it is well-founded (from expGrlexLt_wf) and compatible with Finsupp
--       addition (from expMul_lt_mono + expToFinsupp_expMul).
--   (e) Package as MonomialOrder (Fin n).

-- (a-i) Antisymmetry: grlex strict order is irreflexive + total ⇒ antisymmetric.
theorem expGrlexLt_antisymm (a b : Exp n)
    (h : expGrlexLt a b = true) : expGrlexLt b a = false := by
  by_contra hba
  simp only [Bool.not_eq_false] at hba
  exact absurd (expGrlexLt_trans h hba) (by simp [expGrlexLt_irrefl])

-- (a-ii) Totality: any two distinct exponents are comparable.
theorem expGrlexLt_total (a b : Exp n) :
    a ≠ b → expGrlexLt a b = true ∨ expGrlexLt b a = true := by
  intro h
  simp only [expGrlexLt, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_iff]
  rcases Nat.lt_trichotomy (expDeg a) (expDeg b) with hdeg | hdeg | hdeg
  · exact Or.inl (Or.inl hdeg)
  · rcases expLexLt_total a b h with hlt | hlt
    · exact Or.inl (Or.inr ⟨hdeg, hlt⟩)
    · exact Or.inr (Or.inr ⟨hdeg.symm, hlt⟩)
  · exact Or.inr (Or.inl hdeg)

-- (b) expToFinsupp is a bijection (surjective because Fin n is finite).
theorem expToFinsupp_bijective : Function.Bijective (@expToFinsupp n) := by
  constructor
  · -- Injective: equal Finsupps agree at every index, so agree as functions.
    intro a b hab
    funext i
    have := Finsupp.ext_iff.mp hab i
    rwa [expToFinsupp_apply, expToFinsupp_apply] at this
  · -- Surjective: the underlying function of any f : Fin n →₀ ℕ is a preimage.
    intro f
    exact ⟨⇑f, by ext i; rw [expToFinsupp_apply]⟩

/-- The canonical order equivalence expToFinsupp as an `Equiv`. -/
noncomputable def expEquivFinsupp (n : Nat) : Exp n ≃ (Fin n →₀ ℕ) :=
  Equiv.ofBijective expToFinsupp expToFinsupp_bijective

-- (c) Compatibility with monomial multiplication:
-- expGrlexLt a b ⇒ expGrlexLt (k + a) (k + b)  (pointwise, i.e. expMul)
theorem expMul_lt_mono (k a b : Exp n) (h : expGrlexLt a b = true) :
    expGrlexLt (expMul k a) (expMul k b) = true := by
  simp only [expGrlexLt, expDeg_expMul, Bool.or_eq_true, Bool.and_eq_true,
             beq_iff_eq, decide_eq_true_iff] at *
  rcases h with h | ⟨h, h'⟩
  · left; omega
  · right; exact ⟨by omega, expLexLt_expMul_mono k a b h'⟩

-- (d-e) The MonomialOrder term.
-- Construction: define lt on Fin n →₀ ℕ by pulling back through expEquivFinsupp,
-- verify well-foundedness (InvImage of expGrlexLt_wf) and addition compatibility
-- (via expToFinsupp_expMul + expMul_lt_mono), then use MonomialOrder.mk.
noncomputable def grlexMonomialOrder (n : Nat) : MonomialOrder (Fin n) :=
  MonomialOrder.degLex

-- ── §8  Leading term compatibility ────────────────────────────────────────────

-- Connects our qsort-based `leadTerm` to `(grlexMonomialOrder n).degree`.

-- §8 helpers: expGrlexLt ↔ MonomialOrder.degLex

private lemma expDegAux_eq_sum : ∀ (m : Nat) (a : Fin m → Nat),
    expDegAux m a = ∑ i : Fin m, a i := by
  intro m; induction m with
  | zero => intro a; simp [expDegAux]
  | succ m ih => intro a; simp only [expDegAux, Fin.sum_univ_succ, ih]; rfl

private lemma expDeg_eq_finsupp_degree (e : Exp n) :
    expDeg e = (expToFinsupp e).degree := by
  rw [Finsupp.degree_eq_sum, expDeg, expDegAux_eq_sum]; congr 1; ext i; simp

private lemma expLexLtAux_iff_piLex : ∀ (m : Nat) (a b : Fin m → Nat),
    expLexLtAux m a b = true ↔ Pi.Lex (· < ·) (· < ·) a b := by
  intro m; induction m with
  | zero => intro a b; simp [expLexLtAux, Pi.Lex]
  | succ m ih =>
    intro a b; simp only [expLexLtAux, Pi.Lex]
    constructor
    · intro h
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_iff] at h
      rcases h with h | ⟨h0, htail⟩
      · exact ⟨⟨0, Nat.zero_lt_succ m⟩, fun j hj => absurd hj (Fin.not_lt_zero j), h⟩
      · obtain ⟨k, hk, hlt⟩ := (ih _ _).mp htail
        refine ⟨k.succ, fun j hj => ?_, hlt⟩
        cases j using Fin.cases with
        | zero => exact h0
        | succ l => exact hk l (Fin.succ_lt_succ_iff.mp hj)
    · rintro ⟨i, hi, hlt⟩
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_iff]
      cases i using Fin.cases with
      | zero => left; exact hlt
      | succ k =>
        right; exact ⟨hi ⟨0, Nat.zero_lt_succ m⟩ (Fin.succ_pos k),
               (ih _ _).mpr ⟨k, fun l hl => hi l.succ (Fin.succ_lt_succ_iff.mpr hl), hlt⟩⟩

private lemma expLexLt_iff_finsupp_lex (a b : Exp n) :
    expLexLt a b = true ↔ toLex (expToFinsupp a) < toLex (expToFinsupp b) := by
  rw [Finsupp.Lex.lt_iff]; simp only [ofLex_toLex, expToFinsupp_apply]
  exact expLexLtAux_iff_piLex n a b

private lemma expGrlexLt_iff_degLex (a b : Exp n) :
    expGrlexLt a b = true ↔ expToFinsupp a ≺[MonomialOrder.degLex] expToFinsupp b := by
  rw [MonomialOrder.degLex_lt_iff, Finsupp.DegLex.lt_iff]
  simp only [ofDegLex_toDegLex, expGrlexLt, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
             decide_eq_true_iff, ← expDeg_eq_finsupp_degree]
  exact ⟨fun h => h.imp id (fun ⟨h1, h2⟩ => ⟨h1, (expLexLt_iff_finsupp_lex a b).mp h2⟩),
         fun h => h.imp id (fun ⟨h1, h2⟩ => ⟨h1, (expLexLt_iff_finsupp_lex a b).mpr h2⟩)⟩

-- §8 helpers: coefficient extraction

/-- Named single-term map function to avoid lambda metavariable issues in induction. -/
noncomputable def termToMonom {n : Nat} (t : Rat × Exp n) : MvPolynomial (Fin n) ℚ :=
  MvPolynomial.monomial (expToFinsupp t.2) (t.1 : ℚ)

private lemma toMvPoly_eq_map_termToMonom (p : MPoly n) :
    toMvPoly p = (p.toList.map termToMonom).sum := by
  simp only [toMvPoly]; congr 1

private lemma coeff_list_sum_of_not_mem (l : List (Rat × Exp n)) (d : Fin n →₀ ℕ)
    (h : ∀ t ∈ l, expToFinsupp t.2 ≠ d) :
    (l.map termToMonom).sum.coeff d = 0 := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons, MvPolynomial.coeff_add]
    have hnd : (termToMonom hd).coeff d = 0 := by
      unfold termToMonom
      rw [MvPolynomial.coeff_monomial,
          if_neg (h hd (List.mem_cons.mpr (Or.inl rfl)))]
    rw [hnd, zero_add]
    exact ih (fun t ht => h t (List.mem_cons.mpr (Or.inr ht)))

private lemma support_toMvPoly_mem (p : MPoly n) (d : Fin n →₀ ℕ)
    (hd : d ∈ (toMvPoly p).support) :
    ∃ t ∈ (simplify p).toList, expToFinsupp t.2 = d := by
  by_contra hna
  push Not at hna
  have key : (toMvPoly (simplify p)).coeff d = 0 := by
    rw [toMvPoly_eq_map_termToMonom]
    exact coeff_list_sum_of_not_mem _ d hna
  rw [toMvPoly_simplify] at key
  exact absurd key (MvPolynomial.mem_support_iff.mp hd)

-- §8 helpers: nodup exponents in simplify p

/-- mapIdx that only changes first components preserves the list of second components. -/
private lemma mapIdx_update_snd (acc : MPoly n) (i : Nat) (c : Rat) :
    (acc.mapIdx fun j (t : Rat × Exp n) => if j == i then (t.1 + c, t.2) else t).toList.map Prod.snd =
    acc.toList.map Prod.snd := by
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    simp only [List.getElem_map, Array.getElem_toList, Array.getElem_mapIdx]
    split_ifs <;> rfl

/-- If `findIdx?` returns `none` for the predicate `· == e`, then `e` is not
among the exponents of `acc`. -/
private lemma not_mem_of_findIdx?_none (acc : MPoly n) (e : Exp n)
    (h : acc.findIdx? (fun t : Rat × Exp n => t.2 == e) = none) :
    e ∉ acc.toList.map Prod.snd := by
  intro hmem
  rw [List.mem_map] at hmem
  obtain ⟨t, ht, hte⟩ := hmem
  have hmema : t ∈ acc := by rwa [Array.mem_def]
  have hno : (t.2 == e) = false := (Array.findIdx?_eq_none_iff.mp h) t hmema
  rw [hte, (exp_beq_true_iff_eq e e).mpr rfl] at hno
  exact absurd hno (by decide)

/-- The `mergeStep'` operation preserves the invariant that exponents are distinct. -/
private lemma mergeStep_nodup (acc : MPoly n) (c : Rat) (e : Exp n)
    (hnd : (acc.toList.map Prod.snd).Nodup) :
    ((mergeStep' n acc (c, e)).toList.map Prod.snd).Nodup := by
  rcases h : acc.findIdx? (fun t : Rat × Exp n => t.2 == e) with _ | i
  · have hstep : mergeStep' n acc (c, e) = acc.push (c, e) := by simp [mergeStep', h]
    rw [hstep, Array.toList_push, List.map_append, List.map_singleton, List.nodup_append]
    refine ⟨hnd, List.nodup_singleton e, fun a ha b hb neq => ?_⟩
    have hbe : b = e := List.mem_singleton.mp hb
    exact not_mem_of_findIdx?_none acc e h (hbe ▸ neq ▸ ha)
  · have hstep : mergeStep' n acc (c, e) =
        acc.mapIdx fun j t => if j == i then (t.1 + c, t.2) else t := by
      simp [mergeStep', h]
    rw [hstep, mapIdx_update_snd]; exact hnd

/-- Iterating `mergeStep'` over a list preserves the Nodup invariant. -/
private lemma foldl_mergeStep_nodup (l : List (Rat × Exp n)) :
    ∀ (acc : MPoly n), (acc.toList.map Prod.snd).Nodup →
    ((l.foldl (mergeStep' n) acc).toList.map Prod.snd).Nodup := by
  induction l with
  | nil => intro acc hnd; simpa
  | cons hd tl ih =>
    intro acc hnd
    rw [List.foldl_cons]
    exact ih _ (mergeStep_nodup acc hd.1 hd.2 hnd)

/-- Filtering preserves the Nodup invariant on the exponent projection. -/
private lemma filter_nodup_snd (arr : MPoly n) (pred : Rat × Exp n → Bool)
    (hnd : (arr.toList.map Prod.snd).Nodup) :
    ((arr.filter pred).toList.map Prod.snd).Nodup := by
  rw [Array.toList_filter]
  apply List.Sublist.nodup _ hnd
  apply List.Sublist.map
  exact List.filter_sublist

/-- `simplify p` has pairwise-distinct exponents. -/
private lemma simplify_expNodup (p : MPoly n) :
    ((simplify p).toList.map Prod.snd).Nodup := by
  rw [simplify_eq']
  exact filter_nodup_snd _ _ (foldl_mergeStep_nodup p.toList #[] (by simp))

/-- If the exponents in `l` are pairwise distinct and `(c, e) ∈ l`, then the
coefficient of the `termToMonom` sum at `expToFinsupp e` equals `c`. -/
private lemma coeff_of_mem_nodup (l : List (Rat × Exp n)) (c : Rat) (e : Exp n)
    (hmem : (c, e) ∈ l) (hnodup : (l.map Prod.snd).Nodup) :
    (l.map termToMonom).sum.coeff (expToFinsupp e) = (c : ℚ) := by
  induction l with
  | nil => simp at hmem
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons, MvPolynomial.coeff_add]
    rw [List.map_cons, List.nodup_cons] at hnodup
    obtain ⟨hnotin, hnoduptl⟩ := hnodup
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · -- hd = (c, e): this term contributes c, tail contributes 0
      have hzero : (tl.map termToMonom).sum.coeff (expToFinsupp e) = 0 :=
        coeff_list_sum_of_not_mem tl (expToFinsupp e) fun t ht hte => by
          apply hnotin
          rw [List.mem_map]
          exact ⟨t, ht, expToFinsupp_bijective.injective hte⟩
      rw [hzero, add_zero]
      unfold termToMonom; rw [MvPolynomial.coeff_monomial, if_pos rfl]
    · -- hd ≠ (c, e): hd's exponent differs, recurse on tail
      have hne : expToFinsupp hd.2 ≠ expToFinsupp e := by
        intro heq
        apply hnotin
        rw [List.mem_map]
        exact ⟨(c, e), hmem', (expToFinsupp_bijective.injective heq).symm⟩
      have hzero_hd : (termToMonom hd).coeff (expToFinsupp e) = 0 := by
        unfold termToMonom; rw [MvPolynomial.coeff_monomial, if_neg hne]
      rw [hzero_hd, zero_add]
      exact ih hmem' hnoduptl

/-- The coefficient of `toMvPoly p` at `expToFinsupp e` equals `c` when `(c, e)` appears
in `(simplify p).toList`. -/
private lemma simplify_coeff_of_mem (p : MPoly n) (c : Rat) (e : Exp n)
    (hmem : (c, e) ∈ (simplify p).toList) :
    (toMvPoly p).coeff (expToFinsupp e) = (c : ℚ) := by
  rw [← toMvPoly_simplify p, toMvPoly_eq_map_termToMonom]
  exact coeff_of_mem_nodup _ c e hmem (simplify_expNodup p)

/-- If `leadTerm p = some (c, e)` then `toMvPoly p ≠ 0`.
Proof: the (c,e) term contributes monomial e c ≠ 0 to the sum. -/
theorem toMvPoly_ne_zero_of_leadTerm {p : MPoly n} {c : Rat} {e : Exp n}
    (h : leadTerm p = some (c, e)) : toMvPoly p ≠ 0 := by
  have hc := leadTerm_coeff_ne_zero h
  have hcoeff := simplify_coeff_of_mem p c e (leadTerm_mem h)
  intro heq
  rw [heq, MvPolynomial.coeff_zero] at hcoeff
  exact hc (by exact_mod_cast hcoeff.symm)

/-- The leading exponent of `toMvPoly p` (w.r.t. grlexMonomialOrder) equals
`expToFinsupp e` whenever `leadTerm p = some (c, e)`.
Proof: `leadTerm_is_max` says no term of `simplify p` exceeds `e` in grlex,
so `expToFinsupp e` is the maximum of `(toMvPoly p).support`. -/
theorem leadTerm_degree {p : MPoly n} {c : Rat} {e : Exp n}
    (h : leadTerm p = some (c, e)) :
    (grlexMonomialOrder n).degree (toMvPoly p) = expToFinsupp e := by
  simp only [grlexMonomialOrder]
  have hc := leadTerm_coeff_ne_zero h
  have hmax := leadTerm_is_max h
  have hcoeff := simplify_coeff_of_mem p c e (leadTerm_mem h)
  have hsup : expToFinsupp e ∈ (toMvPoly p).support := by
    rw [MvPolynomial.mem_support_iff, hcoeff]; exact_mod_cast hc
  have hle : ∀ d ∈ (toMvPoly p).support, d ≼[MonomialOrder.degLex] expToFinsupp e := by
    intro d hd
    obtain ⟨⟨c', e'⟩, hmem', heq⟩ := support_toMvPoly_mem p d hd
    rw [← heq]
    have hlt_not : ¬ expToFinsupp e ≺[MonomialOrder.degLex] expToFinsupp e' := by
      rw [← expGrlexLt_iff_degLex]; simp [hmax ⟨c', e'⟩ hmem']
    exact not_lt.mp hlt_not
  apply MonomialOrder.degLex.toSyn.injective
  apply le_antisymm
  · exact MonomialOrder.degree_le_iff.mpr hle
  · exact MonomialOrder.le_degree hsup

/-- The leading coefficient of `toMvPoly p` equals `c` (as a rational)
whenever `leadTerm p = some (c, e)`. -/
theorem leadTerm_leadingCoeff {p : MPoly n} {c : Rat} {e : Exp n}
    (h : leadTerm p = some (c, e)) :
    (grlexMonomialOrder n).leadingCoeff (toMvPoly p) = (c : ℚ) := by
  simp only [grlexMonomialOrder, MonomialOrder.leadingCoeff]
  have hdeg : MonomialOrder.degLex.degree (toMvPoly p) = expToFinsupp e := leadTerm_degree h
  rw [hdeg]
  exact simplify_coeff_of_mem p c e (leadTerm_mem h)

-- ── §9  Division identity bridge ──────────────────────────────────────────────

noncomputable def quotientSum
    (qs : Array (MPoly n)) (divs : Array (MPoly n)) : MvPolynomial (Fin n) ℚ :=
  (qs.zip divs).toList.foldl (fun acc (q, d) => acc + toMvPoly q * toMvPoly d) 0

/-- toMvPoly distributes over a list foldl of mAdd/mMul steps. -/
private lemma foldl_toMvPoly_eq (l : List (MPoly n × MPoly n)) (acc : MPoly n) :
    toMvPoly (l.foldl (fun a p => mAdd a (mMul p.1 p.2)) acc) =
    toMvPoly acc + (l.map fun p => toMvPoly p.1 * toMvPoly p.2).sum := by
  induction l generalizing acc with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨q, d⟩ := hd
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
    rw [toMvPoly_add, toMvPoly_mul]; ring

/-- foldl (· + f ·) 0 = sum of (map f). -/
private lemma foldl_add_sum (l : List (MPoly n × MPoly n)) :
    l.foldl (fun acc p => acc + toMvPoly p.1 * toMvPoly p.2) 0 =
    (l.map fun p => toMvPoly p.1 * toMvPoly p.2).sum := by
  have key : ∀ (acc : MvPolynomial (Fin n) ℚ),
      l.foldl (fun acc p => acc + toMvPoly p.1 * toMvPoly p.2) acc =
      acc + (l.map fun p => toMvPoly p.1 * toMvPoly p.2).sum := by
    induction l with
    | nil => simp
    | cons hd tl ih =>
      intro acc; simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]; ring
  simpa using key 0

/-- `quotientSum` equals `toMvPoly` applied to the MPoly foldl sum.
This is the key lemma connecting the `mAdd`/`mMul` foldl in `mvDiv_identity`
to the MvPolynomial `quotientSum`. -/
lemma quotientSum_foldl_eq (qs divs : Array (MPoly n)) (hs : qs.size = divs.size) :
    quotientSum qs divs =
    toMvPoly ((qs.zip divs).foldl (fun acc (q, d) => mAdd acc (mMul q d)) #[]) := by
  simp only [quotientSum, ← Array.foldl_toList, foldl_toMvPoly_eq, toMvPoly_empty, zero_add,
             foldl_add_sum]

/-- Helper for `quotientSum_updateAt`: updating one entry in a list of pairs
adds the extra term to the sum. -/
private lemma list_pair_sum_fst_update (l : List (MPoly n × MPoly n)) (i : Nat)
    (hi : i < l.length) (t : MPoly n) :
    ((l.set i (mAdd (l[i]'hi).1 t, (l[i]'hi).2)).map
        fun (q, d) => toMvPoly q * toMvPoly d).sum =
    (l.map fun (q, d) => toMvPoly q * toMvPoly d).sum +
    toMvPoly t * toMvPoly (l[i]'hi).2 := by
  induction l generalizing i with
  | nil => simp at hi
  | cons hd tl ih =>
    obtain ⟨q, d⟩ := hd
    cases i with
    | zero =>
      simp only [List.set_cons_zero, List.getElem_cons_zero, List.map_cons, List.sum_cons,
                 toMvPoly_add]
      ring
    | succ k =>
      have hk : k < tl.length := Nat.lt_of_succ_lt_succ hi
      simp only [List.set_cons_succ, List.getElem_cons_succ, List.map_cons, List.sum_cons]
      rw [ih k hk]; ring

/-- `quotientSum` is additive in the quotient array at a given index.
Used to step through `updateAt` calls in the divLoop invariant proof. -/
lemma quotientSum_updateAt (qs divs : Array (MPoly n)) (i : Nat)
    (hi : i < divs.size) (hs : qs.size = divs.size) (t : MPoly n) :
    quotientSum (qs.mapIdx fun j q => if j == i then mAdd q t else q) divs =
    quotientSum qs divs + toMvPoly t * toMvPoly (divs[i]'hi) := by
  have hqs_i : i < qs.size := hs ▸ hi
  have hzi : i < (qs.zip divs).size := by simp [hs, hi]
  have hzl : i < (qs.zip divs).toList.length := by simpa using hzi
  have heq_arr : (qs.mapIdx fun j q => if j == i then mAdd q t else q).zip divs =
      (qs.zip divs).set i (mAdd (qs[i]'hqs_i) t, divs[i]'hi) := by
    apply Array.ext (by simp [hs])
    intro j hj _
    simp only [Array.getElem_zip, Array.getElem_mapIdx, Array.getElem_set]
    by_cases hjk : j = i
    · subst hjk; simp
    · simp [show (j == i) = false from by simp [hjk], show ¬(i = j) from Ne.symm hjk]
  have heq_list : ((qs.mapIdx fun j q => if j == i then mAdd q t else q).zip divs).toList =
      (qs.zip divs).toList.set i (mAdd (qs[i]'hqs_i) t, divs[i]'hi) := by
    rw [heq_arr, Array.toList_set]
  have hget : (qs.zip divs).toList[i]'hzl = (qs[i]'hqs_i, divs[i]'hi) := by
    simp [Array.getElem_toList]
  simp only [quotientSum, foldl_add_sum, heq_list]
  have hkey := list_pair_sum_fst_update (qs.zip divs).toList i hzl t
  rw [hget] at hkey
  exact hkey

/-- `divLoop` preserves the size of the quotients array. -/
private theorem divLoop_size_invariant (divs : Array (MPoly n))
    (p : MPoly n) (qs : Array (MPoly n)) (r : MPoly n)
    (hs : qs.size = divs.size) : (divLoop divs p qs r).1.size = divs.size := by
  induction p using WellFounded.induction (hwf := mPolyLt_wf) generalizing qs r with
  | _ p ih =>
    unfold divLoop
    dsimp only []
    split
    · simpa using hs
    · rename_i c e hp
      split
      · apply ih
        · exact loop_rem_step p c e hp
        · exact hs
      · rename_i f i hfound
        split
        · rename_i hf
          have hpred := Array.find?_some hfound
          simp [hf] at hpred
        · rename_i cf ef hf
          apply ih
          · have hdv : expDivides ef e = true := by
              have hpred := Array.find?_some hfound
              simp only [hf] at hpred; exact hpred
            exact loop_div_step p f c cf e ef hp hf hdv (leadTerm_coeff_ne_zero hf)
          · show (qs.mapIdx fun j q => if j == i then mAdd q (monom (c / cf) (expDiv e ef)) else q).size = divs.size
            simp [hs]

/-- The quotient array returned by `mvDiv` has the same size as the divisor array. -/
theorem mvDiv_size (f : MPoly n) (divs : Array (MPoly n)) :
    (mvDiv f divs).1.size = divs.size := by
  simp only [mvDiv]
  apply divLoop_size_invariant
  simp

/-- The coefficient of `toMvPoly p` at `expToFinsupp e` is exactly `coeffAt p e`. -/
private lemma coeff_toMvPoly_eq_coeffAt (p : MPoly n) (e : Exp n) :
    (toMvPoly p).coeff (expToFinsupp e) = coeffAt p e := by
  simp only [toMvPoly, coeffAt]
  induction p.toList with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨c, f⟩ := hd
    simp only [List.map_cons, List.sum_cons, MvPolynomial.coeff_add, ih,
               MvPolynomial.coeff_monomial]
    by_cases hf : f = e
    · subst hf
      simp
    · have h1 : expToFinsupp f ≠ expToFinsupp e :=
        fun hc => hf (expToFinsupp_bijective.injective hc)
      have h2 : (f == e) = false := beq_eq_false_iff_ne.mpr hf
      simp [h1, h2]

/-- `toMvPoly` respects coefficient-wise equality `mEquiv`. -/
lemma toMvPoly_congr {p q : MPoly n} (h : mEquiv p q) : toMvPoly p = toMvPoly q := by
  apply MvPolynomial.ext
  intro d
  obtain ⟨e, rfl⟩ := expToFinsupp_bijective.surjective d
  rw [coeff_toMvPoly_eq_coeffAt, coeff_toMvPoly_eq_coeffAt, h e]

/-- Main bridge: the executable `mvDiv` satisfies the abstract division equation
in `MvPolynomial (Fin n) ℚ`. Follows from `mvDiv_identity` + `quotientSum_foldl_eq`
+ homomorphism properties. -/
theorem toMvPoly_mvDiv_identity (f : MPoly n) (divs : Array (MPoly n)) :
    let (qs, r) := mvDiv f divs
    toMvPoly f = quotientSum qs divs + toMvPoly r := by
  obtain ⟨qs, r, hqr⟩ : ∃ qs r, mvDiv f divs = (qs, r) := ⟨_, _, rfl⟩
  simp only [hqr]
  have hsize : qs.size = divs.size := by
    have h := mvDiv_size f divs; simp only [hqr] at h; exact h
  have hid := mvDiv_identity f divs
  simp only [hqr] at hid
  have hid' : toMvPoly f =
      toMvPoly (mAdd ((qs.zip divs).foldl (fun acc (q, d) => mAdd acc (mMul q d)) #[]) r) := by
    rw [← toMvPoly_simplify]; exact toMvPoly_congr hid
  rw [hid', toMvPoly_add, ← quotientSum_foldl_eq qs divs hsize]

-- ── §9.5  Auxiliary lemmas for toMvPoly_mvDiv_remainder ─────────────────────

/-- If `leadTerm p = none` then `toMvPoly p = 0`:
the max-fold over `simplify p` is `none` only when `simplify p = #[]`. -/
private lemma leadTerm_none_toMvPoly_zero {p : MPoly n} (h : leadTerm p = none) :
    toMvPoly p = 0 := by
  rw [← toMvPoly_simplify, leadTerm_eq_none_iff.mp h]
  exact toMvPoly_empty

/-- Exponents in `(arr.filter f).toList` are a subset of exponents in `arr.toList`. -/
private lemma filter_toList_map_snd_subset {n : Nat} (arr : MPoly n)
    (f : Rat × Exp n → Bool) :
    (arr.filter f).toList.map Prod.snd ⊆ arr.toList.map Prod.snd := by
  intro e he
  rw [List.mem_map] at he ⊢
  obtain ⟨t, ht, hte⟩ := he
  refine ⟨t, ?_, hte⟩
  simp only [Array.mem_toList_iff, Array.mem_filter] at ht ⊢
  exact ht.1

/-- Exponents accumulated by `foldl mergeStep'` are a subset of the initial acc's
exponents plus the list's exponents. -/
private lemma foldl_mergeStep_snd_subset {n : Nat} (l : List (Rat × Exp n)) :
    ∀ (acc : MPoly n),
    (l.foldl (mergeStep' n) acc).toList.map Prod.snd ⊆
    acc.toList.map Prod.snd ++ l.map Prod.snd := by
  induction l with
  | nil => intro acc; simp
  | cons hd tl ih =>
    obtain ⟨c, e⟩ := hd
    intro acc
    simp only [List.foldl_cons, List.map_cons]
    apply List.Subset.trans (ih (mergeStep' n acc (c, e)))
    have hstep_snd : (mergeStep' n acc (c, e)).toList.map Prod.snd ⊆
        acc.toList.map Prod.snd ++ [e] := by
      rcases h : acc.findIdx? (fun (_, f) => f == e) with _ | i
      · have hstep : mergeStep' n acc (c, e) = acc.push (c, e) := by
          simp [mergeStep', h]
        rw [hstep, Array.toList_push, List.map_append, List.map_singleton]
        exact fun x hx => hx
      · have heq : (mergeStep' n acc (c, e)).toList.map Prod.snd =
            acc.toList.map Prod.snd := by
          have hstep : mergeStep' n acc (c, e) =
              acc.mapIdx fun j t => if j == i then (t.1 + c, t.2) else t := by
            simp [mergeStep', h]
          rw [hstep]; exact mapIdx_update_snd acc i c
        rw [heq]; exact List.subset_append_left _ _
    intro x hx
    rw [List.mem_append] at hx
    rw [List.mem_append, List.mem_cons]
    rcases hx with hx | hx
    · rcases List.mem_append.mp (hstep_snd hx) with hmem | hmem
      · exact Or.inl hmem
      · exact Or.inr (Or.inl (List.mem_singleton.mp hmem))
    · exact Or.inr (Or.inr hx)

/-- Exponents in `simplify p` are a subset of exponents in the original `p`. -/
private lemma simplify_snd_subset {n : Nat} (p : MPoly n) :
    (simplify p).toList.map Prod.snd ⊆ p.toList.map Prod.snd := by
  rw [simplify_eq']
  apply List.Subset.trans (filter_toList_map_snd_subset _ _)
  have h := foldl_mergeStep_snd_subset p.toList #[]
  simp only [List.map_nil, List.nil_append] at h
  exact h

/-- Remainder bridge: no term of the remainder is divisible by any leading monomial
of the divisors, transferred to the MvPolynomial statement used in poly_division.
Follows from `mvDiv_remainder_reduced` + `leadTerm_degree`.
Requires the divisor to be nonzero (zero divisors have `degree 0 ≤ c` trivially). -/
theorem toMvPoly_mvDiv_remainder (f : MPoly n) (divs : Array (MPoly n)) :
    let (_, r) := mvDiv f divs
    ∀ c ∈ (toMvPoly r).support, ∀ i < divs.size,
      toMvPoly (divs[i]!) ≠ 0 →
      ¬ ((grlexMonomialOrder n).degree (toMvPoly (divs[i]!)) ≤ c) := by
  obtain ⟨qs, r, hqr⟩ : ∃ qs r, mvDiv f divs = (qs, r) := ⟨_, _, rfl⟩
  simp only [hqr]
  intro c hc i hi hdi hdeg
  -- Extract leadTerm since divs[i]! ≠ 0
  have hlt_opt : leadTerm (divs[i]!) ≠ none :=
    fun h => hdi (leadTerm_none_toMvPoly_zero h)
  obtain ⟨cf, ef, hlt⟩ : ∃ cf ef, leadTerm (divs[i]!) = some (cf, ef) := by
    rcases hlt : leadTerm (divs[i]!) with _ | ⟨cf, ef⟩
    · exact absurd hlt hlt_opt
    · exact ⟨cf, ef, rfl⟩
  -- hdeg : expToFinsupp ef ≤ c (pointwise Finsupp order)
  rw [leadTerm_degree hlt] at hdeg
  -- Find a term in (simplify r).toList with exponent c
  obtain ⟨⟨c', e'⟩, hmem_simp, heq⟩ := support_toMvPoly_mem r c hc
  -- heq : expToFinsupp e' = c, so expToFinsupp ef ≤ expToFinsupp e' pointwise
  have hdeg_le : expToFinsupp ef ≤ expToFinsupp e' := heq ▸ hdeg
  -- Translate to expDivides
  have hexpDiv : expDivides ef e' = true := by
    rw [expDivides_iff_forall_le]
    intro j
    by_cases hj_supp : j ∈ (expToFinsupp ef).support
    · have hle := (Finsupp.le_iff _ _).mp hdeg_le j hj_supp
      simp only [expToFinsupp_apply] at hle
      exact hle
    · rw [Finsupp.mem_support_iff, expToFinsupp_apply] at hj_supp
      simp only [ne_eq, not_not] at hj_supp
      rw [hj_supp]; exact Nat.zero_le _
  -- Lift the term from (simplify r) to r.toList
  obtain ⟨d, hd_mem⟩ : ∃ d : Rat, (d, e') ∈ r.toList := by
    have he'_in : e' ∈ (simplify r).toList.map Prod.snd :=
      List.mem_map.mpr ⟨(c', e'), hmem_simp, rfl⟩
    obtain ⟨t, ht, hte⟩ := List.mem_map.mp (simplify_snd_subset r he'_in)
    exact ⟨t.1, (Prod.ext rfl hte : t = (t.1, e')) ▸ ht⟩
  -- Apply mvDiv_remainder_reduced to get contradiction
  have hred := mvDiv_remainder_reduced f divs
  simp only [hqr] at hred
  have hred_i := hred (d, e') hd_mem i hi
  -- hred_i : (leadTerm divs[i]!).any (fun (_, de) => expDivides de e') = false
  -- Simplify using hlt and unfold Option.any for the `some` case
  simp only [hlt, Option.any] at hred_i
  -- hred_i : expDivides ef e' = false
  rw [hexpDiv] at hred_i
  exact absurd hred_i (by decide)
