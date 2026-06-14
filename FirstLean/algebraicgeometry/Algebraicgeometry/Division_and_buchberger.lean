import Mathlib

abbrev Exp (n : Nat) := Fin n → Nat
abbrev MPoly (n : Nat) := Array (Rat × Exp n)

instance {n : Nat} : Inhabited (Exp n)         := ⟨fun _ => 0⟩
instance {n : Nat} : Inhabited (Rat × Exp n)   := ⟨(0, fun _ => 0)⟩
instance {n : Nat} : Inhabited (MPoly n)        := ⟨#[]⟩


def expDegAux : ∀ (n : Nat), (Fin n → Nat) → Nat
  | 0,   _  => 0
  | n+1, e  => e ⟨0, Nat.zero_lt_succ n⟩ + expDegAux n (fun i => e i.succ)

def expDeg {n : Nat} (e : Exp n) : Nat := expDegAux n e

private def expDividesAux : ∀ (n : Nat), (Fin n → Nat) → (Fin n → Nat) → Bool
  | 0,   _,  _  => true
  | n+1, a,  b  =>
    a ⟨0, Nat.zero_lt_succ n⟩ ≤ b ⟨0, Nat.zero_lt_succ n⟩ &&
    expDividesAux n (fun i => a i.succ) (fun i => b i.succ)

def expDivides {n : Nat} (a b : Exp n) : Bool := expDividesAux n a b

def expDiv {n : Nat} (a b : Exp n) : Exp n := fun i => a i - b i
def expMul {n : Nat} (a b : Exp n) : Exp n := fun i => a i + b i


-- If expDividesAux m a b = true then a i ≤ b i at every index
private theorem expDividesAux_le : ∀ (m : Nat) (a b : Fin m → Nat),
    expDividesAux m a b = true → ∀ i : Fin m, a i ≤ b i := by
  intro m
  induction m with
  | zero => intro a b _ i; exact i.elim0
  | succ m ih =>
    intro a b h i
    simp only [expDividesAux, Bool.and_eq_true, decide_eq_true_iff] at h
    obtain ⟨h0, htail⟩ := h
    cases i using Fin.cases with
    | zero    => exact h0
    | succ i' => exact ih _ _ htail i'

-- Converse
private theorem expDividesAux_true_of_le : ∀ (m : Nat) (a b : Fin m → Nat),
    (∀ i : Fin m, a i ≤ b i) → expDividesAux m a b = true := by
  intro m; induction m with
  | zero => intro a b _; rfl
  | succ m ih =>
    intro a b h
    simp only [expDividesAux, Bool.and_eq_true, decide_eq_true_iff]
    exact ⟨h ⟨0, Nat.zero_lt_succ m⟩, ih _ _ (fun i => h i.succ)⟩

-- Equivalence
theorem expDivides_iff_forall_le {n : Nat} (a b : Exp n) :
    expDivides a b = true ↔ ∀ i : Fin n, a i ≤ b i :=
  ⟨expDividesAux_le n a b, expDividesAux_true_of_le n a b⟩

-- expMul inverse of expDiv
theorem expMul_expDiv {n : Nat} (lExp dExp : Exp n) (h : expDivides dExp lExp = true) :
    expMul (expDiv lExp dExp) dExp = lExp := by
  funext i
  simp only [expMul, expDiv]
  apply Nat.sub_add_cancel
  exact expDividesAux_le n dExp lExp h i

-- Grlex: total degree first, then lex on components
def expLexLtAux : ∀ (n : Nat), (Fin n → Nat) → (Fin n → Nat) → Bool
  | 0,   _,  _  => false
  | n+1, a,  b  =>
    a ⟨0, Nat.zero_lt_succ n⟩ < b ⟨0, Nat.zero_lt_succ n⟩ ||
    (a ⟨0, Nat.zero_lt_succ n⟩ == b ⟨0, Nat.zero_lt_succ n⟩ &&
     expLexLtAux n (fun i => a i.succ) (fun i => b i.succ))

def expLexLt {n : Nat} (a b : Exp n) : Bool := expLexLtAux n a b

def expGrlexLt {n : Nat} (a b : Exp n) : Bool :=
  expDeg a < expDeg b || (expDeg a == expDeg b && expLexLt a b)

-- Component-wise equality for Exp n
private def expBEqAux : ∀ (n : Nat), (Fin n → Nat) → (Fin n → Nat) → Bool
  | 0,   _,  _  => true
  | n+1, a,  b  =>
    a ⟨0, Nat.zero_lt_succ n⟩ == b ⟨0, Nat.zero_lt_succ n⟩ &&
    expBEqAux n (fun i => a i.succ) (fun i => b i.succ)

instance {n : Nat} : BEq (Exp n) := ⟨expBEqAux n⟩

-- `==` on Exp n decides equality
private theorem expBEqAux_iff : ∀ (m : Nat) (a b : Fin m → Nat),
    expBEqAux m a b = true ↔ a = b := by sorry

instance {n : Nat} : LawfulBEq (Exp n) where
  eq_of_beq h := (expBEqAux_iff _ _ _).mp h
  rfl := (expBEqAux_iff _ _ _).mpr rfl

def monom {n : Nat} (c : Rat) (e : Exp n) : MPoly n :=
  if c == 0 then #[] else #[(c, e)]


def simplify {n : Nat} (p : MPoly n) : MPoly n :=
  let merged := p.foldl (fun acc (c, e) =>
    match acc.findIdx? (fun (_, f) => f == e) with
    | some i => acc.mapIdx fun j t => if j == i then (t.1 + c, t.2) else t
    | none   => acc.push (c, e)) #[]
  merged.filter (fun (c, _) => c != 0)

def leadTerm {n : Nat} (p : MPoly n) : Option (Rat × Exp n) :=
  (simplify p).foldl (fun best t =>
    match best with
    | none   => some t
    | some b => if expGrlexLt b.2 t.2 then some t else some b) none

def mAdd {n : Nat} (p q : MPoly n) : MPoly n := simplify (p ++ q)

def mSub {n : Nat} (p q : MPoly n) : MPoly n :=
  mAdd p (q.map fun (c, e) => (-c, e))

def mScale {n : Nat} (c : Rat) (e : Exp n) (p : MPoly n) : MPoly n :=
  p.map fun (d, f) => (c * d, expMul e f)

def mMul {n : Nat} (p q : MPoly n) : MPoly n :=
  simplify (p.flatMap fun (c, e) => mScale c e q)


def MPolyLt {n : Nat} (p q : MPoly n) : Prop :=
  match leadTerm q with
  | none          => False
  | some (_, leq) =>
    match leadTerm p with
    | none          => True
    | some (_, lep) => expGrlexLt lep leq = true


theorem expLexLt_irrefl : ∀ {n : Nat} (e : Exp n), expLexLt e e = false := by
  intro n
  induction n with
  | zero    => intro e; rfl
  | succ n ih =>
    intro e
    simp only [expLexLt, expLexLtAux, Nat.lt_irrefl, beq_self_eq_true, Bool.true_and]
    exact ih _

theorem expLexLt_trans : ∀ {n : Nat} {a b c : Exp n},
    expLexLt a b = true → expLexLt b c = true → expLexLt a c = true := by
  intro n
  induction n with
  | zero    => intro a b c h; simp [expLexLt, expLexLtAux] at h
  | succ n ih =>
    intro a b c hab hbc
    simp only [expLexLt, expLexLtAux, Bool.or_eq_true, Bool.and_eq_true,
               beq_iff_eq, decide_eq_true_iff] at *
    rcases hab with hab | ⟨hab, hab'⟩ <;> rcases hbc with hbc | ⟨hbc, hbc'⟩
    · left;  exact Nat.lt_trans hab hbc
    · left;  rw [← hbc]; exact hab
    · left;  rw [hab];   exact hbc
    · right; exact ⟨hab.trans hbc, ih hab' hbc'⟩

-- expLexLt on Exp n is well-founded
theorem expLexLt_wf {n : Nat} : WellFounded (fun a b : Exp n => expLexLt a b = true) := by
  induction n with
  | zero =>
    exact ⟨fun _ => Acc.intro _ fun _ h => by simp [expLexLt, expLexLtAux] at h⟩
  | succ n ih =>
    apply Subrelation.wf _
      (InvImage.wf (fun a : Exp (n + 1) =>
          (a ⟨0, Nat.zero_lt_succ n⟩, fun i : Fin n => a i.succ))
        (Prod.lex Nat.lt_wfRel ⟨_, ih⟩).wf)
    intro a b h
    simp only [expLexLt, expLexLtAux, Bool.or_eq_true, Bool.and_eq_true,
               beq_iff_eq, decide_eq_true_iff] at h
    rcases h with hab | ⟨heq, htail⟩
    · exact Prod.Lex.left _ _ hab
    · exact Prod.lex_def.mpr (Or.inr ⟨heq, htail⟩)

theorem expGrlexLt_irrefl {n : Nat} (e : Exp n) : expGrlexLt e e = false := by
  simp [expGrlexLt, expLexLt_irrefl]

theorem expGrlexLt_trans {n : Nat} {a b c : Exp n}
    (hab : expGrlexLt a b = true) (hbc : expGrlexLt b c = true) : expGrlexLt a c = true := by
  unfold expGrlexLt at *
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_iff] at *
  rcases hab with hdeg_ab | ⟨hdeg_ab, hlex_ab⟩ <;>
    rcases hbc with hdeg_bc | ⟨hdeg_bc, hlex_bc⟩
  · left;  exact Nat.lt_trans hdeg_ab hdeg_bc
  · left;  rw [← hdeg_bc]; exact hdeg_ab
  · left;  rw [hdeg_ab];   exact hdeg_bc
  · right; exact ⟨hdeg_ab.trans hdeg_bc, expLexLt_trans hlex_ab hlex_bc⟩

-- expGrlexLt is well-founded
theorem expGrlexLt_wf {n : Nat} : WellFounded (fun a b : Exp n => expGrlexLt a b = true) :=
  Subrelation.wf
    (fun {a b} h => by
      unfold expGrlexLt at h
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_iff] at h
      rcases h with hdeg | ⟨heq, hlex⟩
      · exact Prod.Lex.left _ _ hdeg
      · exact Prod.lex_def.mpr (Or.inr ⟨heq, hlex⟩))
    (InvImage.wf (fun e : Exp n => (expDeg e, e))
      (Prod.lex Nat.lt_wfRel ⟨_, expLexLt_wf⟩).wf)

-- Lex order is total: distinct exponents are always comparable.
private theorem expLexLtAux_total : ∀ (m : Nat) (a b : Fin m → Nat),
    a ≠ b → expLexLtAux m a b = true ∨ expLexLtAux m b a = true := by
  intro m
  induction m with
  | zero => intro a b h; exact absurd (funext fun i => i.elim0) h
  | succ m ih =>
    intro a b hab
    simp only [expLexLtAux, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_iff]
    rcases Nat.lt_trichotomy (a ⟨0, Nat.zero_lt_succ m⟩) (b ⟨0, Nat.zero_lt_succ m⟩) with h | h | h
    · exact Or.inl (Or.inl h)
    · have htail : (fun i : Fin m => a i.succ) ≠ (fun i : Fin m => b i.succ) := by
        intro heq; apply hab; funext i
        cases i using Fin.cases with
        | zero => exact h
        | succ i' => exact congrFun heq i'
      rcases ih (fun i => a i.succ) (fun i => b i.succ) htail with hlt | hlt
      · exact Or.inl (Or.inr ⟨h, hlt⟩)
      · exact Or.inr (Or.inr ⟨h.symm, hlt⟩)
    · exact Or.inr (Or.inl h)

theorem expLexLt_total {n : Nat} (a b : Exp n) (h : a ≠ b) :
    expLexLt a b = true ∨ expLexLt b a = true :=
  expLexLtAux_total n a b h

-- expDeg distributes over expMul
private theorem expDegAux_add : ∀ (m : Nat) (k a : Fin m → Nat),
    expDegAux m (fun i => k i + a i) = expDegAux m k + expDegAux m a := by
  intro m
  induction m with
  | zero => intro k a; simp [expDegAux]
  | succ m ih =>
    intro k a
    simp only [expDegAux]
    have := ih (fun i => k i.succ) (fun i => a i.succ)
    omega

theorem expDeg_expMul {n : Nat} (k a : Exp n) : expDeg (expMul k a) = expDeg k + expDeg a :=
  expDegAux_add n k a

-- Well-founded order on Option (Exp n): none is the minimum element.
private def optExpLt {n : Nat} : Option (Exp n) → Option (Exp n) → Prop
  | _,      none   => False
  | none,   some _ => True
  | some a, some b => expGrlexLt a b = true

private theorem optExpLt_wf {n : Nat} : WellFounded (@optExpLt n) :=
  WellFounded.intro fun oe =>
    match oe with
    | none   => Acc.intro none fun _ h => False.elim h
    | some e =>
        expGrlexLt_wf.induction (C := fun e => Acc optExpLt (some e)) e
          fun e' ih =>
            Acc.intro (some e') fun p h =>
              match p with
              | none     => Acc.intro none fun _ h' => False.elim h'
              | some e'' => ih e'' h

-- MPolyLt p q is equivalent to optExpLt on the leading exponents.
private theorem mPolyLt_iff_optExpLt {n : Nat} (p q : MPoly n) :
    MPolyLt p q ↔ optExpLt ((leadTerm p).map Prod.snd) ((leadTerm q).map Prod.snd) := by
  cases hq : leadTerm q with
  | none    => simp [MPolyLt, hq, optExpLt, Option.map]
  | some lq =>
    cases hp : leadTerm p with
    | none    => simp [MPolyLt, hq, hp, optExpLt, Option.map]
    | some lp => simp [MPolyLt, hq, hp, optExpLt, Option.map]

-- MPolyLt is well-founded: it is the InvImage of optExpLt_wf via the leading exponent map.
theorem mPolyLt_wf {n : Nat} : WellFounded (@MPolyLt n) :=
  Subrelation.wf (fun {p q} h => (mPolyLt_iff_optExpLt p q).mp h)
    (InvImage.wf (fun p : MPoly n => (leadTerm p).map Prod.snd) optExpLt_wf)

instance {n : Nat} : WellFoundedRelation (MPoly n) := ⟨MPolyLt, mPolyLt_wf⟩


theorem expGrlexLt_total_of_ne {n : Nat} {a b : Exp n} (h : a ≠ b) :
    expGrlexLt a b = true ∨ expGrlexLt b a = true := by sorry

theorem expGrlexLt_expMul_mono {n : Nat} (k : Exp n) {a b : Exp n}
    (h : expGrlexLt a b = true) : expGrlexLt (expMul k a) (expMul k b) = true := by sorry


/-- The merged coefficient of exponent `e` in `p`. -/
def coeffAt {n : Nat} (p : MPoly n) (e : Exp n) : Rat :=
  (p.toList.map fun t => if t.2 == e then t.1 else 0).sum

@[simp]
theorem coeffAt_empty {n : Nat} (e : Exp n) : coeffAt (#[] : MPoly n) e = 0 := rfl

-- `simplify` merges coefficients and drops zeros, so coefficients are unchanged.
@[simp]
theorem coeffAt_simplify {n : Nat} (p : MPoly n) (e : Exp n) :
    coeffAt (simplify p) e = coeffAt p e := by sorry

theorem coeffAt_append {n : Nat} (p q : MPoly n) (e : Exp n) :
    coeffAt (p ++ q) e = coeffAt p e + coeffAt q e := by sorry

theorem coeffAt_mAdd {n : Nat} (p q : MPoly n) (e : Exp n) :
    coeffAt (mAdd p q) e = coeffAt p e + coeffAt q e := by sorry

theorem coeffAt_neg {n : Nat} (p : MPoly n) (e : Exp n) :
    coeffAt (p.map fun (c, f) => (-c, f)) e = -coeffAt p e := by sorry

theorem coeffAt_mSub {n : Nat} (p q : MPoly n) (e : Exp n) :
    coeffAt (mSub p q) e = coeffAt p e - coeffAt q e := by sorry

theorem coeffAt_monom {n : Nat} (c : Rat) (k e : Exp n) :
    coeffAt (monom c k) e = if k == e then c else 0 := by sorry

-- mScale shifts exponents by k, so the coefficient at e comes from e − k (if k ∣ e).
theorem coeffAt_mScale {n : Nat} (c : Rat) (k : Exp n) (p : MPoly n) (e : Exp n) :
    coeffAt (mScale c k p) e =
    if expDivides k e then c * coeffAt p (expDiv e k) else 0 := by sorry

-- Convolution formula for products.
theorem coeffAt_mMul {n : Nat} (p q : MPoly n) (e : Exp n) :
    coeffAt (mMul p q) e =
    (p.toList.map fun t =>
      if expDivides t.2 e then t.1 * coeffAt q (expDiv e t.2) else 0).sum := by sorry

theorem coeffAt_mMul_mAdd_left {n : Nat} (p q d : MPoly n) (e : Exp n) :
    coeffAt (mMul (mAdd p q) d) e = coeffAt (mMul p d) e + coeffAt (mMul q d) e := by sorry


theorem simplify_snd_nodup {n : Nat} (p : MPoly n) :
    ((simplify p).toList.map Prod.snd).Nodup := by sorry

theorem coeffAt_of_mem_simplify {n : Nat} {p : MPoly n} {t : Rat × Exp n}
    (h : t ∈ (simplify p).toList) : coeffAt p t.2 = t.1 := by sorry

theorem mem_simplify_of_coeffAt_ne_zero {n : Nat} {p : MPoly n} {e : Exp n}
    (h : coeffAt p e ≠ 0) : (coeffAt p e, e) ∈ (simplify p).toList := by sorry

theorem exists_mem_of_coeffAt_ne_zero {n : Nat} {p : MPoly n} {e : Exp n}
    (h : coeffAt p e ≠ 0) : ∃ t ∈ p.toList, t.2 = e := by sorry


-- The leading coefficient is nonzero
theorem leadTerm_coeff_ne_zero {n : Nat} {p : MPoly n} {c : Rat} {e : Exp n}
    (h : leadTerm p = some (c, e)) : c ≠ 0 := by sorry

-- The leading term appears in the simplified polynomial.
theorem leadTerm_mem {n : Nat} {p : MPoly n} {c : Rat} {e : Exp n}
    (h : leadTerm p = some (c, e)) : (c, e) ∈ (simplify p).toList := by sorry

-- The leading exponent is ≥ every term
theorem leadTerm_is_max {n : Nat} {p : MPoly n} {c : Rat} {e : Exp n}
    (h : leadTerm p = some (c, e)) :
    ∀ t ∈ (simplify p).toList, expGrlexLt e t.2 = false := by sorry

theorem leadTerm_eq_none_iff {n : Nat} {p : MPoly n} :
    leadTerm p = none ↔ simplify p = #[] := by sorry


-- Scaling by a nonzero scalar c and exponent e shifts the leading term:
theorem leadTerm_mScale {n : Nat} {p : MPoly n} {dc : Rat} {de : Exp n}
    (hd : leadTerm p = some (dc, de)) {c : Rat} (hc : c ≠ 0) (e : Exp n) :
    leadTerm (mScale c e p) = some (c * dc, expMul e de) := by sorry

-- Subtracting the leading term (lc, le) from p leaves all terms strictly below le.
theorem mSub_lead_lt {n : Nat} {p : MPoly n} {lc : Rat} {le : Exp n}
    (h : leadTerm p = some (lc, le)) :
    ∀ t ∈ (simplify (mSub p #[(lc, le)])).toList, expGrlexLt t.2 le = true := by sorry

-- Division step: subtracting (lc/dc)·x^(le−de)·d from p leaves all terms strictly below le.
theorem mSub_scale_lead_lt {n : Nat} {p d : MPoly n} {lc dc : Rat} {le de : Exp n}
    (hp  : leadTerm p = some (lc, le))
    (hd  : leadTerm d = some (dc, de))
    (hdv : expDivides de le = true)
    (hdc : dc ≠ 0) :
    ∀ t ∈ (simplify (mSub p (mScale (lc / dc) (expDiv le de) d))).toList,
      expGrlexLt t.2 le = true := by sorry


-- Division step: LT(p - scale * d) <_grlex LT(p).
theorem loop_div_step {n : Nat}
    (p d : MPoly n) (lc dc : Rat) (le de : Exp n)
    (hp  : leadTerm p = some (lc, le))
    (hd  : leadTerm d = some (dc, de))
    (hdv : expDivides de le = true)
    (hdc : dc ≠ 0) :
    MPolyLt (mSub p (mMul (monom (lc / dc) (expDiv le de)) d)) p := by sorry

-- Remainder step: removing LT(p) makes the lead strictly smaller.
theorem loop_rem_step {n : Nat}
    (p : MPoly n) (lc : Rat) (le : Exp n)
    (hp : leadTerm p = some (lc, le)) :
    MPolyLt (mSub p (monom lc le)) p := by sorry


private def updateAt {n : Nat} (qs : Array (MPoly n)) (i : Nat) (v : MPoly n) :
    Array (MPoly n) :=
  qs.mapIdx fun j q => if j == i then mAdd q v else q

-- Division Algorithm
--     p   : polynomial still to divide
--     qs  : quotients so far (one per divisor)
--     r   : remainder so far
def divLoop {n : Nat} (divs : Array (MPoly n)) (p : MPoly n)
    (qs : Array (MPoly n)) (r : MPoly n) : Array (MPoly n) × MPoly n :=
  match hp : leadTerm p with
  | none => (qs, simplify r)
  | some (c, e) =>
    let divsWithIdx := divs.mapIdx (fun i f => (f, i))
    let found? := divsWithIdx.find? fun (f, _) =>
      match leadTerm f with
      | none         => false
      | some (_, ef) => expDivides ef e
    match hfound : found? with
    | none =>
      let t := monom c e
      divLoop divs (mSub p t) qs (mAdd r t)
    | some (f, i) =>
      match hf : leadTerm f with
      | none => divLoop divs p qs r
      | some (cf, ef) =>
        let t := monom (c / cf) (expDiv e ef)
        divLoop divs (mSub p (mMul t f)) (updateAt qs i t) r
termination_by p
decreasing_by
  · exact loop_rem_step p c e hp
  · exfalso
    have hpred := Array.find?_some hfound
    simp only [hf] at hpred
    exact Bool.false_ne_true hpred
  · have hdv : expDivides ef e = true := by
      have hpred := Array.find?_some hfound
      simp only [hf] at hpred
      exact hpred
    exact loop_div_step p f c cf e ef hp hf hdv (leadTerm_coeff_ne_zero hf)

def mvDiv {n : Nat} (f : MPoly n) (divs : Array (MPoly n)) : Array (MPoly n) × MPoly n :=
  let qs : Array (MPoly n) := (List.replicate divs.size #[]).toArray
  divLoop divs (simplify f) qs #[]


def mEquiv {n : Nat} (p q : MPoly n) : Prop := ∀ e, coeffAt p e = coeffAt q e


-- mAdd is commutative and associative
theorem mAdd_comm {n : Nat} (p q : MPoly n) : mEquiv (mAdd p q) (mAdd q p) := by sorry
theorem mAdd_assoc {n : Nat} (p q r : MPoly n) :
    mEquiv (mAdd (mAdd p q) r) (mAdd p (mAdd q r)) := by sorry

-- mMul distributes over mAdd on the left factor
theorem mMul_mAdd_left {n : Nat} (p q d : MPoly n) :
    mEquiv (mMul (mAdd p q) d) (mAdd (mMul p d) (mMul q d)) := by sorry

-- Remainder step identity: r + p = (r + t) + (p − t)
theorem mAdd_mSub_comm {n : Nat} (r p t : MPoly n) :
    mEquiv (mAdd r p) (mAdd (mAdd r t) (mSub p t)) := by sorry

-- Division step identity: qi·d + (r + p) = (qi + t)·d + r + (p − t·d)
theorem mMul_mAdd_cancel {n : Nat} (qi t d r p : MPoly n) :
    mEquiv (mAdd (mMul qi d) (mAdd r p))
           (mAdd (mMul (mAdd qi t) d) (mAdd r (mSub p (mMul t d)))) := by sorry

-- Loop invariant: f = (∑ qs[i] * divs[i]) + r + p throughout execution.
theorem divLoop_invariant {n : Nat}
    (divs : Array (MPoly n)) (f p : MPoly n) (qs : Array (MPoly n)) (r : MPoly n)
    (hsize : qs.size = divs.size)
    (hinv  : mEquiv (simplify f)
        (mAdd ((qs.zip divs).foldl (fun acc (q, d) => mAdd acc (mMul q d)) #[])
             (mAdd r p))) :
    let (qs', r') := divLoop divs p qs r
    mEquiv (simplify f)
        (mAdd ((qs'.zip divs).foldl (fun acc (q, d) => mAdd acc (mMul q d)) #[])
             r') := by sorry

-- Division identity: f = (∑ qᵢ * dᵢ) + r.
theorem mvDiv_identity {n : Nat} (f : MPoly n) (divs : Array (MPoly n)) :
    let (qs, r) := mvDiv f divs
    mEquiv (simplify f)
        (mAdd ((qs.zip divs).foldl (fun acc (q, d) => mAdd acc (mMul q d)) #[]) r) := by sorry

-- Remainder is fully reduced
theorem mvDiv_remainder_reduced {n : Nat} (f : MPoly n) (divs : Array (MPoly n)) :
    let (_, r) := mvDiv f divs
    ∀ t ∈ r.toList, ∀ i < divs.size,
      (leadTerm divs[i]!).any (fun (_, de) => expDivides de t.2) = false := by sorry

open MvPolynomial Set Ideal
open scoped MonomialOrder

namespace MonomialOrder

variable {σ : Type*} (m : MonomialOrder σ) {k : Type*} [Field k]

theorem division_algorithm {ι : Type*} (b : ι → MvPolynomial σ k)
    (hb : ∀ i, b i ≠ 0) (f : MvPolynomial σ k) :
    ∃ (q : ι →₀ MvPolynomial σ k) (r : MvPolynomial σ k),
      f = Finsupp.linearCombination _ b q + r ∧
      (∀ i, m.degree (b i * q i) ≼[m] m.degree f) ∧
      (∀ c ∈ r.support, ∀ i, ¬ m.degree (b i) ≤ c) :=
  m.div (fun i => m.isUnit_leadingCoeff.mpr (hb i)) f


/-- The **initial ideal** (leading term ideal) of `I` with respect to `m`:
the ideal generated by `{lterm(f) | f ∈ I}`. -/
noncomputable def initialIdeal (I : Ideal (MvPolynomial σ k)) :
    Ideal (MvPolynomial σ k) :=
  Ideal.span (m.leadingTerm '' (I : Set (MvPolynomial σ k)))

variable {m}

/-- The leading term of any `f ∈ I` lies in the initial ideal of `I`. -/
lemma leadingTerm_mem_initialIdeal {I : Ideal (MvPolynomial σ k)}
    {f : MvPolynomial σ k} (hf : f ∈ I) :
    m.leadingTerm f ∈ m.initialIdeal I :=
  Ideal.subset_span ⟨f, hf, rfl⟩

/-- The initial ideal is monotone. -/
lemma initialIdeal_mono {I J : Ideal (MvPolynomial σ k)} (h : I ≤ J) :
    m.initialIdeal I ≤ m.initialIdeal J :=
  Ideal.span_mono (Set.image_mono h)

/-- The span of leading terms of `G` embeds into the initial ideal of `Ideal.span G`. -/
lemma span_leadingTerms_le_initialIdeal (G : Set (MvPolynomial σ k)) :
    Ideal.span (m.leadingTerm '' G) ≤ m.initialIdeal (Ideal.span G) :=
  Ideal.span_mono (Set.image_mono Ideal.subset_span)


lemma span_leadingTerm_eq_span_leadingMonomial (G : Set (MvPolynomial σ k)) :
    Ideal.span (m.leadingTerm '' G) =
      Ideal.span ((fun s : σ →₀ ℕ => monomial s (1 : k)) ''
        (m.degree '' (G \ {0}))) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨g, hgG, rfl⟩
    simp only [SetLike.mem_coe]
    by_cases hg0 : g = 0
    · simp [hg0]
    · have heq : m.leadingTerm g = m.leadingCoeff g • monomial (m.degree g) (1 : k) := by
        simp [leadingTerm, smul_monomial]
      rw [heq, Algebra.smul_def]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span
        ⟨m.degree g, Set.mem_image_of_mem _ (by simp [hgG, hg0]), rfl⟩)
  · apply Ideal.span_le.mpr
    rintro _ ⟨d, hd, rfl⟩
    simp only [SetLike.mem_coe]
    obtain ⟨g, hg_diff, rfl⟩ := hd
    simp only [Set.mem_diff, Set.mem_singleton_iff] at hg_diff
    obtain ⟨hgG, hg0⟩ := hg_diff
    have heq : monomial (m.degree g) (1 : k) =
        (m.leadingCoeff g)⁻¹ • m.leadingTerm g := by
      simp [leadingTerm, smul_monomial,
            inv_mul_cancel₀ (m.leadingCoeff_ne_zero_iff.mpr hg0)]
    change monomial (m.degree g) (1 : k) ∈ Ideal.span (m.leadingTerm '' G)
    rw [heq, Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨g, hgG, rfl⟩)

private lemma linearCombination_eq_sum {ι : Type*} [Fintype ι]
    (b : ι → MvPolynomial σ k) (q : ι →₀ MvPolynomial σ k) :
    Finsupp.linearCombination (MvPolynomial σ k) b q = ∑ i, q i * b i := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (fun i => by simp)]
  simp [smul_eq_mul]

def IsGroebnerBasis (I : Ideal (MvPolynomial σ k))
    (G : Finset (MvPolynomial σ k)) : Prop :=
  (∀ g ∈ G, g ∈ I) ∧
  m.initialIdeal I = Ideal.span (m.leadingTerm '' (G : Set (MvPolynomial σ k)))

namespace IsGroebnerBasis

/-- Elements of a Gröbner basis lie in `I`. -/
lemma mem_ideal {I : Ideal (MvPolynomial σ k)} {G : Finset (MvPolynomial σ k)}
    (hG : m.IsGroebnerBasis I G) {g : MvPolynomial σ k} (hg : g ∈ G) : g ∈ I :=
  hG.1 g hg

/-- The initial ideal of `I` is spanned by the leading terms of `G`. -/
lemma initialIdeal_eq {I : Ideal (MvPolynomial σ k)} {G : Finset (MvPolynomial σ k)}
    (hG : m.IsGroebnerBasis I G) :
    m.initialIdeal I = Ideal.span (m.leadingTerm '' (G : Set (MvPolynomial σ k))) :=
  hG.2

/-- **Key property**: for every nonzero `f ∈ I`, some nonzero `g ∈ G` has
`m.degree g ≤ m.degree f`, i.e., `lm(g)` divides `lm(f)`. -/
theorem leadingDeg_dvd {I : Ideal (MvPolynomial σ k)} {G : Finset (MvPolynomial σ k)}
    (hG : m.IsGroebnerBasis I G) {f : MvPolynomial σ k}
    (hf : f ∈ I) (hf0 : f ≠ 0) :
    ∃ g ∈ G, g ≠ 0 ∧ m.degree g ≤ m.degree f := by
  have hlt_init : m.leadingTerm f ∈ m.initialIdeal I :=
    Ideal.subset_span ⟨f, hf, rfl⟩
  rw [hG.initialIdeal_eq, span_leadingTerm_eq_span_leadingMonomial] at hlt_init
  rw [mem_ideal_span_monomial_image] at hlt_init
  have hsupp : m.degree f ∈ (m.leadingTerm f).support := by
    classical
    simp [leadingTerm, support_monomial, m.leadingCoeff_ne_zero_iff.mpr hf0]
  obtain ⟨si, hsi_mem, hle⟩ := hlt_init (m.degree f) hsupp
  obtain ⟨g, hg_diff, hdeg⟩ := hsi_mem
  simp only [Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff] at hg_diff
  exact ⟨g, hg_diff.1, hg_diff.2, hdeg ▸ hle⟩

/-- A Gröbner basis generates `I` (requires all basis elements to be nonzero). -/
lemma span_eq {I : Ideal (MvPolynomial σ k)} {G : Finset (MvPolynomial σ k)}
    (hG : m.IsGroebnerBasis I G) (hG0 : ∀ g : G, (g : MvPolynomial σ k) ≠ 0) :
    Ideal.span (G : Set (MvPolynomial σ k)) = I := by
  apply le_antisymm (Ideal.span_le.mpr hG.1)
  intro f hf
  set b := fun g : G => (g : MvPolynomial σ k)
  obtain ⟨q, r, hfqr, _, hr⟩ := m.div (fun g : G => m.isUnit_leadingCoeff.mpr (hG0 g)) f
  have hsum_span : Finsupp.linearCombination _ b q ∈ Ideal.span (G : Set (MvPolynomial σ k)) := by
    rw [linearCombination_eq_sum]
    exact sum_mem (fun g _ => Ideal.mul_mem_left _ _ (Ideal.subset_span (Finset.mem_coe.mpr g.2)))
  have hG_le : Ideal.span (G : Set (MvPolynomial σ k)) ≤ I :=
    Ideal.span_le.mpr (fun g hg => hG.mem_ideal (Finset.mem_coe.mp hg))
  have hr_mem : r ∈ I := by
    have : r = f - Finsupp.linearCombination _ b q := by linear_combination -hfqr
    rw [this]; exact I.sub_mem hf (hG_le hsum_span)
  have hr0 : r = 0 := by
    by_contra hr0
    obtain ⟨g, hgG, -, hdvd⟩ := leadingDeg_dvd hG hr_mem hr0
    exact absurd hdvd (hr (m.degree r) (m.degree_mem_support hr0) ⟨g, hgG⟩)
  rw [hr0, add_zero] at hfqr; exact hfqr ▸ hsum_span

end IsGroebnerBasis


def ReducesToZero {ι : Type*} (b : ι → MvPolynomial σ k)
    (_ : ∀ i, b i ≠ 0) (f : MvPolynomial σ k) : Prop :=
  ∃ (q : ι →₀ MvPolynomial σ k),
    f = Finsupp.linearCombination _ b q ∧
    ∀ i, m.degree (b i * q i) ≼[m] m.degree f

lemma reducesToZero_zero {ι : Type*} (b : ι → MvPolynomial σ k)
    (hb : ∀ i, b i ≠ 0) : m.ReducesToZero b hb 0 :=
  ⟨0, by simp, by simp⟩

lemma mem_span_of_reducesToZero {ι : Type*} (b : ι → MvPolynomial σ k)
    (hb : ∀ i, b i ≠ 0) {f : MvPolynomial σ k}
    (hred : m.ReducesToZero b hb f) :
    f ∈ Ideal.span (Set.range b) := by
  obtain ⟨q, hq, _⟩ := hred
  rw [hq]
  simp only [Finsupp.linearCombination, Finsupp.lsum_apply, Finsupp.sum,
             LinearMap.smulRight_apply, LinearMap.id_coe, id]
  exact sum_mem (fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩))


theorem mem_ideal_iff_reducesToZero (I : Ideal (MvPolynomial σ k))
    (G : Finset (MvPolynomial σ k)) (hGbasis : m.IsGroebnerBasis I G)
    (hG0 : ∀ g : G, (g : MvPolynomial σ k) ≠ 0) (f : MvPolynomial σ k) :
    f ∈ I ↔ m.ReducesToZero (fun g : G => (g : MvPolynomial σ k)) hG0 f := by
  constructor
  ·
    intro hf
    set b := fun g : G => (g : MvPolynomial σ k)
    obtain ⟨q, r, hfqr, hdeg, hr⟩ := m.div (fun g : G => m.isUnit_leadingCoeff.mpr (hG0 g)) f
    have hG_le : Ideal.span (G : Set (MvPolynomial σ k)) ≤ I :=
      Ideal.span_le.mpr (fun g hg => hGbasis.mem_ideal (Finset.mem_coe.mp hg))
    have hsum_I : Finsupp.linearCombination _ b q ∈ I := hG_le (by
      rw [linearCombination_eq_sum]
      exact sum_mem (fun g _ => Ideal.mul_mem_left _ _ (Ideal.subset_span (Finset.mem_coe.mpr g.2))))
    have hr_mem : r ∈ I := by
      have : r = f - Finsupp.linearCombination _ b q := by linear_combination -hfqr
      rw [this]; exact I.sub_mem hf hsum_I
    have hr0 : r = 0 := by
      by_contra hr0
      obtain ⟨g, hgG, -, hdvd⟩ := hGbasis.leadingDeg_dvd hr_mem hr0
      exact absurd hdvd (hr (m.degree r) (m.degree_mem_support hr0) ⟨g, hgG⟩)
    rw [hr0, add_zero] at hfqr
    exact ⟨q, hfqr, hdeg⟩
  · intro ⟨q, hq, _⟩
    rw [hq]
    rw [linearCombination_eq_sum]
    exact sum_mem (fun g _ => Ideal.mul_mem_left _ _ (hGbasis.mem_ideal g.2))


-- The following section is completely done by AI

noncomputable def repDeg (m : MonomialOrder σ) {G : Finset (MvPolynomial σ k)}
    (μ : ↥G → MvPolynomial σ k) : m.syn :=
  Finset.univ.sup fun g : ↥G => m.toSyn (m.degree (μ g * g.val))

/-- The number `a` of summands of `μ` attaining the top syn-degree `repDeg μ`. -/
noncomputable def repCount (m : MonomialOrder σ) {G : Finset (MvPolynomial σ k)}
    (μ : ↥G → MvPolynomial σ k) : ℕ :=
  (Finset.univ.filter
    fun g : ↥G => m.toSyn (m.degree (μ g * g.val)) = repDeg m μ).card

variable {m : MonomialOrder σ}

/-- Every summand degree is `≤ repDeg`. -/
lemma le_repDeg {G : Finset (MvPolynomial σ k)} (μ : ↥G → MvPolynomial σ k) (g : ↥G) :
    m.toSyn (m.degree (μ g * g.val)) ≤ repDeg m μ :=
  Finset.le_sup (f := fun g : ↥G => m.toSyn (m.degree (μ g * g.val))) (Finset.mem_univ g)

/-- The whole representation has degree `≤ repDeg`. -/
lemma degree_le_repDeg {G : Finset (MvPolynomial σ k)} {f' : MvPolynomial σ k}
    {μ : ↥G → MvPolynomial σ k} (hf' : f' = ∑ g : ↥G, μ g * g.val) :
    m.toSyn (m.degree f') ≤ repDeg m μ :=
  hf' ▸ m.degree_sum_le.trans (Finset.sup_le fun g _ => le_repDeg μ g)

/-! ## Reusable helper lemmas (copied verbatim from `groebner.lean`, fully proved)

These are exactly the helpers the `(δ, a)` path still needs. Note we keep only the
*single-pair* reduction `sPolynomial_lterm_mul_reducesToLower`; the all-at-once
machinery (`sPolynomial_decomposition'`, `sum_sPolynomial_lterm_reductions`,
`degree_sum_lterms_lt_of_cancel`) is **not** needed here. -/

/-- Degree of a finite sum is `< δ` when every term is. -/
private lemma degree_sum_lt_of_forall_lt {ι : Type*} {s : Finset ι}
    {f : ι → MvPolynomial σ k} {δ : m.syn} (hδ : ⊥ < δ)
    (h : ∀ i ∈ s, m.toSyn (m.degree (f i)) < δ) :
    m.toSyn (m.degree (∑ i ∈ s, f i)) < δ :=
  lt_of_le_of_lt m.degree_sum_le ((Finset.sup_lt_iff hδ).mpr h)

/-- If `p * q` achieves syn-degree `δ` and `p, q ≠ 0`, then the tail `(p - LT p) * q`
has syn-degree `< δ`. -/
private lemma degree_tail_mul_lt_of_top_degree {p q : MvPolynomial σ k} {δ : m.syn}
    (hp : p ≠ 0) (hq : q ≠ 0) (hδ : ⊥ < δ)
    (hpq : m.toSyn (m.degree (p * q)) = δ) :
    m.toSyn (m.degree ((p - m.leadingTerm p) * q)) < δ := by
  by_cases htail : p - m.leadingTerm p = 0
  · simp only [htail, zero_mul, degree_zero, map_zero]
    rwa [← m.bot_eq_zero]
  · have hdeg_ne : m.degree p ≠ 0 := by
      intro h
      apply htail; apply sub_eq_zero_of_eq
      have hsupp : ∀ d ∈ p.support, d = 0 := fun d hd => by
        have hle := m.le_degree hd; rw [h] at hle
        exact m.toSyn.injective (le_antisymm hle (m.toSyn_monotone bot_le))
      haveI : DecidableEq σ := Classical.decEq σ
      ext d
      unfold MonomialOrder.leadingTerm MonomialOrder.leadingCoeff
      simp only [coeff_monomial, h]
      split_ifs with hd
      · exact congr_arg p.coeff hd.symm
      · exact Finsupp.notMem_support_iff.mp (fun hmem => hd (hsupp d hmem).symm)
    have hdeg_sum : m.toSyn (m.degree p) + m.toSyn (m.degree q) = δ := by
      rw [← m.toSyn.map_add, ← m.degree_mul hp hq]; exact hpq
    calc m.toSyn (m.degree ((p - m.leadingTerm p) * q))
        ≤ m.toSyn (m.degree (p - m.leadingTerm p)) + m.toSyn (m.degree q) :=
            m.toSyn_degree_mul_le
      _ < m.toSyn (m.degree p) + m.toSyn (m.degree q) :=
            add_lt_add_of_lt_of_le (m.degree_sub_leadingTerm_lt_degree hdeg_ne) le_rfl
      _ = δ := hdeg_sum

/-- A scalar multiple of `S(LT(μ b₁) * b₁, LT(μ b₂) * b₂)` decomposes as `∑_g ν g * g`
with every term of syn-degree `< δ`, using `hspoly` to reduce `S(b₁, b₂)` and
`sPolynomial_leadingTerm_mul` to shift degrees.

**This is the single-pair S-polynomial reduction the `(δ, a)` path is built on.** -/
private lemma sPolynomial_lterm_mul_reducesToLower (G : Finset (MvPolynomial σ k))
    (hG0 : ∀ g : ↥G, (g : MvPolynomial σ k) ≠ 0)
    (hspoly : ∀ g g' : ↥G,
        m.ReducesToZero (fun p : ↥G => (p : MvPolynomial σ k)) hG0 (m.sPolynomial g g'))
    {δ : m.syn} (hδ : ⊥ < δ) {μ' : ↥G → MvPolynomial σ k}
    (_hδ' : ∀ g : ↥G, m.toSyn (m.degree (μ' g * g.val)) ≤ δ)
    {b₁ b₂ : ↥G}
    (hb₁ : m.toSyn (m.degree (μ' b₁ * b₁.val)) = δ)
    (hb₂ : m.toSyn (m.degree (μ' b₂ * b₂.val)) = δ)
    (c : k) :
    ∃ ν : ↥G → MvPolynomial σ k,
      c • m.sPolynomial (m.leadingTerm (μ' b₁) * b₁.val) (m.leadingTerm (μ' b₂) * b₂.val) =
        ∑ g : ↥G, ν g * g.val ∧
      ∀ g : ↥G, m.toSyn (m.degree (ν g * g.val)) < δ := by
  by_cases hc : c = 0
  · exact ⟨fun _ => 0, by simp [hc], fun g => by simp; exact hδ⟩
  by_cases hS : m.sPolynomial b₁.val b₂.val = 0
  · have hSLT0 : m.sPolynomial (m.leadingTerm (μ' b₁) * b₁.val) (m.leadingTerm (μ' b₂) * b₂.val) = 0 :=
      by rw [m.sPolynomial_leadingTerm_mul, hS, mul_zero]
    exact ⟨fun _ => 0, by simp [hSLT0], fun g => by simp; exact hδ⟩
  have hμ₁ : μ' b₁ ≠ 0 := by
    intro h; simp only [h, zero_mul, degree_zero, map_zero, ← m.bot_eq_zero] at hb₁
    exact hδ.ne hb₁
  have hμ₂ : μ' b₂ ≠ 0 := by
    intro h; simp only [h, zero_mul, degree_zero, map_zero, ← m.bot_eq_zero] at hb₂
    exact hδ.ne hb₂
  obtain ⟨q, hq_eq, hq_deg⟩ := hspoly b₁ b₂
  have hq_sum : m.sPolynomial b₁.val b₂.val = ∑ g : ↥G, q g * g.val := by
    rw [hq_eq, Finsupp.linearCombination_apply,
      Finsupp.sum_fintype _ _ (fun i => by simp)]; simp [smul_eq_mul]
  have hcM_ne : m.leadingCoeff (μ' b₁) * m.leadingCoeff (μ' b₂) ≠ 0 :=
    mul_ne_zero (m.leadingCoeff_ne_zero_iff.mpr hμ₁) (m.leadingCoeff_ne_zero_iff.mpr hμ₂)
  set M := monomial
      ((m.degree (μ' b₁) + m.degree b₁.val) ⊔ (m.degree (μ' b₂) + m.degree b₂.val) -
       m.degree b₁.val ⊔ m.degree b₂.val)
      (m.leadingCoeff (μ' b₁) * m.leadingCoeff (μ' b₂))
  have hM_ne : M ≠ 0 := by
    simp only [M, Ne, monomial_eq_zero]; exact hcM_ne
  have hfactor : m.sPolynomial (m.leadingTerm (μ' b₁) * b₁.val) (m.leadingTerm (μ' b₂) * b₂.val) =
                 M * m.sPolynomial b₁.val b₂.val :=
    m.sPolynomial_leadingTerm_mul (μ' b₁) (μ' b₂) b₁.val b₂.val
  have hSLT_ne : m.sPolynomial (m.leadingTerm (μ' b₁) * b₁.val) (m.leadingTerm (μ' b₂) * b₂.val) ≠ 0 :=
    hfactor ▸ mul_ne_zero hM_ne hS
  have hLT₁_ne : m.leadingTerm (μ' b₁) ≠ 0 := by
    simp only [leadingTerm, ne_eq, monomial_eq_zero]
    exact m.leadingCoeff_ne_zero_iff.mpr hμ₁
  have hLT₂_ne : m.leadingTerm (μ' b₂) ≠ 0 := by
    simp only [leadingTerm, ne_eq, monomial_eq_zero]
    exact m.leadingCoeff_ne_zero_iff.mpr hμ₂
  have hdeg_LT₁ : m.toSyn (m.degree (m.leadingTerm (μ' b₁) * b₁.val)) = δ := by
    rw [m.degree_mul hLT₁_ne (hG0 b₁), m.toSyn.map_add, m.degree_leadingTerm,
        ← m.toSyn.map_add, ← m.degree_mul hμ₁ (hG0 b₁)]; exact hb₁
  have hdeg_LT₂ : m.toSyn (m.degree (m.leadingTerm (μ' b₂) * b₂.val)) = δ := by
    rw [m.degree_mul hLT₂_ne (hG0 b₂), m.toSyn.map_add, m.degree_leadingTerm,
        ← m.toSyn.map_add, ← m.degree_mul hμ₂ (hG0 b₂)]; exact hb₂
  have hdeg_eq : m.degree (m.leadingTerm (μ' b₁) * b₁.val) =
                 m.degree (m.leadingTerm (μ' b₂) * b₂.val) :=
    m.toSyn.injective (hdeg_LT₁.trans hdeg_LT₂.symm)
  have hSLT_lt : m.toSyn (m.degree (m.sPolynomial (m.leadingTerm (μ' b₁) * b₁.val)
                                                    (m.leadingTerm (μ' b₂) * b₂.val))) < δ := by
    have h := m.degree_sPolynomial_lt_sup_degree hSLT_ne
    rw [hdeg_eq, sup_idem, hdeg_LT₂] at h; exact h
  have hkey : m.toSyn (m.degree M) + m.toSyn (m.degree (m.sPolynomial b₁.val b₂.val)) < δ := by
    rw [← m.toSyn.map_add, ← m.degree_mul hM_ne hS, ← hfactor]; exact hSLT_lt
  refine ⟨fun g => c • M * q g, ?_, ?_⟩
  · rw [hfactor, hq_sum, ← smul_mul_assoc, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun g _ => (mul_assoc (c • M) (q g) g.val).symm)
  · intro g
    have hdeg_cM : m.toSyn (m.degree (c • M)) = m.toSyn (m.degree M) := by
      congr 1; simp only [M, smul_monomial, smul_eq_mul]
      classical
      simp only [m.degree_monomial, if_neg (mul_ne_zero hc hcM_ne), if_neg hcM_ne]
    calc m.toSyn (m.degree (c • M * q g * g.val))
        = m.toSyn (m.degree (c • M * (q g * g.val))) := by rw [mul_assoc]
      _ ≤ m.toSyn (m.degree (c • M)) + m.toSyn (m.degree (q g * g.val)) :=
            m.toSyn_degree_mul_le
      _ = m.toSyn (m.degree M) + m.toSyn (m.degree (q g * g.val)) := by rw [hdeg_cM]
      _ ≤ m.toSyn (m.degree M) + m.toSyn (m.degree (m.sPolynomial b₁.val b₂.val)) := by
            gcongr; rw [mul_comm]; exact hq_deg g
      _ < δ := hkey

/-! ## The two-term merge: the heart of the `(δ, a)` path

When the top monomial cancels (`deg f' < δ`), there are at least two top summands.
Pick two of them, `b₁ ≠ b₂`, and rewrite *that pair* via their S-polynomial. The
new representation has the same-or-smaller `δ`, and when `δ` is unchanged, strictly
fewer top summands — i.e. the measure `(δ, a)` strictly decreases. -/

/-- **Two-term boss lemma.** If the top monomial of `f' = ∑_g μ' g · g` cancels
(`toSyn (deg f') < repDeg μ'`), there is a new representation `μ''` of the *same*
`f'` whose lex measure `(repDeg, repCount)` is strictly smaller.

The construction: with `cᵢ = leadingCoeff (μ' bᵢ)`, the identity
`S(LT(μ'b₁)·b₁, LT(μ'b₂)·b₂) = (1/c₁)·LT(μ'b₁)·b₁ − (1/c₂)·LT(μ'b₂)·b₂`
lets us set
`μ'' g = μ' g + ν g + ⟦g = b₁⟧·(c₂/c₁)·LT(μ'b₁) − ⟦g = b₂⟧·LT(μ'b₂)`
where `∑ ν g · g = −c₂ · S(LT(μ'b₁)·b₁, LT(μ'b₂)·b₂)` has degree `< δ`
(via `sPolynomial_lterm_mul_reducesToLower`). Then `b₂` leaves the top set and
nothing new enters it. -/
private lemma exists_smaller_measure (G : Finset (MvPolynomial σ k))
    (hG0 : ∀ g : ↥G, (g : MvPolynomial σ k) ≠ 0)
    (hspoly : ∀ g g' : ↥G,
        m.ReducesToZero (fun p : ↥G => (p : MvPolynomial σ k)) hG0 (m.sPolynomial g g'))
    {f' : MvPolynomial σ k} {μ' : ↥G → MvPolynomial σ k}
    (hf' : f' = ∑ g : ↥G, μ' g * g.val)
    (hcancel : m.toSyn (m.degree f') < repDeg m μ') :
    ∃ μ'' : ↥G → MvPolynomial σ k,
      f' = ∑ g : ↥G, μ'' g * g.val ∧
      (repDeg m μ'' < repDeg m μ' ∨
        (repDeg m μ'' = repDeg m μ' ∧ repCount m μ'' < repCount m μ')) := by
  classical
  set δ := repDeg m μ' with hδdef
  have hδ_pos : ⊥ < δ := bot_le.trans_lt hcancel
  have hδ' : ∀ g : ↥G, m.toSyn (m.degree (μ' g * g.val)) ≤ δ := fun g => le_repDeg μ' g
  -- The top set `B`; by definition `repCount μ' = B.card`.
  set B : Finset ↥G :=
    Finset.univ.filter fun g : ↥G => m.toSyn (m.degree (μ' g * g.val)) = δ with hBdef
  have hcount_eq : repCount m μ' = B.card := rfl
  -- (1) `a ≥ 2`: the coefficient of `f'` at the top exponent is the sum of the top
  -- summands' leading coefficients; it is `0` (cancellation `deg f' < δ`), and a
  -- single nonzero leading term cannot sum to zero. Hence `1 < B.card`.
  have hB_two : 1 < B.card := by
    -- `univ` is nonempty (else the sup `δ` would be `⊥`).
    have huniv : (Finset.univ : Finset ↥G).Nonempty := by
      rcases Finset.eq_empty_or_nonempty (Finset.univ : Finset ↥G) with he | hne
      · exact absurd (by simpa only [hδdef, repDeg, he, Finset.sup_empty] using hδ_pos)
          (lt_irrefl _)
      · exact hne
    -- `δ` is attained by some summand `g₀`; let `D` be its exponent.
    obtain ⟨g₀, -, hg₀⟩ := Finset.exists_mem_eq_sup Finset.univ huniv
      (fun g : ↥G => m.toSyn (m.degree (μ' g * g.val)))
    have htop : m.toSyn (m.degree (μ' g₀ * g₀.val)) = δ := by
      rw [hδdef]; simp only [repDeg]; exact hg₀.symm
    set D := m.degree (μ' g₀ * g₀.val) with hDdef
    -- The coefficient of `f'` at `D` vanishes since `deg f' ≺ D`.
    have hfD : f'.coeff D = 0 := by
      apply m.coeff_eq_zero_of_lt
      show m.toSyn (m.degree f') < m.toSyn D
      rw [htop]; exact hcancel
    -- Expanding `f' = ∑ μ'g·g`, the coefficient at `D` is the sum over `g`.
    have hsum0 : ∑ g : ↥G, (μ' g * g.val).coeff D = 0 := by
      rw [← hfD, hf', coeff_sum]
    -- Off the top set, the coefficient at `D` is `0`; on it, it is a nonzero leading coeff.
    have hzero : ∀ g ∈ (Finset.univ : Finset ↥G), g ∉ B → (μ' g * g.val).coeff D = 0 := by
      intro g _ hgB
      apply m.coeff_eq_zero_of_lt
      show m.toSyn (m.degree (μ' g * g.val)) < m.toSyn D
      rw [htop]
      have hne : m.toSyn (m.degree (μ' g * g.val)) ≠ δ := fun h =>
        hgB (Finset.mem_filter.mpr ⟨Finset.mem_univ g, h⟩)
      exact lt_of_le_of_ne (hδ' g) hne
    have hlcB : ∀ g ∈ B, (μ' g * g.val).coeff D ≠ 0 := by
      intro g hg
      have hgδ : m.toSyn (m.degree (μ' g * g.val)) = δ := (Finset.mem_filter.mp hg).2
      have hgD : m.degree (μ' g * g.val) = D :=
        m.toSyn.injective (by rw [hgδ, htop])
      have hne : μ' g * g.val ≠ 0 := by
        intro h; rw [h, m.degree_zero, map_zero, ← m.bot_eq_zero] at hgδ
        exact hδ_pos.ne hgδ
      rw [← hgD]; exact m.coeff_degree_ne_zero_iff.mpr hne
    -- Hence the sum of leading coefficients over `B` is `0`.
    have hsumB0 : ∑ g ∈ B, (μ' g * g.val).coeff D = 0 := by
      rw [Finset.sum_subset (Finset.filter_subset _ Finset.univ) hzero]; exact hsum0
    -- `g₀ ∈ B`, so `B` is nonempty; if `B = {g₀}` the sum is a single nonzero term.
    have hg₀B : g₀ ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ g₀, htop⟩
    rcases lt_or_ge 1 B.card with h | h
    · exact h
    · exfalso
      have hB1 : B = {g₀} := Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hg₀B, fun x hx => Finset.card_le_one.mp h x hx g₀ hg₀B⟩
      rw [hB1, Finset.sum_singleton] at hsumB0
      exact hlcB g₀ hg₀B hsumB0
  -- (2) Extract two distinct top summands.
  obtain ⟨b₁, hb₁B, b₂, hb₂B, hbne⟩ := Finset.one_lt_card.mp hB_two
  have hb₁ : m.toSyn (m.degree (μ' b₁ * b₁.val)) = δ := (Finset.mem_filter.mp hb₁B).2
  have hb₂ : m.toSyn (m.degree (μ' b₂ * b₂.val)) = δ := (Finset.mem_filter.mp hb₂B).2
  have hμ₁ : μ' b₁ ≠ 0 := by
    intro h; simp only [h, zero_mul, degree_zero, map_zero, ← m.bot_eq_zero] at hb₁
    exact hδ_pos.ne hb₁
  have hμ₂ : μ' b₂ ≠ 0 := by
    intro h; simp only [h, zero_mul, degree_zero, map_zero, ← m.bot_eq_zero] at hb₂
    exact hδ_pos.ne hb₂
  -- The two top leading-term products `Lᵢ = LT(μ'bᵢ)·bᵢ` and their leading coeffs `Aᵢ`.
  set L₁ := m.leadingTerm (μ' b₁) * b₁.val with hL₁def
  set L₂ := m.leadingTerm (μ' b₂) * b₂.val with hL₂def
  have hLT₁_ne : m.leadingTerm (μ' b₁) ≠ 0 := by
    simp only [leadingTerm, ne_eq, monomial_eq_zero]; exact m.leadingCoeff_ne_zero_iff.mpr hμ₁
  have hLT₂_ne : m.leadingTerm (μ' b₂) ≠ 0 := by
    simp only [leadingTerm, ne_eq, monomial_eq_zero]; exact m.leadingCoeff_ne_zero_iff.mpr hμ₂
  have hL₁_ne : L₁ ≠ 0 := mul_ne_zero hLT₁_ne (hG0 b₁)
  have hL₂_ne : L₂ ≠ 0 := mul_ne_zero hLT₂_ne (hG0 b₂)
  set A₁ := m.leadingCoeff L₁ with hA₁def
  set A₂ := m.leadingCoeff L₂ with hA₂def
  have hA₁0 : A₁ ≠ 0 := m.leadingCoeff_ne_zero_iff.mpr hL₁_ne
  -- Both `Lᵢ` have syn-degree `δ`, hence equal exponent-degree.
  have hdeg_L₁ : m.toSyn (m.degree L₁) = δ := by
    rw [hL₁def, m.degree_mul hLT₁_ne (hG0 b₁), m.toSyn.map_add, m.degree_leadingTerm,
        ← m.toSyn.map_add, ← m.degree_mul hμ₁ (hG0 b₁)]; exact hb₁
  have hdeg_L₂ : m.toSyn (m.degree L₂) = δ := by
    rw [hL₂def, m.degree_mul hLT₂_ne (hG0 b₂), m.toSyn.map_add, m.degree_leadingTerm,
        ← m.toSyn.map_add, ← m.degree_mul hμ₂ (hG0 b₂)]; exact hb₂
  have hdeg_eq : m.degree L₁ = m.degree L₂ := m.toSyn.injective (hdeg_L₁.trans hdeg_L₂.symm)
  -- The two-term merge scalars.  (Note: the correct values involve the *leading
  -- coefficients of the products* `Lᵢ`, not just `lc (μ' bᵢ)`; the earlier sketch
  -- `c = -c₂, κ = c₂/c₁` is only valid for a monic basis.)
  set c : k := -A₁⁻¹ with hcdef
  set κ : k := A₁⁻¹ * A₂ with hκdef
  -- Closed form for the S-polynomial of the two leading-term products.
  have hS_eq : m.sPolynomial L₁ L₂ = A₂ • L₁ - A₁ • L₂ := by
    unfold MonomialOrder.sPolynomial
    rw [hdeg_eq, tsub_self, ← MvPolynomial.C_apply, ← MvPolynomial.C_apply,
        ← hA₁def, ← hA₂def, ← MvPolynomial.smul_eq_C_mul, ← MvPolynomial.smul_eq_C_mul]
  -- The merge identity:  `c • S(L₁, L₂) = L₂ − κ • L₁`.
  have hcA₁ : c * A₁ = -1 := by rw [hcdef, neg_mul, inv_mul_cancel₀ hA₁0]
  have hcA₂ : c * A₂ = -κ := by rw [hcdef, hκdef, neg_mul]
  have hmerge : c • m.sPolynomial L₁ L₂ = L₂ - κ • L₁ := by
    rw [hS_eq, smul_sub, smul_smul, smul_smul, hcA₁, hcA₂, neg_one_smul, neg_smul]; abel
  -- (3) Single-pair S-poly reduction with scalar `c`.
  obtain ⟨ν, hν_eq, hν_lt⟩ :=
    sPolynomial_lterm_mul_reducesToLower G hG0 hspoly hδ_pos hδ' hb₁ hb₂ c
  have hν_sum : ∑ g : ↥G, ν g * g.val = L₂ - κ • L₁ := by
    rw [← hν_eq, ← hL₁def, ← hL₂def]; exact hmerge
  -- (4) The new representation.
  set μ'' : ↥G → MvPolynomial σ k := fun g =>
      μ' g + ν g
        + (if g = b₁ then κ • m.leadingTerm (μ' b₁) else 0)
        - (if g = b₂ then m.leadingTerm (μ' b₂) else 0) with hμ''def
  -- The indicator sums collapse to the single shifted terms.
  have hind₁ : ∑ g : ↥G, (if g = b₁ then κ • m.leadingTerm (μ' b₁) else 0) * g.val = κ • L₁ := by
    rw [Finset.sum_eq_single b₁]
    · rw [if_pos rfl, smul_mul_assoc, ← hL₁def]
    · intro g _ hg; rw [if_neg hg, zero_mul]
    · intro h; exact absurd (Finset.mem_univ b₁) h
  have hind₂ : ∑ g : ↥G, (if g = b₂ then m.leadingTerm (μ' b₂) else 0) * g.val = L₂ := by
    rw [Finset.sum_eq_single b₂]
    · rw [if_pos rfl, ← hL₂def]
    · intro g _ hg; rw [if_neg hg, zero_mul]
    · intro h; exact absurd (Finset.mem_univ b₂) h
  refine ⟨μ'', ?_, ?_⟩
  · -- `f' = ∑_g μ'' g · g`:  the four extra terms cancel via the merge identity.
    symm
    calc ∑ g : ↥G, μ'' g * g.val
        = ∑ g : ↥G, (μ' g * g.val + ν g * g.val
            + (if g = b₁ then κ • m.leadingTerm (μ' b₁) else 0) * g.val
            - (if g = b₂ then m.leadingTerm (μ' b₂) else 0) * g.val) := by
          apply Finset.sum_congr rfl; intro g _
          have hbody : μ'' g = μ' g + ν g
              + (if g = b₁ then κ • m.leadingTerm (μ' b₁) else 0)
              - (if g = b₂ then m.leadingTerm (μ' b₂) else 0) := rfl
          rw [hbody]; ring
      _ = (∑ g : ↥G, μ' g * g.val) + (∑ g : ↥G, ν g * g.val)
            + (∑ g : ↥G, (if g = b₁ then κ • m.leadingTerm (μ' b₁) else 0) * g.val)
            - (∑ g : ↥G, (if g = b₂ then m.leadingTerm (μ' b₂) else 0) * g.val) := by
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ = (∑ g : ↥G, μ' g * g.val) + (∑ g : ↥G, ν g * g.val) + κ • L₁ - L₂ := by
          rw [hind₁, hind₂]
      _ = f' + (L₂ - κ • L₁) + κ • L₁ - L₂ := by rw [hν_sum, ← hf']
      _ = f' := by abel
  · -- The measure `(repDeg, repCount)` strictly decreases.
    -- `b₂` leaves the top set:  `μ'' b₂ = (μ' b₂ − LT(μ' b₂)) + ν b₂`, both `< δ`.
    have hb₂_lt : m.toSyn (m.degree (μ'' b₂ * b₂.val)) < δ := by
      have hb₂eq : μ'' b₂ = (μ' b₂ - m.leadingTerm (μ' b₂)) + ν b₂ := by
        have h0 : μ'' b₂ = μ' b₂ + ν b₂
            + (if b₂ = b₁ then κ • m.leadingTerm (μ' b₁) else 0)
            - (if b₂ = b₂ then m.leadingTerm (μ' b₂) else 0) := rfl
        rw [h0, if_neg (Ne.symm hbne), if_pos rfl, add_zero]; ring
      rw [hb₂eq, add_mul]
      refine lt_of_le_of_lt m.degree_add_le (sup_lt_iff.mpr ⟨?_, hν_lt b₂⟩)
      exact degree_tail_mul_lt_of_top_degree hμ₂ (hG0 b₂) hδ_pos hb₂
    -- `b₁` stays `≤ δ`:  adding `κ • LT(μ' b₁)` keeps the degree `≤ δ`.
    have hb₁_le : m.toSyn (m.degree (μ'' b₁ * b₁.val)) ≤ δ := by
      have hb₁eq : μ'' b₁ = μ' b₁ + ν b₁ + κ • m.leadingTerm (μ' b₁) := by
        have h0 : μ'' b₁ = μ' b₁ + ν b₁
            + (if b₁ = b₁ then κ • m.leadingTerm (μ' b₁) else 0)
            - (if b₁ = b₂ then m.leadingTerm (μ' b₂) else 0) := rfl
        rw [h0, if_pos rfl, if_neg hbne, sub_zero]
      rw [hb₁eq, add_mul, add_mul]
      refine le_trans m.degree_add_le
        (sup_le (le_trans m.degree_add_le (sup_le (hδ' b₁) (hν_lt b₁).le)) ?_)
      rw [smul_mul_assoc, ← hL₁def]
      exact le_trans m.degree_smul_le hdeg_L₁.le
    -- Off `{b₁, b₂}`:  `μ'' g = μ' g + ν g`.
    have hg_other : ∀ g : ↥G, g ≠ b₁ → g ≠ b₂ → μ'' g = μ' g + ν g := by
      intro g h1 h2
      have h0 : μ'' g = μ' g + ν g
          + (if g = b₁ then κ • m.leadingTerm (μ' b₁) else 0)
          - (if g = b₂ then m.leadingTerm (μ' b₂) else 0) := rfl
      rw [h0, if_neg h1, if_neg h2, add_zero, sub_zero]
    have hub : ∀ g : ↥G, m.toSyn (m.degree (μ'' g * g.val)) ≤ δ := by
      intro g
      by_cases hgb₂ : g = b₂
      · subst hgb₂; exact hb₂_lt.le
      by_cases hgb₁ : g = b₁
      · subst hgb₁; exact hb₁_le
      · rw [hg_other g hgb₁ hgb₂, add_mul]
        exact le_trans m.degree_add_le (sup_le (hδ' g) (hν_lt g).le)
    have hg_lt_of_notB : ∀ g : ↥G, g ∉ B → m.toSyn (m.degree (μ'' g * g.val)) < δ := by
      intro g hgB
      have hgb₁ : g ≠ b₁ := fun h => hgB (h ▸ hb₁B)
      have hgb₂ : g ≠ b₂ := fun h => hgB (h ▸ hb₂B)
      rw [hg_other g hgb₁ hgb₂, add_mul]
      refine lt_of_le_of_lt m.degree_add_le (sup_lt_iff.mpr ⟨?_, hν_lt g⟩)
      have hne : m.toSyn (m.degree (μ' g * g.val)) ≠ δ := fun h =>
        hgB (Finset.mem_filter.mpr ⟨Finset.mem_univ g, h⟩)
      exact lt_of_le_of_ne (hδ' g) hne
    have hrepDeg_le : repDeg m μ'' ≤ δ := Finset.sup_le (fun g _ => hub g)
    by_cases hlt : repDeg m μ'' < δ
    · exact Or.inl hlt
    · refine Or.inr ⟨le_antisymm hrepDeg_le (not_lt.mp hlt), ?_⟩
      have hrepDeg_eq : repDeg m μ'' = δ := le_antisymm hrepDeg_le (not_lt.mp hlt)
      rw [hcount_eq]
      show (Finset.univ.filter fun g : ↥G =>
          m.toSyn (m.degree (μ'' g * g.val)) = repDeg m μ'').card < B.card
      rw [hrepDeg_eq]
      refine lt_of_le_of_lt (Finset.card_le_card ?_) (Finset.card_erase_lt_of_mem hb₂B)
      intro g hg
      rw [Finset.mem_filter] at hg
      obtain ⟨_, hgδ⟩ := hg
      have hgnb₂ : g ≠ b₂ := by rintro rfl; exact absurd hgδ (ne_of_lt hb₂_lt)
      have hgB : g ∈ B := by
        by_contra hgB
        exact absurd hgδ (ne_of_lt (hg_lt_of_notB g hgB))
      exact Finset.mem_erase.mpr ⟨hgnb₂, hgB⟩

/-! ## The induction on the new lexicographic order

This is the structural payoff: a single well-founded induction on
`Prod.Lex (·<·) (·<·) : (m.syn × ℕ) → (m.syn × ℕ) → Prop`, with the measure
`(repDeg μ', repCount μ')`. Case A finishes immediately; Case B applies the boss
lemma and recurses. No `B = ∅` subcase is needed. -/

/-- The lex order on `m.syn × ℕ` is well-founded. -/
lemma wf_lex (m : MonomialOrder σ) :
    WellFounded (Prod.Lex (α := m.syn) (β := ℕ) (· < ·) (· < ·)) :=
  WellFounded.prod_lex m.wf.wf wellFounded_lt

/-- **Buchberger key lemma, `(δ, a)` version.** For any representation
`f' = ∑_g μ' g · g` with `f' ≠ 0`, some nonzero `g₀ ∈ G` has `deg g₀ ≤ deg f'`.

Proof by well-founded induction on the lex measure `(repDeg μ', repCount μ')`. -/
private lemma buchberger_key_lex (G : Finset (MvPolynomial σ k))
    (hG0 : ∀ g : ↥G, (g : MvPolynomial σ k) ≠ 0)
    (hspoly : ∀ g g' : ↥G,
        m.ReducesToZero (fun p : ↥G => (p : MvPolynomial σ k)) hG0 (m.sPolynomial g g')) :
    ∀ (f' : MvPolynomial σ k) (μ' : ↥G → MvPolynomial σ k),
      f' = ∑ g : ↥G, μ' g * g.val → f' ≠ 0 →
      ∃ si ∈ m.degree '' ((G : Set (MvPolynomial σ k)) \ {(0 : MvPolynomial σ k)}),
          si ≤ m.degree f' := by
  classical
  -- Generalize over the measure value `p` so we can induct on it.
  suffices H : ∀ p : m.syn × ℕ, ∀ (f' : MvPolynomial σ k) (μ' : ↥G → MvPolynomial σ k),
      f' = ∑ g : ↥G, μ' g * g.val → (repDeg m μ', repCount m μ') = p → f' ≠ 0 →
      ∃ si ∈ m.degree '' ((G : Set (MvPolynomial σ k)) \ {(0 : MvPolynomial σ k)}),
          si ≤ m.degree f' by
    exact fun f' μ' hf' h0 => H _ f' μ' hf' rfl h0
  intro p
  induction p using (wf_lex m).induction with
  | _ p ih =>
  intro f' μ' hf' hmeas hf'0
  -- `deg f' ≤ repDeg μ'` always; split on equality.
  have hf'le : m.toSyn (m.degree f') ≤ repDeg m μ' := degree_le_repDeg hf'
  by_cases hcaseA : m.toSyn (m.degree f') = repDeg m μ'
  · -- **Case A (survives).** The top monomial of `f'` is realized by some summand
    -- `g₀`, so `LM(g₀) ∣ LM(f')`.  (Same argument as `groebner.lean`'s Case A.)
    have hδ' : ∀ g : ↥G, m.toSyn (m.degree (μ' g * g.val)) ≤ repDeg m μ' :=
      fun g => le_repDeg μ' g
    have hcoeff : ∃ g₀ : ↥G, (μ' g₀ * g₀.val).coeff (m.degree f') ≠ 0 := by
      by_contra hall
      push Not at hall
      have hzero : f'.coeff (m.degree f') = 0 := by
        nth_rw 2 [hf']; rw [coeff_sum]
        exact Finset.sum_eq_zero (fun g _ => hall g)
      exact m.leadingCoeff_ne_zero_iff.mpr hf'0 hzero
    obtain ⟨g₀, hg₀coeff⟩ := hcoeff
    have hg₀supp : m.degree f' ∈ (μ' g₀ * g₀.val).support := mem_support_iff.mpr hg₀coeff
    have hle : m.toSyn (m.degree f') ≤ m.toSyn (m.degree (μ' g₀ * g₀.val)) :=
      m.le_degree hg₀supp
    have heqdeg : m.degree (μ' g₀ * g₀.val) = m.degree f' :=
      m.toSyn.injective (le_antisymm (hcaseA ▸ hδ' g₀) hle)
    have hg₀ne : (g₀.val : MvPolynomial σ k) ≠ 0 := by intro h; simp [h] at hg₀coeff
    have hμ₀ne : μ' g₀ ≠ 0 := by intro h; simp [h] at hg₀coeff
    refine ⟨m.degree g₀.val, ⟨g₀.val, ⟨Finset.mem_coe.mpr g₀.2, hg₀ne⟩, rfl⟩, ?_⟩
    calc m.degree g₀.val
        ≤ m.degree (μ' g₀) + m.degree g₀.val := by
              rw [Finsupp.le_iff]; intro i _
              simp only [Finsupp.add_apply]; exact Nat.le_add_left _ _
      _ = m.degree (μ' g₀ * g₀.val) := (m.degree_mul hμ₀ne hg₀ne).symm
      _ = m.degree f' := heqdeg
  · -- **Case B (cancels).** `deg f' < repDeg μ'`, so the boss lemma drops the measure.
    have hcancel : m.toSyn (m.degree f') < repDeg m μ' := lt_of_le_of_ne hf'le hcaseA
    obtain ⟨μ'', hμ''eq, hdec⟩ := exists_smaller_measure G hG0 hspoly hf' hcancel
    -- Repackage the disjunction as a strict step in the lex order.
    have hrel : Prod.Lex (α := m.syn) (β := ℕ) (· < ·) (· < ·)
        (repDeg m μ'', repCount m μ'') (repDeg m μ', repCount m μ') := by
      rcases hdec with hlt | ⟨heq, hcnt⟩
      · exact Prod.Lex.left _ _ hlt
      · rw [show repDeg m μ'' = repDeg m μ' from heq]; exact Prod.Lex.right _ hcnt
    exact ih (repDeg m μ'', repCount m μ'') (hmeas ▸ hrel) f' μ'' hμ''eq rfl hf'0

end MonomialOrder

-- End of AI section

def expLcm {n : Nat} (a b : Exp n) : Exp n := fun i => max (a i) (b i)

def sPoly {n : Nat} (f g : MPoly n) : MPoly n :=
  match leadTerm f, leadTerm g with
  | some (cf, ef), some (cg, eg) =>
    let γ := expLcm ef eg
    mSub (mScale (1/cf) (expDiv γ ef) f) (mScale (1/cg) (expDiv γ eg) g)
  | _, _ => #[]

partial def buchbergerLoop {n : Nat} (G : Array (MPoly n)) : Array (MPoly n) :=
  let pairs : List (Nat × Nat) :=
    (List.range G.size).flatMap fun i =>
      ((List.range G.size).filter (fun j => i < j)).map (fun j => (i, j))
  let new := pairs.foldl (fun acc (i, j) =>
    let r := (mvDiv (sPoly G[i]! G[j]!) (G ++ acc)).2
    if r.isEmpty then acc else acc.push r) (#[] : Array (MPoly n))
  if new.isEmpty then G else buchbergerLoop (G ++ new)

def buchberger {n : Nat} (F : Array (MPoly n)) : Array (MPoly n) :=
  buchbergerLoop ((F.map simplify).filter (fun p => !p.isEmpty))
