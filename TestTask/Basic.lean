import Mathlib.Data.Finmap

inductive IntExpr: Type where
| const: Int → IntExpr
| ite: Bool → IntExpr → IntExpr → IntExpr
| val: String → IntExpr
| add: IntExpr → IntExpr → IntExpr
| sub: IntExpr → IntExpr → IntExpr
| mul: IntExpr → IntExpr → IntExpr
deriving Repr, Inhabited

def basicExpr := IntExpr.add (IntExpr.const 3) (IntExpr.val "sp")

#eval basicExpr

abbrev VarMap := Finmap (α := String) (fun _ => Int)

variable {vars: VarMap}

@[reducible]
def eval: IntExpr → Option Int
| .const α => do pure α
| .ite cond thn els => if cond then eval thn else eval els
| .val s => vars.lookup s
| .add e₁ e₂ => do
  let l ← eval e₁
  let r ← eval e₂
  pure (l + r)
| .sub e₁ e₂ => do
  let l ← eval e₁
  let r ← eval e₂
  pure (l - r)
| .mul e₁ e₂ => do
  let l ← eval e₁
  let r ← eval e₂
  pure (l * r)

#eval eval (vars := List.toFinmap []) basicExpr
#eval eval (vars := List.toFinmap [⟨"sp", 3⟩]) basicExpr


def IntExprMeasure: IntExpr → Nat
| .const _ => 1
| .ite _ thn els => IntExprMeasure thn + IntExprMeasure els + 1
| .add e₁ e₂ => IntExprMeasure e₁ + IntExprMeasure e₂ + 1
| .sub e₁ e₂ => IntExprMeasure e₁ + IntExprMeasure e₂ + 1
| .mul e₁ e₂ => IntExprMeasure e₁ + IntExprMeasure e₂ + 1
| .val _ => 2

theorem pos_measure (exp: IntExpr): 0 < IntExprMeasure exp := by
  induction exp <;> simp [IntExprMeasure]

set_option linter.unusedVariables false in
mutual
  def stepBinOp
  (constr: IntExpr → IntExpr → IntExpr)
  (fn: Int → Int → Int) (x y: IntExpr)
  (h_constr: ∀ x y, IntExprMeasure (constr x y) = IntExprMeasure x + IntExprMeasure y + 1): Option IntExpr :=
  match x, y with
  | .const val₁, .const val₂ => some (.const (fn val₁ val₂))
  | .const val, e₂ => do
    let r ← step e₂
    pure (constr (.const val) r)
  | e₁, e₂ => do
    let l ← step e₁
    pure (constr l e₂)
  termination_by (IntExprMeasure (constr x y) - 1)
  decreasing_by (
    simp [h_constr, IntExprMeasure]
    simp [h_constr]
    apply pos_measure)

  def step (expr: IntExpr): Option IntExpr := match expr with
  | .const α => some (.const α)
  | .ite cond thn els => if cond then thn else els
  | .add e₁ e₂ => stepBinOp (.add) (fun x y => x + y) e₁ e₂ (by simp [IntExprMeasure])
  | .sub e₁ e₂ => stepBinOp (.sub) (fun x y => x - y) e₁ e₂ (by simp [IntExprMeasure])
  | .mul e₁ e₂ => stepBinOp (.mul) (fun x y => x * y) e₁ e₂ (by simp [IntExprMeasure])
  | .val s =>
    match vars.lookup s with
    | some val => some (.const val)
    | none => none
  termination_by (IntExprMeasure expr)
  decreasing_by (all_goals simp [IntExprMeasure])
end

#eval step basicExpr (vars := List.toFinmap [])
#eval step basicExpr (vars := List.toFinmap [⟨"sp", 3⟩])

def step_iter (exp: IntExpr): Nat → Option IntExpr
| 0 => exp
| .succ n => do
  let inner ← step exp (vars := vars)
  let outer ← step_iter inner n
  pure outer

theorem step_iter_add (exp: IntExpr) (k n: Nat):
  step_iter exp (k + n) (vars := vars) =
  (do
    let inner ← step_iter exp (vars := vars) n
    let outer ← step_iter inner (vars := vars) k
    pure outer) := by
  induction n generalizing exp with
  | zero => simp [step_iter]
  | succ k ih =>
    simp [step_iter, Option.bind]
    aesop

theorem decreasing_measure:
  (∀ α, exp ≠ IntExpr.const α) → (
    (do
      let res ← step exp (vars := vars)
      pure (IntExprMeasure res)) < (some (IntExprMeasure exp))) := by
  intro hexp
  induction exp
  all_goals try {
    simp [step, stepBinOp.eq_def, IntExprMeasure] at *
    split
    { simp [Option.bind, IntExprMeasure] }
    { rename_i xih x y val xh yh
      have xih_res := xih yh
      simp [Option.bind, IntExprMeasure] at *
      split at xih_res
      { simp [*] }
      simp [*, IntExprMeasure] at *
      exact xih_res }
    { rename_i xih yih x y xh yh
      have xih_res := xih xh
      simp [Option.bind] at *
      split at xih_res
      { simp [*] }
      simp [*, IntExprMeasure] at *
      exact xih_res }
  }
  { simp at hexp }
  { simp [step, IntExprMeasure, Option.bind] at *
    split_ifs with hite <;> simp <;> omega }
  simp [step, IntExprMeasure] at *
  simp [Option.bind]
  split
  { simp }
  rename_i heq
  split at heq
  simp at heq
  simp [←heq, IntExprMeasure]
  simp at heq

set_option maxHeartbeats 1000000

theorem step_preserves_eval:
  (do
    let res ← step exp (vars := vars)
    let eval_res ← eval res (vars := vars)
    pure eval_res) = eval exp (vars := vars) := by
  induction exp
  { simp [step, eval, Option.bind] }
  { rename_i x y xih yih
    simp only [eval]
    simp [step]
    split <;> simp [Option.bind] }
  { simp [eval, Option.bind, step]
    split <;> aesop
    simp [eval] at heq_1
    simp [heq_1] }
  all_goals try {
    rename_i x y xih yih
    simp only [eval]
    simp [step, stepBinOp.eq_def]
    split
    { simp [Option.bind, eval] }
    { simp [Option.bind]
      simp [Option.bind] at yih
      rw [←yih]
      aesop }
    simp [Option.bind] at *
    rw [←yih, ←xih]
    aesop
    all_goals simp [eval, Option.bind]
    { simp [heq, ←yih] }
    { simp [heq, ←yih] }
    { simp [heq_2, ←yih] }
    { simp [heq_2, ←yih] }
    { simp [heq_2, ←yih] }
    { simp [heq, heq_2] }
    { simp [heq_3, heq_2] }
    { simp [heq_3, heq_2] } }

theorem step_none_eq_eval_none (exp: IntExpr):
  step exp (vars := vars) = none → eval exp (vars := vars) = none := by
    induction exp <;> intro hnone
    all_goals {
      simp [step, stepBinOp.eq_def, Option.bind, eval] at *
      try aesop
    }

omit vars in
theorem small_step_eval_bound (exp: IntExpr):
∀ svars: VarMap,
∀ k, IntExprMeasure exp ≤ k + 1 → step_iter exp k (vars := svars) = (do let res ← eval exp (vars := svars); pure (.const res)) := by
  intro vars k hk
  induction k generalizing exp
  { simp at hk
    cases exp
    { simp [step_iter, eval] }
    all_goals try {
      rename_i a₁
      simp [IntExprMeasure] at hk
      have lemm := pos_measure a₁
      omega }
    simp [IntExprMeasure] at hk }
  rename_i n ih
  rw [step_iter]
  by_cases const: ∃ α, exp = .const α
  { rcases const with ⟨α, hconst⟩
    have ih_const := ih exp (by simp [hconst, IntExprMeasure])
    simp [Option.bind, hconst, step] at *
    simp [ih_const] }
  by_cases sh: ∃ exp₁, step exp (vars := vars) = some exp₁
  { rcases sh with ⟨exp₁, sh⟩
    have dec_measure := decreasing_measure (exp := exp) (vars := vars) (by aesop)
    simp [Option.bind, sh] at dec_measure
    have ih_exp := ih (exp₁) (by omega)
    simp [Option.bind, sh, ih_exp]
    have preservation := step_preserves_eval (exp := exp) (vars := vars)
    simp [sh] at preservation
    simp [←preservation]
    by_cases heval: ∃ ev, eval exp₁ (vars := vars) = some ev
    { rcases heval with ⟨ev, heval⟩
      simp [heval] }
    simp [←Option.eq_none_iff_forall_ne_some] at heval
    simp [heval] }
  simp at *
  rw [←Option.eq_none_iff_forall_ne_some] at sh
  simp [Option.bind, sh]
  simp [step_none_eq_eval_none exp sh]

omit vars in
theorem small_step_eval_seq (exp: IntExpr):
∀ svars: VarMap,
∃ seq: List (Option IntExpr),
1 ≤ seq.length ∧
seq[0]! = exp ∧
seq.getLast! = (do let evalRes ← eval exp (vars := svars); pure (.const evalRes)) ∧
∀ i < seq.length - 1,
  seq[i + 1]! =
    (do
      let preSeq ← seq[i]!
      let preRes ← step preSeq (vars := svars)
      pure preRes) := by
  intro vars
  exists (List.range (IntExprMeasure exp)).map (step_iter exp (vars := vars))
  have := pos_measure exp
  repeat' constructor
  { simp; omega }
  { simp
    rw [List.getElem?_eq_getElem]
    simp
    rw [List.getElem_range]
    { simp [step_iter] }
    simp [this] }
  { simp
    rw [List.getLast?_eq_getLast]
    simp
    rw [List.getLast_range]
    apply small_step_eval_bound
    omega
    simp
    omega }
  intro i hi
  simp at hi
  simp
  repeat rw [List.getElem?_eq_getElem]
  simp
  repeat rw [List.getElem_range]
  { rw [step_iter]
    have := step_iter_add exp 1 i (vars := vars)
    simp [step_iter] at this
    rw [←this, Nat.add_comm]
    simp [step_iter] }
  { simp; omega }
  simp; omega
