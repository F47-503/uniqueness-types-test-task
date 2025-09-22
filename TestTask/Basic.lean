import Aesop
import Mathlib.Order.WellFounded

inductive IntExpr: Type where
| const: Int → IntExpr
--| val: String → IntExpr
| add: IntExpr → IntExpr → IntExpr
| sub: IntExpr → IntExpr → IntExpr
| mul: IntExpr → IntExpr → IntExpr
deriving Repr, Inhabited

def basicExpr := IntExpr.add (IntExpr.const 3) (IntExpr.const 5)

#eval basicExpr

def eval: IntExpr → Int
| .const α => α
| .add e₁ e₂ => eval e₁ + eval e₂
| .sub e₁ e₂ => eval e₁ - eval e₂
| .mul e₁ e₂ => eval e₁ * eval e₂

#eval eval basicExpr


def IntExprMeasure: IntExpr → Nat
| .const _ => 1
| .add e₁ e₂ => IntExprMeasure e₁ + IntExprMeasure e₂ + 1
| .sub e₁ e₂ => IntExprMeasure e₁ + IntExprMeasure e₂ + 1
| .mul e₁ e₂ => IntExprMeasure e₁ + IntExprMeasure e₂ + 1

theorem pos_measure (exp: IntExpr): 0 < IntExprMeasure exp := by
  induction exp <;> simp [IntExprMeasure]

set_option linter.unusedVariables false in
mutual
  def stepBinOp
  (constr: IntExpr → IntExpr → IntExpr)
  (fn: Int → Int → Int) (x y: IntExpr)
  (h_constr: ∀ x y, IntExprMeasure (constr x y) = IntExprMeasure x + IntExprMeasure y + 1): IntExpr :=
  match x, y with
  | .const val₁, .const val₂ => .const (fn val₁ val₂)
  | .const val, e₂ => constr (.const val) (step e₂)
  | e₁, e₂ => constr (step e₁) e₂
  termination_by (IntExprMeasure (constr x y) - 1)
  decreasing_by (
    simp [h_constr, IntExprMeasure]
    simp [h_constr]
    apply pos_measure)

  def step (expr: IntExpr): IntExpr := match expr with
  | .const α => .const α
  | .add e₁ e₂ => stepBinOp (.add) (fun x y => x + y) e₁ e₂ (by simp [IntExprMeasure])
  | .sub e₁ e₂ => stepBinOp (.sub) (fun x y => x - y) e₁ e₂ (by simp [IntExprMeasure])
  | .mul e₁ e₂ => stepBinOp (.mul) (fun x y => x * y) e₁ e₂ (by simp [IntExprMeasure])
  termination_by (IntExprMeasure expr)
  decreasing_by (all_goals simp [IntExprMeasure])
end

#eval step basicExpr
#eval step (step basicExpr)

def step_iter (exp: IntExpr): Nat → IntExpr
| 0 => exp
| .succ n => step_iter (step exp) n

theorem step_iter_add (exp: IntExpr) (k n: Nat): step_iter exp (k + n) = step_iter (step_iter exp n) k := by
  induction n generalizing exp with
  | zero => simp [step_iter]
  | succ k ih =>
    simp [step_iter]
    rw [ih (step exp)]

theorem decreasing_measure:
  (∀ α, exp ≠ IntExpr.const α) → (IntExprMeasure (step exp) < IntExprMeasure exp) := by
  intro hexp
  induction exp
  { simp at hexp }
  all_goals {
    simp [step, stepBinOp.eq_def, IntExprMeasure]
    split
    all_goals try simp [IntExprMeasure]
    solve_by_elim
    solve_by_elim }

theorem step_preserves_eval:
  eval (step exp) = eval exp := by
  induction exp <;> simp [step, eval]
  all_goals {
    rw [stepBinOp.eq_def]
    split <;> simp [eval, *] }

theorem small_step_eval_bound (exp: IntExpr):
∀ k, IntExprMeasure exp ≤ k + 1 → step_iter exp k = .const (eval exp) := by
  intro k hk
  induction k generalizing exp
  { simp at hk
    cases exp
    { simp [step_iter, eval] }
    all_goals {
      rename_i a₁
      simp [IntExprMeasure] at hk
      have lemm := pos_measure a₁
      omega } }
  rename_i ih
  rw [step_iter, ih (step exp)]
  { simp
    apply step_preserves_eval  }
  by_cases hexp: ∀ α, exp ≠ IntExpr.const α
  { have := decreasing_measure hexp
    omega }
  simp at hexp
  let ⟨a, ha⟩ := hexp
  simp [ha, step, IntExprMeasure]


theorem small_step_eval_seq (exp: IntExpr):
∃ seq: List IntExpr,
1 ≤ seq.length ∧
seq[0]! = exp ∧
seq.getLast! = .const (eval exp) ∧
∀ i < seq.length - 1, seq[i + 1]! = step seq[i]! := by
  exists (List.range (IntExprMeasure exp)).map (step_iter exp)
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
  rw [List.getElem?_eq_getElem]
  rw [List.getElem?_eq_getElem]
  simp
  rw [List.getElem_range]
  { rw [List.getElem_range]
    { rw [step_iter]
      have := step_iter_add exp 1 i
      simp [step_iter] at this
      rw [←this, Nat.add_comm]
      simp [step_iter] }
    simp; omega }
  simp; omega
