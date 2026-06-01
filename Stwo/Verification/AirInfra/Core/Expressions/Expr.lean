import Lean.Data.Json.FromToJson
import Verification.AirInfra.StwoProver
import Verification.AirInfra.Util
import Verification.AirInfra.Core.AirFnRegistry

/-
For now, there are two kinds of variables: state variables and intermediate variables.
-/

inductive VarIndex : Type where
  | stateVar (index : Nat) : VarIndex
  | intermediateVar (index : Nat) : VarIndex
deriving DecidableEq, Hashable, Repr, Lean.ToJson, Lean.FromJson

namespace VarIndex

def toVarName : VarIndex → String
  | stateVar index        => s!"col{index}"
  | intermediateVar index => s!"{INTERMEDIATE_VAR_PREFIX}{index}"

end VarIndex

/-
Binary operations.
-/

inductive BinaryOp where
  | add : BinaryOp
  | sub : BinaryOp
  | mul : BinaryOp
  | div : BinaryOp
  | and : BinaryOp
  | or : BinaryOp
deriving DecidableEq, Hashable, Repr, Lean.ToJson, Lean.FromJson

def BinaryOp.toStr : BinaryOp → String
  | BinaryOp.add => "+"
  | BinaryOp.sub => "-"
  | BinaryOp.mul => "*"
  | BinaryOp.div => "/"
  | BinaryOp.and => "&"
  | BinaryOp.or => "|"

inductive UnaryOp where
  | neg : UnaryOp
  | not : UnaryOp
  | inverse : UnaryOp
deriving DecidableEq, Hashable, Repr, Lean.ToJson, Lean.FromJson

def UnaryOp.toStr : UnaryOp → String
  | UnaryOp.neg => "-"
  | UnaryOp.not => "!"
  | UnaryOp.inverse => "inv:"

/-
Felt expressions
-/

inductive FeltExpr where
  | const (value : Felt) : FeltExpr
  | var (index : VarIndex) : FeltExpr
  | binary (op : BinaryOp) (left : FeltExpr) (right : FeltExpr) : FeltExpr
  | unary (op : UnaryOp) (child : FeltExpr) : FeltExpr
deriving DecidableEq, Hashable, Inhabited, Repr, Lean.ToJson, Lean.FromJson

def FeltExpr.toStr : FeltExpr → String
  | const n => toString n
  | var index => index.toVarName
  | binary op left right => "(" ++ left.toStr ++ " " ++ op.toStr ++ " " ++ right.toStr ++ ")"
  | unary op child => op.toStr ++ child.toStr

instance : ToString FeltExpr := ⟨FeltExpr.toStr⟩

instance : Add FeltExpr where
  add := FeltExpr.binary BinaryOp.add

instance : Sub FeltExpr where
  sub := FeltExpr.binary BinaryOp.sub

instance : Mul FeltExpr where
  mul := FeltExpr.binary BinaryOp.mul

instance : Div FeltExpr where
  div := FeltExpr.binary BinaryOp.div

instance : Neg FeltExpr where
  neg := FeltExpr.unary UnaryOp.neg

instance : AndOp FeltExpr where
  and := FeltExpr.binary BinaryOp.and

instance : OrOp FeltExpr where
  or := FeltExpr.binary BinaryOp.or

instance : Complement FeltExpr where
  complement := FeltExpr.unary UnaryOp.not


/-
Semantics.
-/

def VarAssign := VarIndex → Felt

namespace FeltExpr

variable [Fact (Nat.Prime Stwo.P)]

def eval (varAssign : VarAssign) : FeltExpr → Felt
  | const value => ↑value
  | var index => varAssign index
  | binary op left right =>
    let l := eval varAssign left
    let r := eval varAssign right
    match op with
    | BinaryOp.add => l + r
    | BinaryOp.sub => l - r
    | BinaryOp.mul => l * r
    | BinaryOp.div => l / r
    | BinaryOp.and => l &&& r
    | BinaryOp.or => l ||| r
  | unary op child =>
    let c := eval varAssign child
    match op with
    | UnaryOp.neg => -c
    | UnaryOp.not => ~~~c
    | UnaryOp.inverse => 1/c

@[simp] theorem eval_add (e1 e2 : FeltExpr) (varAssign : VarAssign) :
  (e1 + e2).eval varAssign = e1.eval varAssign + e2.eval varAssign := rfl

@[simp] theorem eval_sub (e1 e2 : FeltExpr) (varAssign : VarAssign) :
  (e1 - e2).eval varAssign = e1.eval varAssign - e2.eval varAssign := rfl

@[simp] theorem eval_mul (e1 e2 : FeltExpr) (varAssign : VarAssign) :
  (e1 * e2).eval varAssign = e1.eval varAssign * e2.eval varAssign := rfl

@[simp] theorem eval_div (e1 e2 : FeltExpr) (varAssign : VarAssign) :
  (e1 / e2).eval varAssign = e1.eval varAssign / e2.eval varAssign := rfl

@[simp] theorem eval_const (varAssign : VarAssign) (x : Felt) :
  (FeltExpr.const x).eval varAssign = x := rfl

end FeltExpr
