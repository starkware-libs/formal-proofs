/-
The only thing that is relevant to soundness is that a UInt32Expr is represented by two felts.
-/

structure UInt32Expr where
  high : FeltExpr
  low : FeltExpr
