import Lean
import Qq
import MatchWhnf.MatchWhnf

open Lean Lean.Elab Lean.Parser.Term Syntax Meta Qq

set_option maxHeartbeats 2000000

axiom AND : Bool → Bool → Bool
axiom OR : Bool → Bool → Bool

axiom A : Bool
axiom B : Bool
axiom C : Bool
axiom D : Bool

noncomputable def E := OR A B
noncomputable def F := OR C D
noncomputable def G := AND E F

def match_whnfB(e: Expr)(iter: Nat): MetaM Bool := do
  let x ← IO.mkRef true
  let startT ← IO.monoNanosNow
  [:iter].forM fun _ => do
    match_whnf e with
    | Expr.app (Expr.app (Expr.const `AND []) (Expr.app (Expr.app (Expr.const `OR []) a) b)) (Expr.app (Expr.app (Expr.const `OR []) c) d) => x.set true
    | _ => x.set false
  let endT ← IO.monoNanosNow
  logInfo s!"{(endT - startT) / 1000000}"
  x.get

#eval match_whnfB (Expr.const `G []) 10000
#eval match_whnfB (Expr.const `G []) 100000
#eval match_whnfB (Expr.const `G []) 1000000


def qqB(e: Q(Bool))(iter: Nat): MetaM Bool := do
  let r ← IO.mkRef true
  let startT ← IO.monoNanosNow
  [:iter].forM fun _ => do
    match e with
    | ~q(AND (OR $a $b) (OR $c $d)) => r.set true
    | _ => r.set false
  let endT ← IO.monoNanosNow
  logInfo s!"{(endT - startT) / 1000000}"
  r.get

#eval qqB (Expr.const `G []) 10000
#eval qqB (Expr.const `G []) 100000
#eval qqB (Expr.const `G []) 1000000
