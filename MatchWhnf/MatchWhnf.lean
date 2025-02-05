import Lean

open Lean Lean.Elab Lean.Parser.Term Syntax Meta

---

partial def matchApp: Term → Option (Term × Array Term)
| `(($t:term)) => matchApp t
| `(Expr.app $f:term $x:term) =>
  if let some (g, args) := matchApp f then
    some (g, args.push x)
  else
    none
| c@`(Expr.const $_:term $_:term) => some (c,#[])
| c@`($_:ident) => some (c,#[])
| c@`(_) => some (c,#[])
| _ => none

---

def mkMkApp(numArgs: Nat): MacroM Term := do
  if numArgs > 10 then
    Macro.throwError "Argument count not supported"
  if numArgs == 1 then
    return ← `($(mkIdent ``Lean.mkApp):ident)
  let mkA := "mkApp" ++ toString numArgs
  let mkN := Name.str Name.anonymous mkA
  let mkI := mkIdent mkN
  `($mkI:term)

---

partial def matchBuilder(goals: Array (Term × Term))(rhs: Term): MacroM Term := do
  if goals.isEmpty then
    return rhs

  let some (discr, case) := goals[0]?
    | Macro.throwError "Goals array is empty"

  let mut goals' := goals.eraseIdx 0

  let some (op, args) := matchApp case
    | Macro.throwError "matchApp case none"

  if args.size == 0 then      -- .const
    let newRhs ← matchBuilder goals' rhs
    `(term| $(Lean.mkIdent ``Lean.Meta.whnf):ident $discr:term >>= fun e =>
      match e with
      | $case:term => $newRhs:term
      | _ => throwError "Internal error 1"
    )
  else                        -- .app
    let mut newArgs := #[]

    for arg in args do
      let some (_, args') := matchApp arg
        | Macro.throwError s!"matchApp arg none (matchBuilder): {arg}"

      if args'.size == 0 then       -- arg .const
        newArgs := newArgs.push arg
      else                          -- arg .app
        let id ← withFreshMacroScope `(x)
        newArgs := newArgs.push id
        goals' := goals'.push (id, arg)

    let newMkApp ← mkMkApp newArgs.size
    let newRhs ← matchBuilder goals' rhs
    return ← `(term| $(Lean.mkIdent ``Lean.Meta.whnf):ident $discr:term >>= fun e =>
      match e with
      | $newMkApp:term $op:term $newArgs:term* => $newRhs:term
      | _ => throwError "Internal error 2"
    )

---

def transform(mAlt: TSyntax ``matchAlt): MacroM (TSyntax ``matchAlt) := do
  match mAlt with
  | c@`(matchAltExpr| | $lhs:term => $rhs:term) =>

    let some (op, args) := matchApp lhs
      | Macro.throwError s!"matchApp lhs none: {lhs}"

    if args.size == 0 then
      return c
    else
      let mut initialGoals: Array (Term × Term) := #[]
      let mut newArgs: Array Term := #[]

      for arg in args do

        let some (_, args') := matchApp arg
          | Macro.throwError s!"matchApp arg is none (transform): {arg}"

        if args'.size == 0 then       -- arg .const
          newArgs := newArgs.push arg
        else                          -- arg .app
          let id ← withFreshMacroScope `(x)
          newArgs := newArgs.push id
          initialGoals := initialGoals.push (id, arg)

      let newMkApp ← mkMkApp newArgs.size
      let newRhs ← matchBuilder initialGoals rhs
      `(matchAltExpr| | $newMkApp:term $op:term $newArgs:term* => $newRhs:term)
  | _ => Macro.throwUnsupported

---

attribute [run_parser_attribute_hooks] Lean.Parser.Term.matchAltExpr

macro "match_whnf " discr:term " with " alts:matchAltExpr*  : term => do
  let mut result : TSyntaxArray ``matchAlt := #[]
  for alt in alts do
    match alt with
    | c@`(matchAltExpr| | $lhs:term => $_:term) => do
      let us ← `(_)
      if lhs == us then
        result := result.push c
      else
        let newAlt ← transform c
        result := result.push newAlt
    | _ => Macro.throwUnsupported

  let stx ← `(term| $(Lean.mkIdent ``Lean.Meta.whnf):ident $discr:term >>= fun e => match e with $result:matchAlt*)
  return stx
