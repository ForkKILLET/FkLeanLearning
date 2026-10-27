import Lean

declare_syntax_cat proofSignature
syntax bracketedBinder* " : " term : proofSignature

declare_syntax_cat proofSolution
syntax "|" ident " := " term : proofSolution

open Lean in
private def expandProofs (doc : Option (TSyntax ``Lean.Parser.Command.docComment))
    (name : Option (TSyntax `ident))
    (signature : TSyntax `proofSignature)
    (solutions : Array (TSyntax `proofSolution)) : MacroM (TSyntax `command) := do
  let (binders, result) ← match signature with
    | `(proofSignature| $binders:bracketedBinder* : $result:term) =>
      pure (binders, result)
    | _ => Macro.throwErrorAt signature "expected optional parameters followed by : and a type"
  let mut declarations : Array (TSyntax `command) := #[]
  for solution in solutions do
    let `(proofSolution| | $_label:ident := $proof:term) := solution
      | Macro.throwErrorAt solution "expected a labeled proof"
    let declaration ← match name with
      | some id =>
        if declarations.isEmpty then
          `(command| $[$doc]? theorem $id $binders* : $result := $proof)
        else
          `(command| example $binders* : $result := $proof)
      | none =>
        let doc := if declarations.isEmpty then doc else none
        `(command| $[$doc]? example $binders* : $result := $proof)
    declarations := declarations.push declaration
  return ⟨mkNullNode (declarations.map TSyntax.raw)⟩

/-- Share a theorem signature across independently checked proofs.

The first proof defines the named theorem; subsequent proofs are anonymous
examples. Omit the declaration name to make every proof anonymous.
Branch labels describe the proof styles and do not declare Lean names.
An optional doc comment is attached to the first declaration.
As with `example` and `theorem`, a colon precedes the result type, even when
there are no parameters.

```
proofs identityProof (P : Prop) (h : P) : P where
  | term := h
  | tactic := by exact h

proofs : True where
  | term := True.intro
```
-/
macro (priority := high) doc:(docComment)? "proofs" name:ident signature:proofSignature " where"
    solutions:proofSolution+ : command =>
  expandProofs doc (some name) signature solutions

macro doc:(docComment)? "proofs" signature:proofSignature " where"
    solutions:proofSolution+ : command =>
  expandProofs doc none signature solutions
