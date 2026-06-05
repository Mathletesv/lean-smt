/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Smt.Recognizers
import Mathlib.Data.Real.Archimedean

import Smt.Translate

namespace Smt.Translate.Rat

open Translator Term

private def mkNat : Lean.Expr :=
  .const ``Nat []
private def mkReal : Lean.Expr :=
  .const ``Real []

def stripTrailingZeros (s : String) : String :=
  let t := (s.toList.reverse.dropWhile (· == '0')).reverse
  if t.isEmpty then "0" else String.ofList t

def sciToDecimalString (n : Nat) (sgn : Bool) (exp : Nat) : String :=
  if n == 0 then "0.0"
  else
    let digits := ToString.toString n
    let (intRaw, decRaw) : String × String :=
      if !sgn || exp == 0 then
        (digits ++ String.ofList (List.replicate exp '0'), "")
      else
        let len := digits.length
        if exp < len then
          let k := len - exp
          (String.Slice.toString (digits.take k), String.Slice.toString (digits.drop k))
        else
          ("0", String.ofList (List.replicate (exp - len) '0') ++ digits)
    intRaw ++ "." ++ stripTrailingZeros decRaw

@[smt_translate] def translateType : Translator := fun e => match e with
  | .const ``Real _  => return symbolT "Real"
  | _                => return none

@[smt_translate] def translateInt : Translator := fun e => do
  if let some x := e.intFloorOf? mkReal then
    return appT (symbolT "to_int") (← applyTranslators! x)
  else
    return none

@[smt_translate] def translateReal : Translator := fun e => do
  if let some n := e.natLitOf? mkReal then
    return literalT s!"{n}.0"
  else if e.zeroOf? mkReal |>.isSome then
    return literalT "0.0"
  else if e.oneOf? mkReal |>.isSome then
    return literalT "1.0"
  else if let some x := e.natCastOf? mkReal then
    if let some n := x.natLitOf? mkNat then
      return literalT s!"{n}.0"
    else
      return appT (symbolT "to_real") (← applyTranslators! x)
  else if let some x := e.intCastOf? mkReal then
    return appT (symbolT "to_real") (← applyTranslators! x)
  else if let some (m, sgn, exp) := e.ofScientificOf? mkReal then
    return literalT (sciToDecimalString m sgn exp)
  else if let some x := e.negOf? mkReal then
    return appT (symbolT "-") (← applyTranslators! x)
  else if let some x := e.absOf? mkReal then
    return appT (symbolT "abs") (← applyTranslators! x)
  else if let some (x, y) := e.hAddOf? mkReal mkReal then
    return mkApp2 (symbolT "+") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (x, y) := e.hSubOf? mkReal mkReal then
    return mkApp2 (symbolT "-") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (x, y) := e.hMulOf? mkReal mkReal then
    return mkApp2 (symbolT "*") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (x, y) := e.hDivOf? mkReal mkReal then
    return mkApp2 (symbolT "/") (← applyTranslators! x) (← applyTranslators! y)
  else
    return none

@[smt_translate] def translateProp : Translator := fun e => do
  if let some (x, y) := e.ltOf? mkReal then
    return mkApp2 (symbolT "<") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (x, y) := e.leOf? mkReal then
    return mkApp2 (symbolT "<=") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (x, y) := e.geOf? mkReal then
    return mkApp2 (symbolT ">=") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (x, y) := e.gtOf? mkReal then
    return mkApp2 (symbolT ">") (← applyTranslators! x) (← applyTranslators! y)
  else
    return none

end Smt.Translate.Rat
