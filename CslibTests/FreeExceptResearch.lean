/-
Copyright (c) 2026 Mateo Petel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mateo Petel
-/

import Cslib.Foundations.Control.Monad.Free

/-!
# Free exception effect research

This file tests a minimal exception effect directly on CSLib's existing `FreeM` API.
The exception operation is indexed by `PEmpty`, so throwing is structurally abortive:
there is no result value with which a continuation could resume.

The experiment intentionally stays in the test tree. Its purpose is to validate the representation,
canonical `Except` interpreter, universal-property uniqueness, and bind semantics before considering
any public API.
-/

namespace CslibTests.FreeExceptResearch

open Cslib
open Cslib.FreeM

universe u v

/-- Exception signature with no return value after `throw`. -/
inductive ExceptF (ε : Type u) : Type u → Type u where
  | throw (e : ε) : ExceptF ε PEmpty

/-- Free exception computations over CSLib's existing freer monad. -/
abbrev FreeExcept (ε : Type u) := FreeM (ExceptF ε)

namespace FreeExcept

variable {ε : Type u} {α : Type v}

/-- Abort the computation with `e`. -/
def throw (e : ε) : FreeExcept ε α :=
  .liftBind (.throw e) PEmpty.elim

/-- Direct recursive semantics into `Except`. -/
def run : FreeExcept ε α → Except ε α
  | .pure a => .ok a
  | .liftBind (.throw e) _ => .error e

@[simp]
theorem run_pure (a : α) : run (pure a : FreeExcept ε α) = .ok a := rfl

@[simp]
theorem run_throw (e : ε) : run (throw (α := α) e) = .error e := rfl

@[simp]
theorem run_bind (x : FreeExcept ε α) (f : α → FreeExcept ε β) :
    run (x.bind f) = run x >>= fun a => run (f a) := by
  induction x using FreeM.induction generalizing f with
  | pure a => rfl
  | lift_bind op cont ih =>
    cases op
    rfl

section Canonical

variable {ε α : Type u}

/-- Interpret one exception operation into Lean's `Except` monad. -/
@[simp]
def exceptInterp {ι : Type u} : ExceptF ε ι → Except ε ι
  | .throw e => .error e

/-- Canonical interpreter obtained from `FreeM.liftM`. -/
abbrev toExcept (comp : FreeExcept ε α) : Except ε α :=
  comp.liftM exceptInterp

/-- The canonical interpreter agrees with the direct recursive semantics. -/
@[simp]
theorem toExcept_eq_run (comp : FreeExcept ε α) : toExcept comp = run comp := by
  induction comp using FreeM.induction with
  | pure a => rfl
  | lift_bind op cont ih =>
    cases op
    rfl

/-- `toExcept` is the unique interpreter extending `exceptInterp`. -/
theorem toExcept_unique (g : FreeExcept ε α → Except ε α)
    (h : Interprets exceptInterp g) : g = toExcept :=
  h.eq

end Canonical

/-- A throw discards all syntactic continuations. -/
example (e : ε) (f : Nat → FreeExcept ε Nat) :
    run ((throw (α := Nat) e).bind f) = .error e := by
  rw [run_bind, run_throw]
  rfl

end FreeExcept

end CslibTests.FreeExceptResearch
