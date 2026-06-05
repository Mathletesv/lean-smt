/-
Copyright (c) 2021-2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Mathlib.Data.Real.Basic
import Smt.Preprocess.Normalize.Attribute
import Auto.MathlibReal

@[smt_normalize ↓]
theorem Real.ofNat_eq_natCast (n : Nat) : Auto.MathlibReal.Real.ofNat n = n := rfl

@[smt_normalize ↓]
theorem Real.neg : Auto.MathlibReal.Real.neg r = -r := rfl

@[smt_normalize ↓]
theorem Real.abs : Auto.MathlibReal.Real.abs r = |r| := rfl

@[smt_normalize ↓]
theorem Real.add_def : Auto.MathlibReal.Real.add a b = a + b := rfl

@[smt_normalize ↓]
theorem Real.sub_def : Auto.MathlibReal.Real.sub a b = a - b := rfl

@[smt_normalize ↓]
theorem Real.mul_def : Auto.MathlibReal.Real.mul a b = a * b := rfl

@[smt_normalize ↓]
theorem Real.div_def : Auto.MathlibReal.Real.div a b = a / b := rfl

@[smt_normalize ↓]
theorem Real.lt_def : Auto.MathlibReal.Real.lt a b = (a < b) := rfl

@[smt_normalize ↓]
theorem Real.le_def : Auto.MathlibReal.Real.le a b = (a ≤ b) := rfl

@[smt_normalize ↓]
theorem Real.max_def : Auto.MathlibReal.Real.max a b = max a b := rfl

@[smt_normalize ↓]
theorem Real.min_def : Auto.MathlibReal.Real.min a b = min a b := rfl
