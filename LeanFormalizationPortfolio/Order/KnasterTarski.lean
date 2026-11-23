import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.Monotone.Basic

/-!
# The Knaster–Tarski fixed point theorem

Let `α` be a complete lattice and `f : α → α` a monotone map.

* `lfp f` is the infimum of the *pre-fixed points* `{x | f x ≤ x}`;
* `gfp f` is the supremum of the *post-fixed points* `{x | x ≤ f x}`.

We prove that `lfp f` (resp. `gfp f`) is a fixed point of `f`, and that it is the
least (resp. greatest) one.

This is a from-scratch re-development for practice. Mathlib has the same
theory as `OrderHom.lfp` / `OrderHom.gfp`.
-/

namespace Portfolio

variable {α : Type*} [CompleteLattice α]

/-- Elements `x` with `f x ≤ x`. -/
def prefixedPoints (f : α → α) : Set α := {x | f x ≤ x}

/-- Elements `x` with `x ≤ f x`. -/
def postfixedPoints (f : α → α) : Set α := {x | x ≤ f x}

/-- Least fixed point candidate: the infimum of all pre-fixed points. -/
def lfp (f : α → α) : α := sInf (prefixedPoints f)

/-- Greatest fixed point candidate: the supremum of all post-fixed points. -/
def gfp (f : α → α) : α := sSup (postfixedPoints f)

/-! ### Least fixed point -/

/-- `lfp f` lies below every pre-fixed point. -/
theorem lfp_le_of_map_le {f : α → α} {x : α} (hx : f x ≤ x) : lfp f ≤ x :=
  sInf_le (show x ∈ prefixedPoints f from hx)

/-- First half of the argument: `f (lfp f) ≤ lfp f`. -/
theorem map_lfp_le {f : α → α} (hf : Monotone f) : f (lfp f) ≤ lfp f :=
  le_sInf fun b hb => le_trans (hf (sInf_le hb)) hb

/-- Second half: `lfp f ≤ f (lfp f)`, using that `f (lfp f)` is itself pre-fixed. -/
theorem lfp_le_map {f : α → α} (hf : Monotone f) : lfp f ≤ f (lfp f) :=
  lfp_le_of_map_le (hf (map_lfp_le hf))

/-- **Knaster–Tarski (least fixed point).** `lfp f` is a fixed point of `f`. -/
theorem lfp_isFixedPt {f : α → α} (hf : Monotone f) : f (lfp f) = lfp f :=
  le_antisymm (map_lfp_le hf) (lfp_le_map hf)

/-- `lfp f` is below every fixed point. -/
theorem lfp_le_fixedPt {f : α → α} {x : α} (hx : f x = x) : lfp f ≤ x :=
  lfp_le_of_map_le (le_of_eq hx)

/-- `lfp f` is the least fixed point of `f`. -/
theorem lfp_isLeast {f : α → α} (hf : Monotone f) :
    f (lfp f) = lfp f ∧ ∀ x, f x = x → lfp f ≤ x :=
  ⟨lfp_isFixedPt hf, fun _ hx => lfp_le_fixedPt hx⟩

/-- The least fixed point is monotone in the function. -/
theorem lfp_mono {f g : α → α} (hf : Monotone f) (hg : Monotone g)
    (hfg : ∀ x, f x ≤ g x) : lfp f ≤ lfp g :=
  lfp_le_of_map_le (le_trans (hfg _) (map_lfp_le hg))

/-! ### Greatest fixed point (dual argument) -/

/-- `gfp f` lies above every post-fixed point. -/
theorem le_gfp_of_le_map {f : α → α} {x : α} (hx : x ≤ f x) : x ≤ gfp f :=
  le_sSup (show x ∈ postfixedPoints f from hx)

theorem le_map_gfp {f : α → α} (hf : Monotone f) : gfp f ≤ f (gfp f) :=
  sSup_le fun b hb => le_trans hb (hf (le_sSup hb))

theorem map_gfp_le {f : α → α} (hf : Monotone f) : f (gfp f) ≤ gfp f :=
  le_gfp_of_le_map (hf (le_map_gfp hf))

/-- **Knaster–Tarski (greatest fixed point).** -/
theorem gfp_isFixedPt {f : α → α} (hf : Monotone f) : f (gfp f) = gfp f :=
  le_antisymm (map_gfp_le hf) (le_map_gfp hf)

theorem le_gfp_of_fixedPt {f : α → α} {x : α} (hx : f x = x) : x ≤ gfp f :=
  le_gfp_of_le_map (le_of_eq hx.symm)

/-- `gfp f` is the greatest fixed point of `f`. -/
theorem gfp_isGreatest {f : α → α} (hf : Monotone f) :
    f (gfp f) = gfp f ∧ ∀ x, f x = x → x ≤ gfp f :=
  ⟨gfp_isFixedPt hf, fun _ hx => le_gfp_of_fixedPt hx⟩

end Portfolio
