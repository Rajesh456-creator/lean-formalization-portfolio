/-!
# Schur's theorem for two colours: `S(2) = 4`

A *Schur triple* is `x + y = z` with `1 ≤ x ≤ y` (so `x = y` is allowed).

* `schur_five` : every 2-colouring of `{1,…,5}` contains a monochromatic Schur triple.
* `schur_four` : `{1,…,4}` can be 2-coloured with none (`1,4` red; `2,3` blue).

Only core Lean is used.
-/

namespace Portfolio.Schur

/-- Five Booleans (the colours of `1..5`) always contain a monochromatic Schur triple;
the six triples in `1..5` are listed. -/
theorem schur_bool (b1 b2 b3 b4 b5 : Bool) :
    (b1 = b1 ∧ b1 = b2) ∨
    (b1 = b2 ∧ b2 = b3) ∨
    (b1 = b3 ∧ b3 = b4) ∨
    (b1 = b4 ∧ b4 = b5) ∨
    (b2 = b2 ∧ b2 = b4) ∨
    (b2 = b3 ∧ b3 = b5) := by
  revert b1 b2 b3 b4 b5
  decide

/-- **Upper bound.** Any colouring `c : ℕ → Bool` of `1..5` has `x + y = z` monochromatic. -/
theorem schur_five (c : Nat → Bool) :
    ∃ x y : Nat, 1 ≤ x ∧ x ≤ y ∧ x + y ≤ 5 ∧ c x = c y ∧ c y = c (x + y) := by
  rcases schur_bool (c 1) (c 2) (c 3) (c 4) (c 5) with
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨1, 1, by decide, by decide, by decide, h1, h2⟩
  · exact ⟨1, 2, by decide, by decide, by decide, h1, h2⟩
  · exact ⟨1, 3, by decide, by decide, by decide, h1, h2⟩
  · exact ⟨1, 4, by decide, by decide, by decide, h1, h2⟩
  · exact ⟨2, 2, by decide, by decide, by decide, h1, h2⟩
  · exact ⟨2, 3, by decide, by decide, by decide, h1, h2⟩

/-- Colour `1` and `4` with `true`, `2` and `3` with `false`. -/
def split14 (n : Nat) : Bool := decide (n = 1 ∨ n = 4)

/-- **Lower bound.** This colouring of `1..4` has no monochromatic Schur triple. -/
theorem schur_four :
    ∃ c : Nat → Bool, ∀ x y : Nat, 1 ≤ x → x ≤ y → x + y ≤ 4 →
      ¬ (c x = c y ∧ c y = c (x + y)) := by
  refine ⟨split14, ?_⟩
  have key : ∀ x, x < 4 → ∀ y, y < 4 → (1 ≤ x ∧ x ≤ y ∧ x + y ≤ 4) →
      ¬ (split14 x = split14 y ∧ split14 y = split14 (x + y)) := by
    decide
  intro x y hx hxy hs
  exact key x (by omega) y (by omega) ⟨hx, hxy, hs⟩

/-- Hence the Schur number `S(2) = 4`. -/
theorem schur_2 :
    (∀ c : Nat → Bool, ∃ x y : Nat, 1 ≤ x ∧ x ≤ y ∧ x + y ≤ 5 ∧
        c x = c y ∧ c y = c (x + y)) ∧
    (∃ c : Nat → Bool, ∀ x y : Nat, 1 ≤ x → x ≤ y → x + y ≤ 4 →
        ¬ (c x = c y ∧ c y = c (x + y))) :=
  ⟨schur_five, schur_four⟩

end Portfolio.Schur
