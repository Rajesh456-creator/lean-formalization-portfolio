/-!
# Van der Waerden number `W(2; 3) = 9`

Colour the integers `0, 1, …, n-1` with two colours.  A *monochromatic 3-term arithmetic
progression* is `a, a+d, a+2d` (with `d > 0`, `a + 2d < n`) all of one colour.

* `vdw_nine`  : every 2-colouring of `{0,…,8}` has such a progression.
* `vdw_eight` : there is a 2-colouring of `{0,…,7}` with none (`RRBBRRBB`).

Only core Lean is used.
-/

namespace Portfolio.VanDerWaerden

/-- Nine Booleans always contain a monochromatic 3-term arithmetic progression
(all sixteen progressions in `0..8` are listed). Checked by exhausting all 512 cases. -/
theorem vdw_bool (b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool) :
    (b0 = b1 ∧ b1 = b2) ∨
    (b1 = b2 ∧ b2 = b3) ∨
    (b2 = b3 ∧ b3 = b4) ∨
    (b3 = b4 ∧ b4 = b5) ∨
    (b4 = b5 ∧ b5 = b6) ∨
    (b5 = b6 ∧ b6 = b7) ∨
    (b6 = b7 ∧ b7 = b8) ∨
    (b0 = b2 ∧ b2 = b4) ∨
    (b1 = b3 ∧ b3 = b5) ∨
    (b2 = b4 ∧ b4 = b6) ∨
    (b3 = b5 ∧ b5 = b7) ∨
    (b4 = b6 ∧ b6 = b8) ∨
    (b0 = b3 ∧ b3 = b6) ∨
    (b1 = b4 ∧ b4 = b7) ∨
    (b2 = b5 ∧ b5 = b8) ∨
    (b0 = b4 ∧ b4 = b8) := by
  revert b0 b1 b2 b3 b4 b5 b6 b7 b8
  decide

/-- **Upper bound.** Any colouring `c : ℕ → Bool` has a monochromatic 3-AP inside `0..8`. -/
theorem vdw_nine (c : Nat → Bool) :
    ∃ a d : Nat, 0 < d ∧ a + 2 * d < 9 ∧ c a = c (a + d) ∧ c (a + d) = c (a + 2 * d) := by
  rcases vdw_bool (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) (c 6) (c 7) (c 8) with
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨0, 1, by decide, by decide, h1, h2⟩
  · exact ⟨1, 1, by decide, by decide, h1, h2⟩
  · exact ⟨2, 1, by decide, by decide, h1, h2⟩
  · exact ⟨3, 1, by decide, by decide, h1, h2⟩
  · exact ⟨4, 1, by decide, by decide, h1, h2⟩
  · exact ⟨5, 1, by decide, by decide, h1, h2⟩
  · exact ⟨6, 1, by decide, by decide, h1, h2⟩
  · exact ⟨0, 2, by decide, by decide, h1, h2⟩
  · exact ⟨1, 2, by decide, by decide, h1, h2⟩
  · exact ⟨2, 2, by decide, by decide, h1, h2⟩
  · exact ⟨3, 2, by decide, by decide, h1, h2⟩
  · exact ⟨4, 2, by decide, by decide, h1, h2⟩
  · exact ⟨0, 3, by decide, by decide, h1, h2⟩
  · exact ⟨1, 3, by decide, by decide, h1, h2⟩
  · exact ⟨2, 3, by decide, by decide, h1, h2⟩
  · exact ⟨0, 4, by decide, by decide, h1, h2⟩

/-- The colouring `RRBBRRBB` on `0..7`. -/
def rrbb (n : Nat) : Bool := decide (n % 4 < 2)

/-- **Lower bound.** `RRBBRRBB` has no monochromatic 3-AP inside `0..7`. -/
theorem vdw_eight :
    ∃ c : Nat → Bool, ∀ a d : Nat, 0 < d → a + 2 * d < 8 →
      ¬ (c a = c (a + d) ∧ c (a + d) = c (a + 2 * d)) := by
  refine ⟨rrbb, ?_⟩
  have key : ∀ a, a < 8 → ∀ d, d < 4 → 0 < d → a + 2 * d < 8 →
      ¬ (rrbb a = rrbb (a + d) ∧ rrbb (a + d) = rrbb (a + 2 * d)) := by
    decide
  intro a d hd hlt
  exact key a (by omega) d (by omega) hd hlt

/-- Hence `W(2; 3) = 9`. -/
theorem vdw_2_3 :
    (∀ c : Nat → Bool, ∃ a d : Nat, 0 < d ∧ a + 2 * d < 9 ∧
        c a = c (a + d) ∧ c (a + d) = c (a + 2 * d)) ∧
    (∃ c : Nat → Bool, ∀ a d : Nat, 0 < d → a + 2 * d < 8 →
        ¬ (c a = c (a + d) ∧ c (a + d) = c (a + 2 * d))) :=
  ⟨vdw_nine, vdw_eight⟩

end Portfolio.VanDerWaerden
