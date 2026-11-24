/-!
# Ramsey's theorem for triangles: R(3,3) = 6

Colour every pair `i < j` of `Fin n` with one of two colours (`Bool`).
A *monochromatic triangle* is a triple `i < j < k` with
`c i j = c j k = c i k`.

* `ramsey_six`   : every colouring of `Fin 6` has a monochromatic triangle.
* `pentagon_no_mono` : the pentagon/pentagram colouring of `Fin 5` has none.
* `ramsey33`     : together, `R(3,3) = 6`.
* `party_of_six` : among any six people, there are three who all know each other
  or three who are pairwise strangers (for any relation, no symmetry needed).

Only core Lean is used (no Mathlib import), so the file is self-contained.
-/

namespace Portfolio.Ramsey

/-- A 2-colouring of pairs of `Fin n` (only pairs `i < j` are ever looked at). -/
abbrev Coloring (n : Nat) := Fin n → Fin n → Bool

/-- `i < j < k` is a monochromatic triangle for `c`. -/
def MonoTriangle {n : Nat} (c : Coloring n) (i j k : Fin n) : Prop :=
  i < j ∧ j < k ∧ c i j = c j k ∧ c j k = c i k

instance {n : Nat} (c : Coloring n) (i j k : Fin n) : Decidable (MonoTriangle c i j k) := by
  unfold MonoTriangle
  infer_instance

/-- Boolean case split used in the final step: either one of `p q r` equals `x`,
or all three are equal (to `!x`). -/
theorem bool_trichotomy (x p q r : Bool) :
    p = x ∨ q = x ∨ r = x ∨ (p = q ∧ q = r) := by
  revert x p q r
  decide

/-- Pigeonhole on five Booleans: three of them agree. -/
theorem three_of_five (b0 b1 b2 b3 b4 : Bool) :
    (b0 = b1 ∧ b1 = b2) ∨
      (b0 = b1 ∧ b1 = b3) ∨
      (b0 = b1 ∧ b1 = b4) ∨
      (b0 = b2 ∧ b2 = b3) ∨
      (b0 = b2 ∧ b2 = b4) ∨
      (b0 = b3 ∧ b3 = b4) ∨
      (b1 = b2 ∧ b2 = b3) ∨
      (b1 = b2 ∧ b2 = b4) ∨
      (b1 = b3 ∧ b3 = b4) ∨
      (b2 = b3 ∧ b3 = b4) := by
  revert b0 b1 b2 b3 b4
  decide

/-- Pigeonhole for a 2-colouring of five points: some `i < j < k` get the same colour. -/
theorem three_alike (f : Fin 5 → Bool) :
    ∃ i j k : Fin 5, i < j ∧ j < k ∧ f i = f j ∧ f j = f k := by
  rcases three_of_five (f 0) (f 1) (f 2) (f 3) (f 4) with
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨0, 1, 2, by decide, by decide, h1, h2⟩
  · exact ⟨0, 1, 3, by decide, by decide, h1, h2⟩
  · exact ⟨0, 1, 4, by decide, by decide, h1, h2⟩
  · exact ⟨0, 2, 3, by decide, by decide, h1, h2⟩
  · exact ⟨0, 2, 4, by decide, by decide, h1, h2⟩
  · exact ⟨0, 3, 4, by decide, by decide, h1, h2⟩
  · exact ⟨1, 2, 3, by decide, by decide, h1, h2⟩
  · exact ⟨1, 2, 4, by decide, by decide, h1, h2⟩
  · exact ⟨1, 3, 4, by decide, by decide, h1, h2⟩
  · exact ⟨2, 3, 4, by decide, by decide, h1, h2⟩

/-- **Upper bound.** Every 2-colouring of the pairs of a 6-element set contains a
monochromatic triangle.  Proof: the five edges at vertex `0` have two colours, so three
of them, to `a < b < d`, share a colour `x`. If one of the edges `ab, ad, bd` has colour `x`
it closes a triangle with `0`; otherwise `ab, ad, bd` all have the other colour. -/
theorem ramsey_six (c : Coloring 6) : ∃ i j k : Fin 6, MonoTriangle c i j k := by
  obtain ⟨i, j, k, hij, hjk, h1, h2⟩ := three_alike (fun t : Fin 5 => c 0 t.succ)
  have h1 : c 0 i.succ = c 0 j.succ := h1
  have h2 : c 0 j.succ = c 0 k.succ := h2
  have hab : i.succ < j.succ := Fin.succ_lt_succ_iff.mpr hij
  have hbd : j.succ < k.succ := Fin.succ_lt_succ_iff.mpr hjk
  have h0a : (0 : Fin 6) < i.succ := Fin.succ_pos i
  have h0b : (0 : Fin 6) < j.succ := Fin.succ_pos j
  have h0d : (0 : Fin 6) < k.succ := Fin.succ_pos k
  have h3 : c 0 i.succ = c 0 k.succ := h1.trans h2
  rcases bool_trichotomy (c 0 i.succ) (c i.succ j.succ) (c i.succ k.succ) (c j.succ k.succ)
    with hp | hq | hr | ⟨hpq, hqr⟩
  · -- triangle (0, a, b)
    exact ⟨0, i.succ, j.succ, h0a, hab, hp.symm, hp.trans h1⟩
  · -- triangle (0, a, d)
    exact ⟨0, i.succ, k.succ, h0a, Fin.lt_trans hab hbd, hq.symm, hq.trans h3⟩
  · -- triangle (0, b, d)
    exact ⟨0, j.succ, k.succ, h0b, hbd, h1.symm.trans hr.symm, hr.trans h3⟩
  · -- triangle (a, b, d): all three edges have the colour opposite to `x`
    exact ⟨i.succ, j.succ, k.succ, hab, hbd, hpq.trans hqr, hqr.symm⟩

/-- **Lower bound.** Colour the pair `{i, j}` of `Fin 5` by "are they neighbours on the
5-cycle?".  Both the cycle and its complement (the pentagram) are triangle-free. -/
def pentagon : Coloring 5 := fun i j =>
  decide (i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
    (i.val = 0 ∧ j.val = 4) ∨ (j.val = 0 ∧ i.val = 4))

theorem pentagon_no_mono : ∀ i j k : Fin 5, ¬ MonoTriangle pentagon i j k := by
  decide

/-- **`R(3,3) = 6`.** -/
theorem ramsey33 :
    (∀ c : Coloring 6, ∃ i j k : Fin 6, MonoTriangle c i j k) ∧
    (∃ c : Coloring 5, ∀ i j k : Fin 5, ¬ MonoTriangle c i j k) :=
  ⟨ramsey_six, ⟨pentagon, pentagon_no_mono⟩⟩

open Classical in
/-- The "party problem": for any relation `R` ("knows") on six people, there are three
people `i < j < k` who pairwise know each other, or three who pairwise do not. -/
theorem party_of_six (R : Fin 6 → Fin 6 → Prop) :
    ∃ i j k : Fin 6, i < j ∧ j < k ∧
      ((R i j ∧ R j k ∧ R i k) ∨ (¬ R i j ∧ ¬ R j k ∧ ¬ R i k)) := by
  obtain ⟨i, j, k, hij, hjk, h1, h2⟩ := ramsey_six (fun a b => decide (R a b))
  refine ⟨i, j, k, hij, hjk, ?_⟩
  by_cases h : R i j
  · left
    have e1 : decide (R i j) = true := decide_eq_true h
    have e2 : decide (R j k) = true := h1.symm.trans e1
    have e3 : decide (R i k) = true := h2.symm.trans e2
    exact ⟨h, of_decide_eq_true e2, of_decide_eq_true e3⟩
  · right
    have e1 : decide (R i j) = false := decide_eq_false h
    have e2 : decide (R j k) = false := h1.symm.trans e1
    have e3 : decide (R i k) = false := h2.symm.trans e2
    exact ⟨h, of_decide_eq_false e2, of_decide_eq_false e3⟩

end Portfolio.Ramsey
