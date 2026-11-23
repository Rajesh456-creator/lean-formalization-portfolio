import LeanFormalizationPortfolio.Order.KnasterTarski
import Mathlib.Data.Set.Lattice

/-!
# Cantor–Schröder–Bernstein via Knaster–Tarski

If `f : α → β` and `g : β → α` are injective, there is a bijection `α → β`.

Proof idea. On the complete lattice `Set α` consider
`F S = α \ g '' (β \ f '' S)`.
`F` is monotone, so it has a fixed point `S`. Then `α \ S = g '' (β \ f '' S)`.
Define `h a = f a` for `a ∈ S` and `h a = g⁻¹ a` for `a ∉ S`. This `h` is a bijection.

Mathlib has `Function.Embedding.schroeder_bernstein`; this is an independent proof.
-/

namespace Portfolio

open Classical

variable {α β : Type*}

/-- The monotone operator driving the proof, written with explicit quantifiers. -/
def sbMap (f : α → β) (g : β → α) (S : Set α) : Set α :=
  {a | ¬ ∃ b, g b = a ∧ ¬ ∃ x, x ∈ S ∧ f x = b}

theorem sbMap_monotone (f : α → β) (g : β → α) : Monotone (sbMap f g) := by
  intro S T hST a ha hb
  obtain ⟨b, hgb, hnot⟩ := hb
  apply ha
  exact ⟨b, hgb, fun ⟨x, hxS, hfx⟩ => hnot ⟨x, hST hxS, hfx⟩⟩

/-- Cantor–Schröder–Bernstein. -/
theorem schroeder_bernstein' {f : α → β} {g : β → α}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ h : α → β, Function.Bijective h := by
  -- the fixed point from Knaster–Tarski
  let S : Set α := lfp (sbMap f g)
  have hS : sbMap f g S = S := lfp_isFixedPt (sbMap_monotone f g)
  -- unfolded form: a ∈ S ↔ ¬ ∃ b, g b = a ∧ ¬ ∃ x ∈ S, f x = b
  have mem_iff : ∀ a, a ∈ S ↔ ¬ ∃ b, g b = a ∧ ¬ ∃ x, x ∈ S ∧ f x = b := by
    intro a
    constructor
    · intro ha
      have : a ∈ sbMap f g S := by rw [hS]; exact ha
      exact this
    · intro ha
      have : a ∈ sbMap f g S := ha
      rw [hS] at this
      exact this
  -- outside S, a has a g-preimage
  have hpre : ∀ a, a ∉ S → ∃ b, g b = a := by
    intro a ha
    by_contra hne
    apply ha
    rw [mem_iff]
    rintro ⟨b, hb, _⟩
    exact hne ⟨b, hb⟩
  -- and that preimage is not in f '' S
  have hnotimg : ∀ a b, a ∉ S → g b = a → ¬ ∃ x, x ∈ S ∧ f x = b := by
    intro a b ha hb hex
    apply ha
    rw [mem_iff]
    rintro ⟨b', hb', hnot⟩
    have : b' = b := hg (hb'.trans hb.symm)
    subst this
    exact hnot hex
  -- the bijection
  let h : α → β := fun a => if ha : a ∈ S then f a else Classical.choose (hpre a ha)
  have h_in : ∀ a, a ∈ S → h a = f a := by
    intro a ha
    simp only [h, dif_pos ha]
  have h_out : ∀ a (ha : a ∉ S), g (h a) = a := by
    intro a ha
    simp only [h, dif_neg ha]
    exact Classical.choose_spec (hpre a ha)
  refine ⟨h, ?_, ?_⟩
  · -- injective
    intro a₁ a₂ heq
    by_cases h1 : a₁ ∈ S <;> by_cases h2 : a₂ ∈ S
    · rw [h_in a₁ h1, h_in a₂ h2] at heq
      exact hf heq
    · exfalso
      rw [h_in a₁ h1] at heq
      exact hnotimg a₂ (h a₂) h2 (h_out a₂ h2) ⟨a₁, h1, heq⟩
    · exfalso
      rw [h_in a₂ h2] at heq
      exact hnotimg a₁ (h a₁) h1 (h_out a₁ h1) ⟨a₂, h2, heq.symm⟩
    · calc a₁ = g (h a₁) := (h_out a₁ h1).symm
        _ = g (h a₂) := by rw [heq]
        _ = a₂ := h_out a₂ h2
  · -- surjective
    intro b
    by_cases hb : ∃ x, x ∈ S ∧ f x = b
    · obtain ⟨x, hxS, hfx⟩ := hb
      exact ⟨x, by rw [h_in x hxS, hfx]⟩
    · have hga : g b ∉ S := by
        intro hmem
        exact ((mem_iff (g b)).1 hmem) ⟨b, rfl, hb⟩
      refine ⟨g b, ?_⟩
      exact hg (h_out (g b) hga)

end Portfolio
