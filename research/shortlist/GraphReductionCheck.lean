import Mathlib

-- Self-contained checker harness. Hypomorphic and the root statement follow
-- FormalConjectures.Wikipedia.ReconstructionConjecture. The root type is
-- written out as a proposition so this check needs no conjectural axiom.
namespace ReconstructionConjecture

def Hypomorphic {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ σ : V ≃ W, ∀ v : V, Nonempty (G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ)

lemma Hypomorphic.card_eq {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (h : Hypomorphic G H) :
    Fintype.card V = Fintype.card W := by
  obtain ⟨σ, -⟩ := h
  exact Fintype.card_congr σ

def RootTarget : Prop :=
  ∀ {V W : Type} [Fintype V] [Fintype W], 3 ≤ Fintype.card V →
    ∀ (G : SimpleGraph V) (H : SimpleGraph W),
      Hypomorphic G H → Nonempty (G ≃g H)

end ReconstructionConjecture

-- Reduction ReconstructionConjecture.reconstruction_conjecture.R1
-- of the graph reconstruction conjecture.
-- Credit: @lawrencerowland

/-!
Complementing a graph complements every vertex-deleted card. We prove
this directly and transport isomorphisms in both directions.

H1 is the published interval-graph theorem of Heinrich, Kiyomi, Otachi
and Schweitzer (Theorem 1, https://arxiv.org/abs/2504.02353).
The comparison graph is unrestricted, as in their theorem.
H2 is the remaining conjecture for two graphs for which neither graph
and neither complement has an interval representation.
-/

namespace OMA.R_ReconstructionConjecture_reconstruction_conjecture_R1

open SimpleGraph ReconstructionConjecture

/-- Intersection graphs of nonempty closed intervals, with loops excluded. -/
def HasIntervalModel {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ left right : V → ℝ, (∀ v, left v ≤ right v) ∧
    ∀ x y, G.Adj x y ↔ x ≠ y ∧ left x ≤ right y ∧ left y ≤ right x

/-- Theorem 1 of Heinrich–Kiyomi–Otachi–Schweitzer. -/
def H1 : Prop :=
  ∀ {V W : Type} [Fintype V] [Fintype W],
    3 ≤ Fintype.card V → ∀ (G : SimpleGraph V) (H : SimpleGraph W),
      HasIntervalModel G → Hypomorphic G H → Nonempty (G ≃g H)

/-- Remaining pairs after exploiting deck symmetry and complementation. -/
def H2 : Prop :=
  ∀ {V W : Type} [Fintype V] [Fintype W],
    3 ≤ Fintype.card V → ∀ (G : SimpleGraph V) (H : SimpleGraph W),
      ¬ HasIntervalModel G → ¬ HasIntervalModel Gᶜ →
      ¬ HasIntervalModel H → ¬ HasIntervalModel Hᶜ →
      Hypomorphic G H → Nonempty (G ≃g H)

private def complementIso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ≃g H) : Gᶜ ≃g Hᶜ := by
  refine ⟨f.toEquiv, ?_⟩
  intro a b
  change (f a ≠ f b ∧ ¬ H.Adj (f a) (f b)) ↔ (a ≠ b ∧ ¬ G.Adj a b)
  exact and_congr (not_congr f.injective.eq_iff) (not_congr f.map_rel_iff)

private theorem induce_complement {V : Type*} (G : SimpleGraph V) (S : Set V) :
    (Gᶜ).induce S = (G.induce S)ᶜ := by
  ext a b
  change ((a : V) ≠ (b : V) ∧ ¬ G.Adj a b) ↔ (a ≠ b ∧ ¬ G.Adj a b)
  exact and_congr (not_congr Subtype.val_injective.eq_iff) Iff.rfl

/-- The deck-matching bijection works also for the complements. -/
theorem complement_hypomorphic {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (h : Hypomorphic G H) : Hypomorphic Gᶜ Hᶜ := by
  obtain ⟨σ, cards⟩ := h
  refine ⟨σ, fun v => ?_⟩
  obtain ⟨f⟩ := cards v
  rw [induce_complement, induce_complement]
  exact ⟨complementIso f⟩

private theorem swap_decks {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (h : Hypomorphic G H) : Hypomorphic H G := by
  obtain ⟨σ, cards⟩ := h
  refine ⟨σ.symm, fun w => ?_⟩
  obtain ⟨f⟩ := cards (σ.symm w)
  exact ⟨by simpa only [σ.apply_symm_apply] using f.symm⟩

private theorem interval_or_complement (known : H1)
    {V W : Type} [Fintype V] [Fintype W] (n : 3 ≤ Fintype.card V)
    {G : SimpleGraph V} {H : SimpleGraph W} (h : Hypomorphic G H)
    (model : HasIntervalModel G ∨ HasIntervalModel Gᶜ) : Nonempty (G ≃g H) := by
  rcases model with direct | dual
  · exact known n G H direct h
  · obtain ⟨f⟩ := known n Gᶜ Hᶜ dual (complement_hypomorphic h)
    exact ⟨by simpa only [compl_compl] using complementIso f⟩

theorem main : H1 → H2 → ReconstructionConjecture.RootTarget := by
  intro known remaining V W _ _ n G H h
  by_cases g : HasIntervalModel G ∨ HasIntervalModel Gᶜ
  · exact interval_or_complement known n h g
  by_cases k : HasIntervalModel H ∨ HasIntervalModel Hᶜ
  · have n' : 3 ≤ Fintype.card W := h.card_eq ▸ n
    obtain ⟨f⟩ := interval_or_complement known n' (swap_decks h) k
    exact ⟨f.symm⟩
  exact remaining n G H (fun i => g (Or.inl i)) (fun i => g (Or.inr i))
    (fun i => k (Or.inl i)) (fun i => k (Or.inr i)) h

end OMA.R_ReconstructionConjecture_reconstruction_conjecture_R1
