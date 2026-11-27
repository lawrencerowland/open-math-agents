import Mathlib

/-!
# Relabelling a vertex deck

The project denotes the cross-carrier hypothesis below by
`ReconstructionConjecture.Hypomorphic`. Schlesinger's separate reconstruction
library formulates `SimpleGraph.SameDeck` for two graphs on one vertex type.
This transport lets a same-carrier result be used with the project hypothesis.
It needs neither finiteness nor a lower bound on the order; those assumptions
belong to the reconstruction theorem being transported.
-/

namespace ReconstructionTransport

abbrev Card {V : Type*} (G : SimpleGraph V) (v : V) :=
  G.induce ({v}ᶜ : Set V)

def CrossDeck {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ σ : V ≃ W, ∀ v, Nonempty (Card G v ≃g Card H (σ v))

/-- The cards of the pulled-back graph are the original cards, relabelled. -/
private def pullCardIso {V W : Type*} (σ : V ≃ W) (H : SimpleGraph W) (v : V) :
    Card (H.comap σ) v ≃g Card H (σ v) := by
  let e : {x : V // x ≠ v} ≃ {y : W // y ≠ σ v} :=
    { toFun := fun x => ⟨σ x.val, fun h => x.property (σ.injective h)⟩
      invFun := fun y => ⟨σ.symm y.val, fun h => y.property
        ((σ.apply_symm_apply y.val).symm.trans (congrArg σ h))⟩
      left_inv := fun x => Subtype.ext (σ.symm_apply_apply x.val)
      right_inv := fun y => Subtype.ext (σ.apply_symm_apply y.val) }
  exact ⟨e, by intro a b; rfl⟩

/-- A matching of unlabelled cards is equivalent to a relabelling of the
second graph after which every card matches the card at the same index. -/
theorem crossDeck_iff_aligned {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) :
    CrossDeck G H ↔ ∃ σ : V ≃ W, ∀ v,
      Nonempty (Card G v ≃g Card (H.comap σ) v) := by
  constructor
  · rintro ⟨σ, h⟩
    refine ⟨σ, fun v => ?_⟩
    obtain ⟨e⟩ := h v
    exact ⟨e.trans (pullCardIso σ H v).symm⟩
  · rintro ⟨σ, h⟩
    refine ⟨σ, fun v => ?_⟩
    obtain ⟨e⟩ := h v
    exact ⟨e.trans (pullCardIso σ H v)⟩

/-- Any same-carrier reconstruction theorem at a particular graph extends
to comparison graphs on arbitrary types, including other universes. -/
theorem reconstruct_of_same_carrier {V W : Type*} {G : SimpleGraph V}
    (same : ∀ K : SimpleGraph V, CrossDeck G K → Nonempty (G ≃g K))
    {H : SimpleGraph W} (deck : CrossDeck G H) : Nonempty (G ≃g H) := by
  obtain ⟨σ, aligned⟩ := (crossDeck_iff_aligned G H).mp deck
  obtain ⟨e⟩ := same (H.comap σ) ⟨Equiv.refl V, aligned⟩
  let restore : H.comap σ ≃g H := ⟨σ, by intro a b; rfl⟩
  exact ⟨e.trans restore⟩

end ReconstructionTransport

#print axioms ReconstructionTransport.crossDeck_iff_aligned
#print axioms ReconstructionTransport.reconstruct_of_same_carrier
