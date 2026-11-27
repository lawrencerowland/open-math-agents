import GraphNext
import Reconstruction.SeparatorDual

/-!
# Applying an existing reconstruction theorem to a cross-carrier deck

Interface for Samuel Schlesinger's reconstruction-conjecture,
commit 419d639395bd5e3bc32f7e6e220a6c2c371e1ea5 (Lean 4.28.0).
The reconstruction theorems are earlier work; the contribution here is
transport from the same-carrier formulation to the project's deck hypothesis.
-/

namespace ReconstructionTransport

/-- A universal vertex suffices even if the vertices of the competing network
are named from a completely different type. -/
theorem crossCarrierUniversal {V W : Type*} [Fintype V] {G : SimpleGraph V}
    {H : SimpleGraph W} {v : V} (universal : G.IsUniversal v)
    (size : 3 ≤ Fintype.card V) (deck : CrossDeck G H) : Nonempty (G ≃g H) := by
  refine reconstruct_of_same_carrier ?_ deck
  intro K same
  exact SimpleGraph.nonempty_iso_of_universal_vertex universal size same

/-- Kelly's disconnected case, together with its complement dual, also extends
to different vertex carriers by the same transport. -/
theorem crossCarrierDisconnectedOrDual {V W : Type*} [Fintype V] {G : SimpleGraph V}
    {H : SimpleGraph W} (split : ¬ G.Connected ∨ ¬ Gᶜ.Connected)
    (size : 3 ≤ Fintype.card V) (deck : CrossDeck G H) : Nonempty (G ≃g H) := by
  refine reconstruct_of_same_carrier ?_ deck
  intro K same
  have hd : G.SameDeck K := same
  rcases split with h | h
  · exact hd.iso_of_not_connected size h
  · exact SimpleGraph.nonempty_iso_of_compl_not_connected h size hd

end ReconstructionTransport

#print axioms ReconstructionTransport.crossCarrierUniversal
#print axioms ReconstructionTransport.crossCarrierDisconnectedOrDual
