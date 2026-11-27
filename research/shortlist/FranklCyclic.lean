import Mathlib

/-!
# Six activities for which every containment pairing fails

Take the consecutive triples of a six-cycle. Their nonempty unions are the
consecutive windows of sizes three through six. Include the empty scope.
Every activity occurs in 13 of 20 scopes, yet none admits a pairing that
only adds activities. This gives a six-point obstruction inside the case
with no singleton or pair. The five-cycle edge-union obstruction and its
Hall argument were described by makoto-developer on 23 July 2026:
https://blog.makoto-developer.net/articles/2026-07-23-union-closed-conjecture-3

Codex, with Lawrence Rowland.
-/

namespace FranklCyclic

abbrev Activity := Fin 6
abbrev Scope := Finset Activity

def three (i : Activity) : Scope := {i, i + 1, i + 2}
def four (i : Activity) : Scope := insert (i + 3) (three i)
def five (i : Activity) : Scope := insert (i + 4) (four i)

def family : Finset Scope :=
  insert ∅ (insert Finset.univ
    ((Finset.univ.image three ∪ Finset.univ.image four) ∪ Finset.univ.image five))

/-- The consecutive triple opposite the activity under consideration. -/
def opposite (a : Activity) : Scope := three (a + 2)

def sources (a : Activity) : Finset Scope :=
  family.filter fun X => opposite a ⊆ X ∧ a ∉ X

def targets (a : Activity) : Finset Scope :=
  family.filter fun X => opposite a ⊆ X ∧ a ∈ X

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem union_closed : ∀ X ∈ family, ∀ Y ∈ family, X ∪ Y ∈ family := by decide

theorem counts : family.card = 20 ∧ (∀ X ∈ family, X = ∅ ∨ 3 ≤ X.card) ∧
    (∀ a : Activity, (family.filter fun X => a ∈ X).card = 13) := by decide

theorem bottlenecks : ∀ a : Activity, (sources a).card = 4 ∧ (targets a).card = 3 := by
  decide

/-- No choice of activity lets us pair every scope lacking it with a
distinct containing scope by adding activities, even with a different
choice of additions at each source scope. -/
theorem no_containment_pairing (a : Activity) :
    ¬ ∃ f : Scope → Scope,
      (∀ X ∈ family, a ∉ X → f X ∈ family ∧ a ∈ f X ∧ X ⊆ f X) ∧
      ((family.filter fun X => a ∉ X) : Set Scope).InjOn f := by
  rintro ⟨f, hmap, hinj⟩
  have lands : Set.MapsTo f (sources a : Set Scope) (targets a : Set Scope) := by
    intro X hX
    obtain ⟨hF, hP, ha⟩ := Finset.mem_filter.mp hX
    obtain ⟨hi, hai, hsub⟩ := hmap X hF ha
    exact Finset.mem_filter.mpr ⟨hi, hP.trans hsub, hai⟩
  have injects : (sources a : Set Scope).InjOn f := by
    intro X hX Y hY h
    obtain ⟨hxF, _, hxa⟩ := Finset.mem_filter.mp hX
    obtain ⟨hyF, _, hya⟩ := Finset.mem_filter.mp hY
    exact hinj (Finset.mem_filter.mpr ⟨hxF, hxa⟩) (Finset.mem_filter.mpr ⟨hyF, hya⟩) h
  have bound := Finset.card_le_card_of_injOn f lands injects
  obtain ⟨hs, ht⟩ := bottlenecks a
  omega

end FranklCyclic

#print axioms FranklCyclic.no_containment_pairing
#print axioms FranklCyclic.union_closed
#print axioms FranklCyclic.counts
