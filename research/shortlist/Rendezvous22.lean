import Mathlib

/-!
# Exact certificate for the 22-step symmetric rendezvous policy

Keep this file next to `rendezvous-22.tsv` and run `lake env lean Rendezvous22.lean`
in a Mathlib project. The file checks positive integer weights, two signs
per player, 22 unit steps and return home. It counts all ordered independent
choices with a weighted prefix tree. The two players can meet only at a tick:
their gap is even there and changes by at most two over one step.

The data-consuming equality `policy22_certificate` uses kernel reduction.
The preceding `#eval` provides a quicker diagnostic and is not used as proof.
-/

namespace Rendezvous22

inductive Trie where
  | empty
  | node (weight : ℕ) (back forward : Trie)

def Trie.parts : Trie → ℕ × Trie × Trie
  | .empty => (0, .empty, .empty)
  | .node w b f => (w, b, f)

def insert (weight : ℕ) : List Bool → Trie → Trie
  | [], tree =>
    let (m, b, f) := tree.parts
    .node (m + weight) b f
  | step :: steps, tree =>
    let (m, b, f) := tree.parts
    if step then .node (m + weight) b (insert weight steps f)
    else .node (m + weight) (insert weight steps b) f

def readRow (line : String) : Option (List Bool × ℕ) := do
  let [word, numeral] := line.splitOn "\t" | none
  let weight ← numeral.toNat?
  let steps ← word.toList.mapM (fun c =>
    if c = 'F' then some true else if c = 'B' then some false else none)
  if weight > 0 ∧ steps.length = 22 ∧ steps.count true = 11 then
    some (steps, weight)
  else none

structure Count where
  ticks : ℕ
  failed : ℕ
  wrongGap : ℕ
  deriving DecidableEq, Repr

def Count.plus (x y : Count) : Count :=
  ⟨x.ticks + y.ticks, x.failed + y.failed, x.wrongGap + y.wrongGap⟩

def nothing : Count := ⟨0, 0, 0⟩

/-- For a surviving prefix the physical separation is 2*(slack+1).
An inward simultaneous step at zero slack is a meeting. At a terminal we
count failures separately and check their remaining separation exactly. -/
def count : ℕ → ℕ → Trie → Trie → Count
  | _, _, .empty, _ => nothing
  | _, _, _, .empty => nothing
  | 0, slack, .node l _ _, .node r _ _ =>
    ⟨0, l*r, if slack = 0 then 0 else l*r⟩
  | n+1, slack, .node l lb lf, .node r rb rf =>
    let sameB := count n slack lb rb
    let sameF := count n slack lf rf
    let outward := count n (slack+1) lb rf
    let inward := match slack with
      | 0 => nothing
      | k+1 => count n k lf rb
    let rest := ((sameB.plus sameF).plus outward).plus inward
    ⟨l*r + rest.ticks, rest.failed, rest.wrongGap⟩

structure Audit where
  rows : ℕ
  total : ℕ
  result : Count
  deriving DecidableEq, Repr

def audit (text : String) : Option Audit := do
  let lines := (text.splitOn "\n").filter (fun s => !s.isEmpty)
  let rows ← lines.mapM readRow
  let tree := rows.foldl (fun t row =>
    insert row.2 (row.1.map (fun b => !b)) (insert row.2 row.1 t)) Trie.empty
  let mass := tree.parts.1
  return ⟨rows.length, mass*mass, count 22 0 tree tree⟩

def policy : String := include_str "rendezvous-22.tsv"

def recorded : Audit :=
  ⟨1178, 4000000056000000196, ⟨17004259653205463428, 3383065596638476, 0⟩⟩

/-- The n-th term is the expected amount of time charged by block n.
Independent resampling and return to the starting gap after failures give
the factor (failure probability)^n. The series must converge. -/
def HasMean (a : Audit) (t : ℝ) : Prop :=
  HasSum (fun n : ℕ =>
    ((a.result.ticks : ℝ) / a.total) * ((a.result.failed : ℝ) / a.total) ^ n) t

theorem renewal (a : Audit) (h : a.result.failed < a.total) :
    HasMean a ((a.result.ticks : ℝ) / (a.total - (a.result.failed : ℝ))) := by
  have hlt : (a.result.failed : ℝ) < a.total := by exact_mod_cast h
  have hm : (0 : ℝ) < a.total := lt_of_le_of_lt (by positivity) hlt
  have hq : (a.result.failed : ℝ) / a.total < 1 := (div_lt_one hm).2 hlt
  have hs := (hasSum_geometric_of_lt_one
    (show (0 : ℝ) ≤ a.result.failed / a.total by positivity) hq).mul_left
      ((a.result.ticks : ℝ) / a.total)
  have h₁ : (1 : ℝ) - a.result.failed / a.total ≠ 0 := by linarith
  have h₂ : (a.total : ℝ) - a.result.failed ≠ 0 := by linarith
  unfold HasMean
  convert hs using 1
  field_simp [ne_of_gt hm, h₁, h₂] <;> ring

theorem recorded_mean :
    HasMean recorded (4251064913301365857 / 999154247600840430 : ℝ) := by
  convert renewal recorded (by decide) using 1 <;> norm_num [recorded]

theorem below_reported_bound :
    (4251064913301365857 / 999154247600840430 : ℝ) < 42574 / 10000 := by
  norm_num

#eval audit policy

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem policy22_certificate : audit policy = some recorded := by decide +kernel

theorem policy22_mean : ∃ a, audit policy = some a ∧ a.result.wrongGap = 0 ∧
    HasMean a (4251064913301365857 / 999154247600840430 : ℝ) :=
  ⟨recorded, policy22_certificate, rfl, recorded_mean⟩

end Rendezvous22
