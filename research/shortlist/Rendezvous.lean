import Mathlib

/-!
# Three symmetric rendezvous rules on the line

Players start two units apart. Each chooses an independent fair sign per
block and follows the given word of signed unit velocities in that direction.
Relative position suffices, including for blocks which translate both players.
For these walks the gap at a tick is even and its change per tick is 0 or ±2:
a first meeting always occurs at an integer tick.

`effort w n d` adds the time spent in block n across the 4^(n+1) equally
likely orientation histories, with initial gap d. A history contributes zero
after a previous hit. Summing the expected contributions of successive
blocks gives the mean duration, also on infinite histories by the tail-sum
interpretation of expectation for a nonnegative integer-valued time.
-/

namespace LineRendezvous

inductive Outcome where
  | hit (tick : ℕ)
  | miss (gap : ℤ)
  deriving DecidableEq

def oriented (positive : Bool) (v : ℤ) : ℤ := if positive then v else -v

/-- Simulate one block from the current right-minus-left gap. -/
def run (left right : Bool) : List ℤ → ℤ → Outcome
  | [], d => .miss d
  | v :: vs, d =>
    let next := d + oriented right v - oriented left v
    if next = 0 then .hit 1 else
      match run left right vs next with
      | .hit t => .hit (t + 1)
      | .miss d' => .miss d'

def outcomes (w : List ℤ) (d : ℤ) : List Outcome :=
  [run true true w d, run true false w d, run false true w d, run false false w d]

def charged (duration : ℕ) : Outcome → ℕ
  | .hit t => t
  | .miss _ => duration

def effort (w : List ℤ) : ℕ → ℤ → ℕ
  | 0, d => ((outcomes w d).map (charged w.length)).sum
  | n+1, d =>
    ((outcomes w d).map (fun o => match o with
      | .hit _ => 0
      | .miss gap => effort w n gap)).sum

/-- The series must converge to the asserted mean. -/
def HasMean (w : List ℤ) (t : ℝ) : Prop :=
  HasSum (fun n : ℕ => (effort w n 2 : ℝ) / (4 : ℝ) ^ (n + 1)) t

def baseline : List ℤ := [1, -1]
def fourStep : List ℤ := [1, -1, -1, 1]
def alpern : List ℤ := [1, -1, -1]

theorem baseline_table :
    outcomes baseline 2 = [.miss 2, .hit 1, .miss 2, .miss 2] := by decide

theorem fourStep_table :
    outcomes fourStep 2 = [.miss 2, .hit 1, .hit 3, .miss 2] := by decide

theorem alpern_table :
    outcomes alpern 2 = [.miss 2, .hit 1, .hit 3, .miss 2] := by decide

theorem baseline_cost (n : ℕ) : effort baseline n 2 = 7 * 3 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [effort, baseline_table]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero, Nat.zero_add, ih, pow_succ]
    ring

private theorem two_misses (w : List ℤ) (a : ℕ)
    (h : outcomes w 2 = [.miss 2, .hit 1, .hit 3, .miss 2])
    (h₀ : effort w 0 2 = a) (n : ℕ) : effort w n 2 = a * 2 ^ n := by
  induction n with
  | zero => simpa using h₀
  | succ n ih =>
    rw [effort, h]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero, Nat.zero_add, ih, pow_succ]
    ring

theorem fourStep_cost (n : ℕ) : effort fourStep n 2 = 12 * 2 ^ n :=
  two_misses fourStep 12 fourStep_table (by decide) n

theorem alpern_cost (n : ℕ) : effort alpern n 2 = 10 * 2 ^ n :=
  two_misses alpern 10 alpern_table (by decide) n

private theorem mean_of_cost (w : List ℤ) (a m : ℕ) (hm : m < 4)
    (hcost : ∀ n, effort w n 2 = a * m ^ n) :
    HasMean w ((a : ℝ) / (4 - (m : ℝ))) := by
  have hm' : (m : ℝ) < 4 := by exact_mod_cast hm
  have hr : (m : ℝ) / 4 < 1 := by linarith
  have hs := (hasSum_geometric_of_lt_one
    (show 0 ≤ (m : ℝ) / 4 by positivity) hr).mul_left ((a : ℝ) / 4)
  have h₁ : 1 - (m : ℝ) / 4 ≠ 0 := by linarith
  have h₂ : 4 - (m : ℝ) ≠ 0 := by linarith
  have he : (a : ℝ) / 4 * (1 - (m : ℝ) / 4)⁻¹ = (a : ℝ) / (4 - (m : ℝ)) := by
    field_simp [h₁, h₂] <;> ring
  unfold HasMean
  rw [← he]
  apply hs.congr_fun
  intro n
  rw [hcost, Nat.cast_mul, Nat.cast_pow, div_pow, pow_succ]
  field_simp <;> ring

theorem baseline_mean : HasMean baseline 7 := by
  convert mean_of_cost baseline 7 3 (by decide) baseline_cost using 1 <;> norm_num

theorem fourStep_mean : HasMean fourStep 6 := by
  convert mean_of_cost fourStep 12 2 (by decide) fourStep_cost using 1 <;> norm_num

theorem alpern_mean : HasMean alpern 5 := by
  convert mean_of_cost alpern 10 2 (by decide) alpern_cost using 1 <;> norm_num

end LineRendezvous
