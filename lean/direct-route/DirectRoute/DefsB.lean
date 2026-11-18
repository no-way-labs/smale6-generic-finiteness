import DirectRoute.Defs

/-!
The definition of `ChallengeB.lean`, copied without change for the solution.
-/

open Finset

noncomputable section

/-- A closed alternating sequence (paper, Definition 5.1): 2r different edges
`f 0, g 0, …, f (r − 1), g (r − 1)` of `E`, such that `f i` and `g i` have the same height `HW`, and
`g i` and `f (i + 1)` have the same height `HZ`; the index after `r − 1` is 0. -/
structure IsAltSeq {α : Type} (E : Set (ℕ × ℕ)) (HZ HW : ℕ × ℕ → α) (r : ℕ) (f g : ℕ → ℕ × ℕ) :
    Prop where
  pos : 1 ≤ r
  mem_f : ∀ i, i < r → f i ∈ E
  mem_g : ∀ i, i < r → g i ∈ E
  adj_w : ∀ i, i < r → HW (f i) = HW (g i)
  adj_z : ∀ i, i < r → HZ (g i) = HZ (f ((i + 1) % r))
  inj_f : ∀ i j, i < r → j < r → f i = f j → i = j
  inj_g : ∀ i j, i < r → j < r → g i = g j → i = j
  ne_fg : ∀ i j, i < r → j < r → f i ≠ g j

end
