import Mathlib.Tactic
import Mathlib.NumberTheory.LegendreSymbol.GaussEisensteinLemmas
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.Real.Basic

open Function

variable (n : ℕ)
variable (p : ℕ) [pPrime : Fact (Nat.Prime p)] [p_gt_2 : Fact (p > 2)]

lemma zmod_2_ne_0 : (2 : ZMod p) ≠ (0 : ZMod p) := by
  intro h
  cases p with
  | zero =>
    simpa using p_gt_2.out
  | succ p =>
    have := congr_arg ZMod.val h
    change 2 % (p + 1) = 0 % (p + 1) at this
    simp at this
    rw [Nat.mod_eq_of_lt Fact.out] at this
    simp at this

def sol_sum2squares : Finset (ZMod p × ZMod p) := Finset.univ.filter <|
  fun (x, y) ↦ x^2 + y^2 = 1

def sol_1square (a : ZMod p) : Finset (ZMod p) := Finset.univ.filter <|
  fun x ↦ x^2 = a

def sol_dif2squares_unit : Finset (ZMod p × ZMod p) := Finset.univ.filter <|
  fun (x, y) ↦ x^2 - y^2 = 1

def sol_mul_unit : Finset (ZMod p × ZMod p) := Finset.univ.filter <|
  fun (x, y) ↦ x * y = 1

def f' : sol_dif2squares_unit p -> sol_mul_unit p := fun ⟨⟨x, y⟩, h⟩ =>
  let f : ZMod p × ZMod p := ⟨x + y, x - y⟩
  ⟨ f
  , by apply Finset.mem_filter.mpr
       constructor
       exact Finset.mem_univ f
       have ⟨_fst, snd⟩ := Finset.mem_filter.mp h
       ring_nf; exact snd
  ⟩

lemma f'_bi : Bijective (f' p) := by
  constructor
  · intro a0 a1
    have h0 := f' p a0; rcases h0 with ⟨h0_val, h0_p⟩
    have h1 := f' p a1; rcases h1 with ⟨h1_val, h1_p⟩
    intro h; unfold f' at h; simp at h
    rcases h with ⟨h₁, h₂⟩
    have h_plus :
      (a0.1.fst + a0.1.snd) + (a0.1.fst - a0.1.snd) = (a1.1.fst + a1.1.snd) + (a1.1.fst - a1.1.snd) := by
        exact Mathlib.Tactic.LinearCombination.add_pf h₁ h₂
    have h_sub :
      (a0.1.fst + a0.1.snd) - (a0.1.fst - a0.1.snd) = (a1.1.fst + a1.1.snd) - (a1.1.fst - a1.1.snd) := by
        exact Mathlib.Tactic.LinearCombination.sub_pf h₁ h₂
    ring_nf at h_plus
    ring_nf at h_sub
    have h_plus_1 : a0.1.fst = a1.1.fst := by
      refine (mul_right_cancel₀ ?_ h_plus)
      apply zmod_2_ne_0
    have h_sub_1 : a0.1.snd = a1.1.snd := by
      refine (mul_right_cancel₀ ?_ h_sub)
      apply zmod_2_ne_0
    ext <;> assumption
  unfold Surjective
  rintro ⟨⟨m, n⟩, mn_in_sol_mul_unit⟩
  use ?_
  constructor
  swap
  exact ⟨(m + n) / 2, (m - n) / 2⟩
  apply Finset.mem_filter.mpr
  constructor
  dsimp
  apply Finset.mem_univ
  dsimp
  unfold sol_mul_unit at mn_in_sol_mul_unit; simp at mn_in_sol_mul_unit
  ring_nf
  rw [mn_in_sol_mul_unit]
  norm_num
  apply inv_mul_cancel
  have : (4 : ZMod p) = 2 ^ 2
  norm_num
  rw [this]
  apply pow_ne_zero
  apply zmod_2_ne_0
  dsimp
  ext
  · simp
    unfold f'
    simp
    ring_nf
    rw [mul_assoc, inv_mul_cancel, mul_one]
    apply zmod_2_ne_0
  simp
  unfold f'
  simp
  ring_nf
  rw [mul_assoc, inv_mul_cancel, mul_one]
  apply zmod_2_ne_0

def g' (x : ZMod p) (xnz : x.val ≠ 0) : sol_mul_unit p :=
  let g : ZMod p × ZMod p := ⟨x, 1/x⟩
  ⟨ g
  , by apply Finset.mem_filter.mpr
       constructor
       exact Finset.mem_univ g
       simp; refine (GroupWithZero.mul_inv_cancel x ?_)
       exact (ZMod.val_eq_zero x).not.mp xnz
  ⟩

lemma g'_bi : Bijective (g' p x) := by
  constructor
  · intro a₀ a₁
    have h₀ := g' p x a₀
    rcases h₀ with ⟨h₀_val, h₀_p⟩
    have h₁ := g' p x a₁
    rcases h₁ with ⟨h₁_val, h₁_p⟩
    intro h
    sorry
  sorry

def h' (x : ZMod p) (xnz : x.val ≠ 0) : ZMod (p - 1) := by
  exact x - 1

lemma h'_bi : Bijective (h' p x) := by
  constructor
  · intro a₀ a₁
    simp
  intro a₂
  unfold h'
  sorry

theorem card_sol_1square
    (p : ℕ) [Fact p.Prime] (a : ZMod p) :
  (sol_1square p a).card = 1 + legendreSym p a := by
  by_cases a = 0
  · have : legendreSym p a = 0 := by
      apply (legendreSym.eq_zero_iff p a).mpr
      simp
      exact h
    rw [this, h]; simp
    have : ∀(x : ZMod p), x ∈ sol_1square p 0 ↔ x = 0 := by
      intro x
      constructor
      · intro h
        have : x^2 = 0 := (Finset.mem_filter.mp h).right
        exact sq_eq_zero_iff.mp this
      sorry
    sorry
  sorry

lemma card_sol_dif2squares_unit
    (a b : ZMod p) : (sol_dif2squares_unit p).card = p - 1 := by
    have : (sol_dif2squares_unit p).card = (sol_mul_unit p).card := by
      refine (Finset.card_congr ?_ ?_ ?_ ?_)
      · have f : (a : ZMod p × ZMod p) → a ∈ sol_dif2squares_unit p → ZMod p × ZMod p :=
          fun ⟨x, y⟩ => fun xy_in_sol_dif2squares_unit =>
            have ⟨xs, _⟩ := f' p (Subtype.mk ⟨x, y⟩ xy_in_sol_dif2squares_unit)
            xs
        exact f
      sorry
      sorry
      dsimp
      intro xs xs_in_sol_dif2squares_unit
      sorry
    sorry

theorem card_sol_sum2squares
    (p : ℕ) [Fact (Nat.Prime p)] :
  (sol_sum2squares p).card = 1 - (-1 : ℤ)^((p-1)/2) := by
  sorry
