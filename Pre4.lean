import Mathlib.Tactic
import Mathlib.NumberTheory.LegendreSymbol.GaussEisensteinLemmas
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.Real.Basic

open Function

variable (n : ℕ)
variable (p : ℕ) [Fact (Nat.Prime p)]

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
    have h0 := f' p a0
    rcases h0 with ⟨h0_val, h0_p⟩
    have h1 := f' p a1
    rcases h1 with ⟨h1_val, h1_p⟩
    intro h
    sorry
  sorry

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
