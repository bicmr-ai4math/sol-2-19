import Mathlib.Tactic
import Mathlib.NumberTheory.LegendreSymbol.GaussEisensteinLemmas

import Mathlib.GroupTheory.SpecificGroups.Cyclic

import Mathlib.Data.Real.Basic

#check subgroup_units_cyclic
#check IsCyclic.card_pow_eq_one_le


-- Z/nZ
variable (n : ℕ)
#check ZMod n

-- the type/set of solutions to an equation in a finite type/set
def sol_sum2squares
    (p : ℕ) [Fact (Nat.Prime p)] : Finset (ZMod p × ZMod p) :=
  Finset.univ.filter (fun (x, y) ↦ x^2 + y^2 = 1)
-- def my_sol
--     {α : Type} [DecidableEq α] [Fintype α] (eq : α → Prop) : Finset α :=
--   Finset.filter eq Finset.univ
variable (p : ℕ) [hP : Fact (Nat.Prime p)]
#check Finset.card (sol_sum2squares p)

def sol_1square
    (p : ℕ) [Fact (Nat.Prime p)] (a : ZMod p) : Finset (ZMod p) :=
  Finset.univ.filter (fun x ↦ x^2 = a)

def sol_dif2squares_unit
    (p : ℕ) [Fact (Nat.Prime p)] : Finset (ZMod p × ZMod p) :=
  Finset.univ.filter (fun (x, y) ↦ x^2 - y^2 = 1)


-- structure ZModPWithoutZero where
--   n : ZMod p
--   p : n ≠ 0

--For Lemma 2
def sol_mul_unit
    (p : ℕ) [Fact (Nat.Prime p)] : Finset (ZMod p × ZMod p) :=
  Finset.univ.filter (fun (x, y) ↦ x * y = 1)
--For Lemma 2



open Function

-- lemma h_to : ∀ x y : ZMod p, (x^2 - y^2 = 1 ↔ (x + y) * (x - y) = 1) := by
--   intro x y
--   constructor
--   · ring
--     exact fun a ↦ a
--   ring
--   exact fun a ↦ a

#check Finset.mem_filter.mpr

-- trans (x, y) -> (x+y, x-y) into set theorical function
def f' : sol_dif2squares_unit p -> sol_mul_unit p := by
  rintro ⟨⟨x, y⟩, h⟩
  constructor
  swap
  constructor
  exact x + y
  exact x - y
  apply Finset.mem_filter.mpr
  constructor
  exact Finset.mem_univ (x + y, x - y)
  simp
  have ⟨fst, snd⟩ := Finset.mem_filter.mp h
  simp at snd
  ring
  exact snd

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


-- def g' [inst : Fact (Nat.Prime p)] : ZMod (p-1) -> @sol_mul_unit p inst := by
--   induction p
--   sorry
--   sorry

def g' (x : ZMod p) (xnz : x.val ≠ 0) : sol_mul_unit p := by
  constructor
  swap
  constructor
  exact x
  exact 1/x
  apply Finset.mem_filter.mpr
  constructor
  exact Finset.mem_univ (x, 1/x)
  simp
  -- rw [mul_right_inv x]
  -- rw [mul_inv_cancel_left hP.ne_zero]
  sorry

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



/-
PROB FOR NOW:
def g' x * x⁻¹ = 1
f'_bi and g'_bi
def h' and h'_bi below
-/


def h' (x : ZMod p) (xnz : x.val ≠ 0) : ZMod (p - 1) := by
  exact x - 1


lemma h'_bi : Bijective (h' p x) := by
  constructor
  · intro a₀ a₁
    simp
  intro a₂
  unfold h'
  sorry







#check Fintype.card (ZMod p)










-- example (p : ℕ) [Fact (Nat.Prime p)] : Bijective (fun x => x ∈ sol_dif2squares_unit p -> x ∈ sol_mul_unit p) := by
--   constructor
--   · unfold Injective
--     intro a1 a2
--     simp
--     intro hP
--     unfold sol_dif2squares_unit at hP
--     sorry
--   sorry


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
      -- dsimp
      -- intro x
      -- rw [Finset.mem_filter] -- why can't rw here?
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
      apply Nat.card_eq_of_bijective f'_bi
    sorry


    -- have : ∀ a₁ a₂ b₁ b₂ : ZMod p, ((a₁ = a₂ ∧ b₁ = b₂) ↔ (a₁ + b₁ = a₂ + b₂ ∧ a₁ - b₁ = a₂ - b₂)) := by
    --   intro a₁ a₂ b₁ b₂
    --   constructor
    --   ·



    -- have : ∀ x : ZMod p, ∃! y : ZMod p, x^2 - y^2 = 1 := by
    --   intro x
    --   have : Bijective (fun x ↦ (x, y)) := by
    --     have : ∃! y : ZMod p, y^2 = x^2 - 1 := by
    --       -- apply card_sol_1square p (x^2 - 1)
    --       sorry
    --     sorry
    --   sorry
    -- sorry


      -- sorry
    -- sorry




theorem card_sol_sum2squares
    (p : ℕ) [Fact (Nat.Prime p)] :
  (sol_sum2squares p).card = 1 - (-1 : ℤ)^((p-1)/2) := by
  sorry
