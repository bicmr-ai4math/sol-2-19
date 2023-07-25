import Mathlib.Tactic
import Mathlib.NumberTheory.LegendreSymbol.GaussEisensteinLemmas
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.Real.Basic

open Function

variable (n : ℕ)
variable (p : ℕ) [pPrime : Fact (Nat.Prime p)] [p_gt_2 : Fact (p > 2)] [p_odd : Fact (p % 2 = 1)]

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

def sol_ne_zero : Finset (ZMod p) := Finset.univ.filter <|
  fun x => x ≠ 0

lemma card_sol_ne_zero_p_1 : Finset.card (sol_ne_zero p) = p - 1 := by
  simp [sol_ne_zero, Finset.filter_ne', Finset.card_univ, ZMod.card]

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
  ext; repeat
    unfold f'
    ring_nf
    rw [mul_assoc, inv_mul_cancel, mul_one]
    apply zmod_2_ne_0

def g' : sol_ne_zero p -> sol_mul_unit p := fun ⟨x, xnz⟩ =>
  let g : ZMod p × ZMod p := ⟨x, 1/x⟩
  ⟨ g
  , by apply Finset.mem_filter.mpr
       constructor
       exact Finset.mem_univ g
       simp; refine (GroupWithZero.mul_inv_cancel x ?_)
       refine ((ZMod.val_eq_zero x).not.mp ?_)
       have ⟨_, xnz⟩ := Finset.mem_filter.mp xnz
       contrapose! xnz
       exact Iff.mp (ZMod.val_eq_zero x) xnz
  ⟩

lemma g'_bi : Bijective (g' p) := by
  constructor
  · intro a₀ a₁
    have h₀ := g' p a₀; rcases h₀ with ⟨h₀_val, h₀_p⟩
    have h₁ := g' p a₁; rcases h₁ with ⟨h₁_val, h₁_p⟩
    intro h
    unfold g' at h; simp at h
    exact SetCoe.ext h
  rintro ⟨⟨a₂, a₃⟩, a₂a₃_in_sol_mul_unit⟩
  use ?_
  constructor
  swap
  exact a₂
  apply Finset.mem_filter.mpr
  constructor
  apply Finset.mem_univ
  unfold sol_mul_unit at a₂a₃_in_sol_mul_unit
  simp at a₂a₃_in_sol_mul_unit
  intro h
  rw [h, zero_mul] at a₂a₃_in_sol_mul_unit
  sorry
  unfold g'
  simp
  refine inv_eq_of_mul_eq_one_right ?right.mk.mk.refine_2.a
  unfold sol_mul_unit at a₂a₃_in_sol_mul_unit
  simp at a₂a₃_in_sol_mul_unit
  exact a₂a₃_in_sol_mul_unit

-- def h' : sol_ne_zero -> ZMod (p - 1) := fun x =>
--   ⟨ h
--   , by apply Finset.mem_filter.mpr

-- lemma h'_bi : Bijective (h' p x) := by
--   constructor
--   · intro a₀ a₁
--     simp
--   intro a₂
--   unfold h'
--   sorry

theorem card_sol_1square (a : ZMod p) :
  (sol_1square p a).card = 1 + legendreSym p a := by
  by_cases h : a = 0
  · have : legendreSym p a = 0 := by
      apply (legendreSym.eq_zero_iff p a).mpr
      simp
      exact h
    rw [this, h]; simp
    have : ∀(x : ZMod p), x ∈ sol_1square p 0 ↔ x ∈ {(0:ZMod p)} := by
      -- intro x
      -- rw [sol_1square, Finset.mem_filter]
      intro x
      constructor
      · intro h'
        have : x = 0 := sq_eq_zero_iff.mp (Finset.mem_filter.mp h').right
        rw [this]
        exact Set.mem_singleton 0
      · intro h'
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ x, sq_eq_zero_iff.mpr h'⟩
    apply Finset.card_eq_one.mpr
    use 0
    -- exact Finset.ext this
    -- -- doesn't work because "∈" has different types
    apply Finset.ext
    simp
    exact this
  by_cases h' : IsSquare a
  · have : legendreSym p a = 1 := by
      apply (legendreSym.eq_one_iff p ?_).mpr
      simpa using h'
      simpa using h
    rw [this]; ring_nf
    have ⟨c, csq_eq_a⟩ : ∃c : ZMod p, a = c^2 := (isSquare_iff_exists_sq a).mp h'
    symm at csq_eq_a
    rw [Int.coe_nat_eq]; congr
    apply Finset.card_eq_two.mpr -- another way: show 'card≤2' using 'poly_root', then show 'c≠-c∈sol...'
    use c, -c
    constructor
    · apply ZMod.ne_neg_self
      intro c0
      apply h
      rw [← csq_eq_a]
      exact sq_eq_zero_iff.mpr c0
    · ext x
      constructor
      · intro hx
        have xsq_eq_a : x^2 = a := (Finset.mem_filter.mp hx).right
        simp
        have : c^2 - x^2 = 0 := by simp [csq_eq_a, xsq_eq_a]
        -- rw [sq_sub_sq] at this
        have : x + c = 0 ∨ x - c = 0 := by
          apply eq_zero_or_eq_zero_of_mul_eq_zero
          ring_nf
          rw [sub_eq_zero] at this
          rw [sub_eq_zero]
          exact this.symm
        rcases this with xc | xc
        · right; exact add_eq_zero_iff_eq_neg.mp xc
        · left; exact sub_eq_zero.mp xc
      · intro xc
        apply Finset.mem_filter.mpr
        constructor
        · exact Finset.mem_univ x
        simp at xc
        rcases xc with xc | xc
        · rw [xc]
          exact csq_eq_a
        · rw [xc]
          ring_nf
          exact csq_eq_a
  · have : legendreSym p a = -1 := by
      apply (legendreSym.eq_neg_one_iff p).mpr
      simp
      exact h'
    rw [this]
    simp
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro x h''
    have : x^2 = a := (Finset.mem_filter.mp h'').right
    have : IsSquare a := by
      apply (isSquare_iff_exists_sq a).mpr
      use x
      exact this.symm
    exact h' this


theorem card_sol_dif2squares_unit
    (a b : ZMod p) : (sol_dif2squares_unit p).card = p - 1 := by
    have : (sol_dif2squares_unit p).card = (sol_mul_unit p).card := by
      refine (Finset.card_congr ?_ ?_ ?_ ?_)
      · have f : (a : ZMod p × ZMod p) → a ∈ sol_dif2squares_unit p → ZMod p × ZMod p :=
          fun ⟨x, y⟩ => fun xy_in_sol_dif2squares_unit =>
            have ⟨xs, _⟩ := f' p (Subtype.mk ⟨x, y⟩ xy_in_sol_dif2squares_unit)
            xs
        exact f
      · dsimp
        intro ⟨x, y⟩ ha
        unfold f'
        simp
        apply Finset.mem_filter.mpr
        simp
        have ⟨_fst, snd⟩ := Finset.mem_filter.mp ha
        ring_nf
        exact snd
      · dsimp
        intro a₀ a₁ ha hb
        intro h
        unfold f' at h
        simp at h
        rcases h with ⟨h₁, h₂⟩
        have h_plus :
          (a₀.fst + a₀.snd) + (a₀.fst - a₀.snd) = (a₁.fst + a₁.snd) + (a₁.fst - a₁.snd) := by
            exact Mathlib.Tactic.LinearCombination.add_pf h₁ h₂
        have h_sub :
          (a₀.fst + a₀.snd) - (a₀.fst - a₀.snd) = (a₁.fst + a₁.snd) - (a₁.fst - a₁.snd) := by
            exact Mathlib.Tactic.LinearCombination.sub_pf h₁ h₂
        ring_nf at h_plus
        ring_nf at h_sub
        have h_plus_1 : a₀.fst = a₁.fst := by
          refine (mul_right_cancel₀ ?_ h_plus)
          apply zmod_2_ne_0
        have h_sub_1 : a₀.snd = a₁.snd := by
          refine (mul_right_cancel₀ ?_ h_sub)
          apply zmod_2_ne_0
        ext <;> dsimp
        exact h_plus_1
        exact h_sub_1
      dsimp
      intro ⟨m, n⟩ mn_in_sol_mul_unit
      use ?_
      exact ⟨(m + n) / 2, (m - n) / 2⟩
      dsimp
      constructor
      · ext; repeat
        unfold f'
        ring_nf
        rw [mul_assoc, inv_mul_cancel, mul_one]
        apply zmod_2_ne_0
      apply Finset.mem_filter.mpr
      dsimp
      constructor
      · apply Finset.mem_univ
      ring_nf
      unfold sol_mul_unit at mn_in_sol_mul_unit
      simp at mn_in_sol_mul_unit
      rw [mn_in_sol_mul_unit]
      norm_num
      apply inv_mul_cancel
      have : (4 : ZMod p) = 2 ^ 2
      norm_num
      rw [this]
      apply pow_ne_zero
      apply zmod_2_ne_0
    rw [this]
    have : (sol_mul_unit p).card = (sol_ne_zero p).card := by
      refine (Finset.card_congr ?_ ?_ ?_ ?_)
      · sorry
      -- · have g : (a : ZMod p × ZMod p) → a ∈ sol_mul_unit p → ZMod p :=
      --     fun ⟨x, y⟩ => fun xy_in_sol_mul_unit =>
      --       have ⟨xt, _⟩ := g' p (Subtype.mk ⟨x, y⟩ xy_in_sol_mul_unit)
      --   exact g
      · sorry
      · sorry
      sorry
    rw [this]
    apply card_sol_ne_zero_p_1

theorem card_sol_sum2squares : (sol_sum2squares p).card = 1 - (-1 : ℤ) ^ ((p - 1) / 2) := by
  sorry
