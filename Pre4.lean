import Mathlib.Tactic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic

import Mathlib.Data.Set.Pairwise.Basic

open BigOperators
open Set

#check legendreSym.card_sqrts
#check quadraticChar_isNontrivial
#check setOf
#check Finset.card_disjiUnion

variable {p : ℕ} [Fact (Nat.Prime p)] {p_odd : p ≠ 2}
variable {a b : ℤ}

def card_x_sqrt_eq_a : ℕ := {x : ZMod p | x ^ 2 = a}.toFinset.card
def card_y_sqrt_eq_b : ℕ := {y : ZMod p | y ^ 2 = b}.toFinset.card

def xs : ZMod p → Finset (ZMod p × ZMod p) :=
  fun (a : ZMod p) => {xs : ZMod p × ZMod p | xs.1 ^ 2 = a ∧ xs.2 ^ 2 = 1 - a}.toFinset


example : @card_x_sqrt_eq_a p _ a = legendreSym p a + 1 := by
  apply legendreSym.card_sqrts
  exact p_odd

example : @card_y_sqrt_eq_b p _ b = legendreSym p b + 1 := by
  apply legendreSym.card_sqrts
  exact p_odd

def x_sqrt_y_sqrt_eq_one : Finset (ZMod p × ZMod p) :=
  let h := setOf <| fun xs => xs.1 ^ 2 + xs.2 ^ 2 = 1
  h.toFinset


def x_sqrt_y_sqrt_and : Finset (ZMod p × ZMod p) := toFinset $
  ⋃ (a : ZMod p), {xs : ZMod p × ZMod p | xs.1 ^ 2 = a ∧ xs.2 ^ 2 = 1 - a}

lemma x_sqrt_y_sqrt_eq_one_eq_x_sqrt_y_sqrt_and :
  @x_sqrt_y_sqrt_eq_one p _ = x_sqrt_y_sqrt_and := by
  ext xs
  constructor
  intro xs_in
  unfold x_sqrt_y_sqrt_and
  apply (Iff.mpr mem_toFinset)
  rw [mem_iUnion]
  simp
  unfold x_sqrt_y_sqrt_eq_one at xs_in
  simp at xs_in
  rw [<- xs_in]
  ring
  intro xs_in
  unfold x_sqrt_y_sqrt_eq_one; simp
  unfold x_sqrt_y_sqrt_and at xs_in; simp
  -- apply (Iff.mpr mem_toFinset)
  simp at xs_in
  -- rw [mem_iUnion] at xs_in
  -- rcases xs_in with ⟨i, i_prf⟩
  -- simp at i_prf
  -- rw [i_prf.1, i_prf.2]
  -- simp
  rw [xs_in]; simp


def univ_ : Finset (ZMod p) := Finset.univ

#check Finset.disjiUnion
#check Set.PairwiseDisjoint
#check Finset.mem_fin

lemma disj_x_sqrt_y_sqrt_and :
  Set.PairwiseDisjoint univ.toFinset.toSet (@xs p _) := by
  unfold PairwiseDisjoint
  intro xs _xs_in_univ ys _ys_in_univ xs_ne_ys
  unfold Disjoint
  intro xss
  intro xss_le
  unfold xs at xss_le; simp at xss_le
  intro xss_in; unfold xs at xss_in
  simp
  intro yss
  intro xss_in_yss
  simp
  have h0 : yss ∈ {xs_1 | xs_1.fst ^ 2 = xs ∧ xs_1.snd ^ 2 = 1 - xs} := by
    exact Iff.mp mem_toFinset (xss_le xss_in_yss)
  have h1 : yss ∈ {xs | xs.fst ^ 2 = ys ∧ xs.snd ^ 2 = 1 - ys} := by
    exact Iff.mp mem_toFinset (xss_in xss_in_yss)
  simp at h0; simp at h1
  have : xs = ys := by
    rw [<- h0.1, <- h1.1]
  contradiction

#check Finset.disjiUnion

def dis_j : Finset (ZMod p × ZMod p) := Finset.disjiUnion univ.toFinset (@xs p _) disj_x_sqrt_y_sqrt_and

-- def fin_x_sqrt_y_sqrt_and : Finset (ZMod p × ZMod p) :=
--   x_sqrt_y_sqrt_and.toFinset

#check Finset.card_disjiUnion

example : (Set.univ : Set (ZMod p)) = ((univ.toFinset).toSet : Set (ZMod p)) := by
  simp


lemma xxx_eq :
  (@dis_j p _).card = ∑ a in univ.toFinset, (@xs p _ a).card := by
  -- simp
  -- unfold x_sqrt_y_sqrt_and; dsimp
  apply Finset.card_disjiUnion
  -- refine (@Finset.card_disjiUnion (ZMod p × ZMod p) (ZMod p) univ.toFinset xs ?_)
