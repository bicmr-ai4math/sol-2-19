import Mathlib.Tactic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Pairwise.Basic

open BigOperators
open Set

-- #check legendreSym.card_sqrts
-- #check quadraticChar_isNontrivial
-- #check Finset.card_disjiUnion

variable {p : ℕ} [Fact (Nat.Prime p)] {p_odd : p ≠ 2}
variable {a b : ℤ}

def card_x_sqrt_eq_a : ℕ := {x : ZMod p | x ^ 2 = a}.toFinset.card
def card_y_sqrt_eq_b : ℕ := {y : ZMod p | y ^ 2 = b}.toFinset.card

example : @card_x_sqrt_eq_a p _ a = legendreSym p a + 1 := by
  apply legendreSym.card_sqrts
  exact p_odd

example : @card_y_sqrt_eq_b p _ b = legendreSym p b + 1 := by
  apply legendreSym.card_sqrts
  exact p_odd

def map_x_sqrt_y_sqrt_and_one : ZMod p → Finset (ZMod p × ZMod p) :=
  fun (a : ZMod p) => {xs : ZMod p × ZMod p | xs.1 ^ 2 = a ∧ xs.2 ^ 2 = 1 - a}.toFinset

def x_sqrt_y_sqrt_eq_one : Finset (ZMod p × ZMod p) :=
  let h := setOf <| fun xs => xs.1 ^ 2 + xs.2 ^ 2 = 1
  h.toFinset

def x_sqrt_y_sqrt_and_one : Finset (ZMod p × ZMod p) := toFinset $
  ⋃ (a : ZMod p), {xs : ZMod p × ZMod p | xs.1 ^ 2 = a ∧ xs.2 ^ 2 = 1 - a}

lemma x_sqrt_y_sqrt_eq_one_eq_x_sqrt_y_sqrt_and_one :
  @x_sqrt_y_sqrt_eq_one p _ = x_sqrt_y_sqrt_and_one := by
  ext xs
  constructor
  · intro xs_in_x_sqrt_y_sqrt_eq_one
    unfold x_sqrt_y_sqrt_and_one
    apply (Iff.mpr mem_toFinset)
    rw [mem_iUnion]; simp
    unfold x_sqrt_y_sqrt_eq_one at xs_in_x_sqrt_y_sqrt_eq_one; simp at xs_in_x_sqrt_y_sqrt_eq_one
    rw [<- xs_in_x_sqrt_y_sqrt_eq_one]; ring
  intro xs_in_x_sqrt_y_sqrt_and_one
  unfold x_sqrt_y_sqrt_eq_one
  unfold x_sqrt_y_sqrt_and_one at xs_in_x_sqrt_y_sqrt_and_one; simp
  simp at xs_in_x_sqrt_y_sqrt_and_one
  rw [xs_in_x_sqrt_y_sqrt_and_one]; simp

lemma pairwise_disjoint_map_x_sqrt_y_sqrt_and_one : Set.PairwiseDisjoint univ.toFinset.toSet (@map_x_sqrt_y_sqrt_and_one p _) := by
  intro a _a_in_univ b _b_in_univ a_ne_b
  intro xs xs_in_map_x_sqrt_y_sqrt_and_one_a
  unfold map_x_sqrt_y_sqrt_and_one at xs_in_map_x_sqrt_y_sqrt_and_one_a; simp at xs_in_map_x_sqrt_y_sqrt_and_one_a
  intro xs_in_map_x_sqrt_y_sqrt_and_one; unfold map_x_sqrt_y_sqrt_and_one at xs_in_map_x_sqrt_y_sqrt_and_one
  simp
  intro ys ys_in_xs
  simp
  have h0 : ys ∈ {xs_1 | xs_1.fst ^ 2 = a ∧ xs_1.snd ^ 2 = 1 - a} := by
    exact Iff.mp mem_toFinset (xs_in_map_x_sqrt_y_sqrt_and_one_a ys_in_xs)
  have h1 : ys ∈ {xs | xs.fst ^ 2 = b ∧ xs.snd ^ 2 = 1 - b} := by
    exact Iff.mp mem_toFinset (xs_in_map_x_sqrt_y_sqrt_and_one ys_in_xs)
  simp at h0; simp at h1
  have : a = b := by
    rw [<- h0.1, <- h1.1]
  contradiction

def disjiUnion_map_x_sqrt_y_sqrt_and_one : Finset (ZMod p × ZMod p) := Finset.disjiUnion univ.toFinset (@map_x_sqrt_y_sqrt_and_one p _) pairwise_disjoint_map_x_sqrt_y_sqrt_and_one

lemma card_disjiUnion_eq_card_sum_map_x_sqrt_y_sqrt_and_one : (@disjiUnion_map_x_sqrt_y_sqrt_and_one p _).card = ∑ a in univ.toFinset, (@map_x_sqrt_y_sqrt_and_one p _ a).card := by
  apply Finset.card_disjiUnion
