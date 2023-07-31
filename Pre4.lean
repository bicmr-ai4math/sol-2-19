import Mathlib.Tactic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Pairwise.Basic

open BigOperators Set Finset

variable {p : ℕ} [Fact (Nat.Prime p)] {p_odd : p ≠ 2}

def sol : Finset (ZMod p × ZMod p) :=
  {z :ZMod p × ZMod p | z.1 ^ 2 + z.2 ^ 2 = 1}.toFinset

def xs : ZMod p → Finset (ZMod p × ZMod p) :=
  fun (a : ZMod p) => {x : ZMod p | x ^ 2 = a}.toFinset ×ˢ {y : ZMod p | y ^ 2 = 1-a}.toFinset

lemma disj_of_xs :
  Set.PairwiseDisjoint univ.toFinset.toSet (@xs p _) := by
  unfold PairwiseDisjoint
  intro a _ b _ h
  unfold Disjoint
  intro z za zb t tz
  simp
  have h1:=za tz
  have h2:=zb tz
  unfold xs at h1 h2
  simp at h1 h2
  cases' h1 with h1 h3
  cases' h2 with h2 h4
  rw [mem_toFinset] at h1 h2
  simp at h1 h2
  rw [h1] at h2
  contradiction

def disjiUnion_of_xs : Finset (ZMod p × ZMod p) := disjiUnion univ.toFinset (@xs p _) disj_of_xs

lemma disjeq : @sol p _ = @disjiUnion_of_xs p _ := by
  unfold disjiUnion_of_xs
  unfold sol
  simp
  unfold xs
  ext z
  rw [mem_toFinset,Finset.mem_biUnion]
  simp
  constructor
  intro h
  use z.fst^2
  rw [mem_toFinset,mem_toFinset]
  simp
  rw [← h];simp
  intro h
  cases' h with a h
  rw [mem_toFinset,mem_toFinset] at h
  simp at h
  rw [h.1,h.2]
  simp

lemma disj_card : (@disjiUnion_of_xs p _).card = ∑ a in univ.toFinset, (@xs p _ a).card := card_disjiUnion _ _ _

lemma xs_card (a:ZMod p) : (@xs p _ a).card =({x : ZMod p | x ^ 2 = a}.toFinset).card * ({y : ZMod p | y ^ 2 = 1-a}.toFinset).card:= card_product _ _

lemma legendreSym_eq_quadraticChar :∀ a :ZMod p,legendreSym p a=quadraticChar (ZMod p) a:= by
    intro a
    by_cases h1:a=0
    have h2:(quadraticChar (ZMod p)) a=0
    rw [quadraticChar_eq_zero_iff]
    exact h1
    have h3 :legendreSym p ↑a=0
    rw [legendreSym.eq_zero_iff]
    simp
    exact h1
    rw [h2,h3]
    by_cases h2:IsSquare a
    have h3:(quadraticChar (ZMod p)) a=1
    rw [quadraticChar_one_iff_isSquare]
    exact h2
    exact h1
    have h4:legendreSym p ↑a=1
    rw [legendreSym.eq_one_iff]
    simp
    exact h2
    simp
    exact h1
    rw [h3,h4]
    have h3:(quadraticChar (ZMod p)) a=-1
    rw [quadraticChar_neg_one_iff_not_isSquare]
    exact h2
    have h4:legendreSym p ↑a=-1
    rw [legendreSym.eq_neg_one_iff]
    simp
    exact h2
    rw [h3,h4]

lemma card_quadraticChar (a :ZMod p) : {x | x ^ 2 = a}.toFinset.card = (quadraticChar (ZMod p) a + 1) := by
  have h : ↑(a:ℤ) = a
  simp
  rw [← h,legendreSym.card_sqrts,legendreSym_eq_quadraticChar,h]
  assumption

lemma comp1 : Int.ofNat (@sol p _).card = ∑ a in (univ.toFinset : Finset (ZMod p)), (quadraticChar (ZMod p) a + 1) * (quadraticChar (ZMod p) (1-a) + 1) := by
  rw [disjeq,disj_card]
  conv => lhs ;simp
  conv => rhs ;lhs; simp
  congr
  ext a
  rw [xs_card]
  rw [← card_quadraticChar,← card_quadraticChar]
  simp
  repeat assumption

lemma sum_of_quadraticChar : ∑ a in (univ.toFinset : Finset (ZMod p)), (quadraticChar (ZMod p)) a = 0 := by
  simp
  apply quadraticChar_sum_zero
  rw [ZMod.ringChar_zmod_n]
  exact p_odd

lemma comp2 : ∑ a in (univ.toFinset : Finset (ZMod p)), (quadraticChar (ZMod p) a + 1) * (quadraticChar (ZMod p) (1-a) + 1) = p - (-1)^((p-1)/2) :=
calc
  ∑ a in (univ.toFinset : Finset (ZMod p)), (quadraticChar (ZMod p) a + 1) * (quadraticChar (ZMod p) (1-a) + 1) = ∑ a in (univ.toFinset : Finset (ZMod p)), ((quadraticChar (ZMod p) a)*(quadraticChar (ZMod p) (1-a)) +(quadraticChar (ZMod p) a) +(quadraticChar (ZMod p) (1-a))+1) := by
    simp
    congr
    ext a
    ring

  _ = ∑ a in (univ.toFinset : Finset (ZMod p)), (quadraticChar (ZMod p) a)*(quadraticChar (ZMod p) (1-a))+∑ a in (univ.toFinset : Finset (ZMod p)), (quadraticChar (ZMod p) a)+∑ a in (univ.toFinset : Finset (ZMod p)), (quadraticChar (ZMod p) (1-a))+∑ a in (univ.toFinset : Finset (ZMod p)),1:= by
    repeat rw [sum_add_distrib]

  _ = ∑ a in (univ.toFinset : Finset (ZMod p)), (quadraticChar (ZMod p) (a*(1-a))) + p :=by
    have p1 :∑ a in (univ.toFinset : Finset (ZMod p)), (quadraticChar (ZMod p) (1-a))=0
    have h1 :∑ a in (univ.toFinset : Finset (ZMod p)), (quadraticChar (ZMod p) a)=∑ a in (univ.toFinset : Finset (ZMod p)), quadraticChar (ZMod p) (1-a)
    let g: ZMod p → ZMod p := fun a => 1-a
    have h2 : univ.toFinset = Finset.image g univ.toFinset
    ext a
    simp
    use 1-a
    simp
    nth_rw 1 [h2]
    apply sum_image
    intro x _ y _ h5
    simp at h5
    exact h5
    rw [← h1,sum_of_quadraticChar]
    exact p_odd
    have p2 :∑ a in (univ.toFinset : Finset (ZMod p)),1=(p:ℤ)
    simp
    rw [card_univ,← Nat.card_eq_fintype_card]
    simp
    rw [p1,p2,sum_of_quadraticChar]
    simp
    exact p_odd

  _=∑ a in {x : ZMod p | x ≠ 0}.toFinset,(quadraticChar (ZMod p) (a*(1-a))) + p := by
    have h1 : {x : ZMod p | x ≠ 0}.toFinset = erase univ.toFinset 0
    ext x
    simp
    rw [mem_toFinset]
    simp
    rw [h1,sum_erase_eq_sub]
    simp
    simp

  _=∑ a in {x : ZMod p | x ≠ 0}.toFinset,(quadraticChar (ZMod p) (a⁻¹-1)) + p := by
    apply add_right_cancel_iff.mpr
    apply sum_congr
    rfl
    intro a h0
    rw [mem_toFinset] at h0
    simp at h0
    have h1: a*(1-a)=a^2*(a⁻¹-1)
    rw [mul_sub,mul_sub]
    simp
    have h2:a= a ^ 2 * a⁻¹
    rw [sq,mul_inv_cancel_right₀]
    exact h0
    rw [← h2,sq]
    rw [h1]
    simp
    have h3:quadraticCharFun (ZMod p) a ^ 2=1
    apply quadraticChar_sq_one h0
    rw [h3]
    simp

  _=∑ a in {x : ZMod p | x ≠ -1}.toFinset,(quadraticChar (ZMod p) a) + p := by
    simp
    symm
    let g:ZMod p→ ZMod p := fun x => x⁻¹-1
    have h1:{x : ZMod p | x ≠ -1}.toFinset=Finset.image g {x : ZMod p | x ≠ 0}.toFinset
    ext x
    rw [mem_toFinset,Finset.mem_image]
    simp
    constructor
    intro h0
    use (x+1)⁻¹
    rw [mem_toFinset]
    simp
    contrapose! h0
    rw [← sub_zero x,← h0]
    simp
    intro h1
    cases' h1 with a h1
    rw [mem_toFinset] at h1
    simp at h1
    cases' h1 with h1 h2
    contrapose! h1
    rw [h1] at h2
    simp at h2
    exact h2
    rw [h1]
    apply sum_image
    intro x _ y _ h4
    simp at h4
    exact h4

  _=p - legendreSym p (-1) := by
    have h1 : {x : ZMod p | x ≠ -1}.toFinset = erase univ.toFinset (-1)
    ext x
    simp
    rw [mem_toFinset]
    simp
    rw [h1,sum_erase_eq_sub,sum_of_quadraticChar,add_comm,sub_eq_add_neg (p:ℤ),add_left_cancel_iff]
    simp
    symm
    have h3:legendreSym p (-1)=legendreSym p (-1:ZMod p)
    rw [legendreSym.mod,legendreSym.mod p ↑(-1:ZMod p)]
    have h4:-1 % ↑p=↑(-1:ZMod p) % (↑p:ℤ)
    rw [← ZMod.int_cast_eq_int_cast_iff']
    simp
    rw [h4]
    rw [h3]
    apply legendreSym_eq_quadraticChar
    assumption
    simp

  _=↑p - (-1) ^ ((p-1)/2) := by
    have h1:= Nat.Prime.mod_two_eq_one_iff_ne_two.mpr p_odd
    rw [legendreSym.at_neg_one,ZMod.χ₄_eq_neg_one_pow]
    repeat swap;assumption
    have h5:p-1+1=p
    cases' p with p
    simp at h1
    rw [Nat.succ_sub_one]
    have h2:p /2=(p-1)/2
    have h3: (p-1)%2=0
    have h4:=Nat.mod_two_add_succ_mod_two (p-1)
    rw [h5,h1] at h4
    simp at h4
    exact h4
    rw [← Nat.div_add_mod (p-1) 2] at h5
    nth_rw 3 [← Nat.div_add_mod p 2] at h5
    rw [h1,h3] at h5
    simp at h5
    symm
    exact h5
    rw [h2]

lemma card_sol : Int.ofNat (@sol p _).card = p - (-1)^((p-1)/2) := by
  rw [comp1, comp2]
  repeat assumption
