import GaugeFieldConstruction.RanksAll

/-!
# Compute (97) in the on-shell price. Includes nonvanishing,
 rank-axis interpretation. Not using the physical tensor price yet.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 6000
noncomputable section
namespace YM.GaugeFieldConstruction
open Cauchy Row Raw Record Calibration U1 Vouchers Function Finset Submodule
open scoped BigOperators
namespace U1
namespace Gauge97
lemma turnover (i j : Axis) : F i j = -F j i := by
  apply ext_jet loyalty
  intro x
  let w:=Chart.face x.1.val x.2
  change w.read (F _ _)=w.read _
  rw [map_neg, Maxwell.read_F, Maxwell.read_F,Maxwell.alternate,neg_mul]
lemma zero_angle (i : Axis) : F i i=0 := by
  apply loyalty _
  intro x
  rw [LinearMap.mem_ker]; change (x.1.val.face x.2).read (F i i)=0
  rw [Chart.wedge_formula]; simp [Chart.area]

def bill (i j : Axis) := ∑ k,P_pair i j k
where P_pair i j k := Bose (F i k) (F j k)
def recorded (i j : Axis) := (4:ℂ) • bill i j - if i=j then ∑ k:Axis,bill k k else 0
def Root (s : Raw.Sym) := recorded s.val.1 s.val.2
lemma uniform (i j : Axis) : recorded i j = recorded j i := by
  have h : bill i j=bill j i := Finset.sum_congr rfl fun s _=>bose_swap ..
  rw [recorded,recorded,h]; simp only [eq_comm (a:=i) (b:=j)]
lemma ordered_bill (i j : Axis) : Root (ordered i j)=recorded i j := by
  unfold ordered; split; exact uniform ..; rfl

private lemma same_m (s : Signed) (w : Maxwell) (i k : Axis) : (Maxwell.still s w).point.read (F i k)=
    pay ((s.flip i).xor (s.flip k)) (w.read (F (s.perm i) (s.perm k))) := by
  rw [Maxwell.read_F,Maxwell.read_F]
  simp only [power,Prod.fst_zero,Prod.snd_zero, pow_zero,mul_one]
  exact (Maxwell.still s w).create ..
private lemma curves {s w u} (h : recG.poses s w u) (i j : Axis) :
    recG.tester u (bill i j) = pay ((s.flip i).xor (s.flip j)) (recG.tester w (bill (s.perm i) (s.perm j))) := by
  unfold bill; change productRead u.1.read u.2.read _= pay _ (productRead w.1.read w.2.read _)
  rw [show u.1=_ from h.1, show u.2=_ from h.2,map_sum,map_sum, Record.feePay]
  conv_rhs=> rw [← Equiv.sum_comp s.perm]
  apply Finset.sum_congr rfl
  intro k _; rw [bill.P_pair,bose_charge,bill.P_pair,bose_charge]; repeat rw [same_m]
  cases s.flip i <;> cases s.flip j <;> cases s.flip k <;> simp only [Bool.false_xor,Bool.true_xor,Bool.not_true,Bool.not_false,pay_false,pay_true, neg_mul,mul_neg,neg_neg,neg_add]
private lemma bose_r (x y : GJet) : Bose x (-y)= -Bose x y := by simp only [Bose,map_neg,LinearMap.neg_apply]; abel
private lemma bose_l (x y : GJet) : Bose (-x) y= -Bose x y := by simp only [Bose,map_neg,LinearMap.neg_apply]; abel
private lemma ink (i j k : Axis) : Bose (F i k) (F j k) ∈ gFour := by
  by_cases h:i=k; subst k; simp [zero_angle,Bose]
  by_cases p:j=k; subst k; simp [zero_angle,Bose]
  have he (a c: Wed) : Bose (arc a) (arc c)∈gFour := by
    unfold gFour space; rw [Fintype.range_linearCombination]; apply subset_span
    refine ⟨ordered a c,?_⟩; unfold ordered; split; exact bose_swap ..; rfl
  rcases lt_or_gt_of_ne h with v|v <;> rcases lt_or_gt_of_ne p with w|w
  · exact he (Wed.mk i k v) (Wed.mk j k w)
  · rw [turnover j k, bose_r]
    exact gFour.neg_mem (he (Wed.mk _ _ v) (Wed.mk _ _ w))
  · rw [turnover i k, bose_l]
    exact gFour.neg_mem (he (Wed.mk _ _ v) (Wed.mk _ _ w))
  -- avoid second rewriting same if i=j, simultaneous conv
  change Bose (F _ _) (F _ _)∈ _
  conv_rhs => lhs; rw [turnover i k]
  conv_rhs => rhs; rw [turnover j k]
  rw [show Bose (-F k i) (-F k j)=Bose (F k i) (F k j) from by simp [Bose]]
  exact he (Wed.mk _ _ v) (Wed.mk _ _ w)

lemma root_ok : Root ∈ TT recG gFour := by
  constructor
  · intro s w u h i
    have hx := ordered_same i
    let a:=i.val.1; let b:=i.val.2
    rw [← show ordered a b=i from hx, fee_turn,sym_turn,ordered_bill,ordered_bill]
    unfold recorded; rw [map_sub,map_sub,map_smul, map_smul]
    rw [curves h]
    by_cases hp : a=b
    · rw [hp]; simp only [ite_true,map_sum,Bool.xor_self,pay_false]; congr 1
      conv_rhs=> rw [← Equiv.sum_comp s.perm]
      apply sum_congr rfl; intro j _; rw [curves h,Bool.xor_self,pay_false]
    rw [if_neg hp,if_neg (s.perm.injective.ne hp),map_zero,map_zero,sub_zero,sub_zero]
    cases (s.flip a).xor (s.flip b) <;> simp
  intro i _; change recorded _ _∈ gFour
  have he i j : bill i j∈gFour:=Submodule.sum_mem _ (fun k _ => ink i j k)
  unfold recorded; split_ifs
  · exact gFour.sub_mem (gFour.smul_mem _ (he ..)) (Submodule.sum_mem _ fun j _=> he ..)
  exact gFour.sub_mem (gFour.smul_mem _ (he ..)) gFour.zero_mem
end Gauge97
end U1
end YM.GaugeFieldConstruction
