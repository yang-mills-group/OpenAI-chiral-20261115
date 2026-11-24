import GaugeFieldConstruction.GStress

/-! (97) nonzero and lies in the actual computed free jet kernel. -/
set_option autoImplicit false
namespace YM.GaugeFieldConstruction.U1
open Function Finset U1 Calibration Raw Cauchy Row Record Vouchers
open Vouchers.Camera Vouchers.Bill
open scoped BigOperators

namespace Gauge97
def spot (i j : Axis) : Bill GIndex :=
  if h : i < j then pixel (Wed.mk i j h) else if h : j < i then spend (-1) (pixel (Wed.mk j i h)) else []
lemma spot_pay (i j : Axis) : total (spot i j)=F i j := by
  unfold spot; split_ifs with h t
  · exact pixel_cost (Wed.mk i j h)
  · rw [cost,pixel_cost,turnover i j]; rw [Credit.opposite,Credit.one_c]; simp only [neg_smul, one_smul]; rfl
  have he:i=j := by order
  subst j; rw [zero_angle]; rfl

def geo (i j : Axis) : Bill Row.g := join axisList fun k => twice (spot i k) (spot j k)
private lemma take_a {X} (f : Axis → Bill X) : total (join axisList f)= ∑ i, total (f i) := by
  rw [take_join]; simp [axisList, Function.comp_def, Fin.sum_univ_succ]
lemma geo_pay (i j : Axis) : total (geo i j)=bill i j := by
  rw [geo, take_a]
  apply Finset.sum_congr rfl; intro c _; rw [twice,total_append,give,give,spot_pay,spot_pay]; rfl

def tax (s : Raw.Sym) := spend ⟨4,0⟩ (geo s.val.1 s.val.2) ++ if s.val.1=s.val.2 then spend (-1)
    (join axisList (fun i=>geo i i)) else []
lemma taxPay (s) : total (tax s)= Root s := by
  rw [tax,total_append,cost,geo_pay,Root,recorded]; split_ifs
  · rw [cost,take_a,Credit.opposite,Credit.one_c]; simp [geo_pay,Credit.money, sub_eq_add_neg]
  simp [total,Credit.money]

set_option synthInstance.maxSize 5000
lemma receipt : ∀ i, (Bill.norm (dimTest dg tax i)).isEmpty=true := by decide +kernel
lemma div_true : recG.divP Root=0 := by
  ext1 i
  rw [← dim_cost _ dg dg_c tax Root taxPay,← Bill.same, List.isEmpty_iff.mp (receipt i)]; rfl

lemma awake : Root ≠ 0 := by
  intro h
  let j : GIndex := (false,⟨(1,0,0,0),fun t=>(show False from (by decide : (1:S3)≠2) t).elim⟩)
  -- i=3 diagonal E all legs; coefficient nonzero
  let a := ordered τ τ
  have e : cash (j,j) (tax a)≠0 := by unfold j a; decide +kernel
  apply Credit.nonzero _ |>.mpr e
  rw [spendable,taxPay,h]; rfl
end Gauge97

namespace Spin97
noncomputable def element (i j : Axis) := L i (B j)+L j (B i)
noncomputable def Root (s : Raw.Sym) := element s.val.1 s.val.2
lemma element_o (i j : Axis) : Root (ordered i j)=element i j := by unfold ordered; split; exact add_comm ..; rfl
lemma root_ok : Root ∈ TT ph fFour := by
  constructor
  · intro s w u h i
    rw [← ordered_same i]; generalize i.val.1=a,i.val.2=b
    rw [fee_turn,sym_turn,element_o,element_o,element,element, map_add,map_add,pay_add]
    have he (i j:Axis) : ph.tester u (L i (B j)) = pay ((s.flip i).xor (s.flip j))
        (ph.tester w (L (s.perm i) (B (s.perm j)))) := by
      have hv:= readingTf.moving s w u h (j,Sum.inl i)
      change _ = pay (((signBit s).xor (s.flip j)).xor ((signBit s).xor (s.flip i))) _ at hv
      have hq : (((signBit s).xor (s.flip j)).xor ((signBit s).xor (s.flip i)))=(s.flip i).xor (s.flip j) := by
        cases signBit s <;> cases s.flip j <;> cases s.flip i <;> decide
      rw [hq] at hv; exact hv
    rw [he a b,he b a,Bool.xor_comm (s.flip b)]
  intro i _; apply (show space evalTf ≤ fFour from le_sup_right)
  rw [space,Fintype.range_linearCombination]; apply Submodule.add_mem
  exact Submodule.subset_span ⟨(i.val.2,Sum.inl i.val.1),rfl⟩
  exact Submodule.subset_span ⟨(i.val.1,Sum.inl i.val.2),rfl⟩

def tax (i : Raw.Sym) := f4Cost (i.val.2,Sum.inl i.val.1) ++ f4Cost (i.val.1,Sum.inl i.val.2)
lemma taxPay (s) : total (tax s)=Root s := by rw [tax,total_append,face4,face4]; rfl
set_option synthInstance.maxSize 5000 in
lemma receipt : ∀ i,(Bill.norm (dimTest (dp false) tax i)).isEmpty=true := by decide +kernel
lemma div_true : ph.divP Root=0 := by
  ext1 i; rw [← dim_cost _ (dp false) dp_c tax Root taxPay,← Bill.same,List.isEmpty_iff.mp (receipt i)]; rfl
lemma awake : Root≠0 := by
  intro h
  let j : Row.f:= ((0,1,0,0),(1,0,0,0))
  let a:=ordered (0:Axis) 0
  have e : cash j (tax a) ≠ 0 := by unfold j a; decide +kernel
  apply Credit.nonzero _ |>.mpr e
  rw [spendable,taxPay,h]; rfl
end Spin97
end YM.GaugeFieldConstruction.U1
