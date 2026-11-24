import GaugeFieldConstruction.Atoms
/-!
# Changing arguments with handedness or active designation
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Stage
open Cauchy Row Phys Function Matrix
open scoped Matrix Matrix.Norms.Frobenius Kronecker BigOperators Topology ContDiff
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
namespace Cell
variable (A : Labels α) (B : Labels β)

def beacon (s : Signed): Module.End ℂ (J α):= jet fun i=> YM.GaugeFieldConstruction.pay (A.cost s i) (ket (A.move s i))
lemma beacon1 : beacon A 1=LinearMap.id:= ket_ext fun i=>by simp [beacon]
lemma beacon_spin (s t) : beacon A (s*t)=beacon A s ∘ₗ beacon A t:= ket_ext (fun i=>by
  change beacon A (s*t) _=(beacon A s ∘ₗ beacon A t) _
  rw [beacon, LinearMap.comp_apply,beacon,beacon,on_ket,on_ket,A.move_mul, A.cost_mul]
  cases A.cost t i <;> cases e:A.cost s (A.move t i) <;> simp [e])
lemma twistB (s) (w : J α) : beacon A.twist s w=YM.GaugeFieldConstruction.pay (signBit s) (beacon A s w) := by
  cases p : signBit s
  · have H : beacon A.twist s=beacon A s := ket_ext fun i=>by simp only [beacon,on_ket,Labels.twist,p,Bool.false_xor]
    rw [H]; rfl
  have H : beacon A.twist s= -beacon A s:= ket_ext (fun i=>by simp only [LinearMap.neg_apply,beacon,on_ket,Labels.twist,p]; cases A.cost s i <;> simp)
  rw [H]; rfl
lemma beacon_cross (s) (i j) : beacon (A.tensorProd B) s (times' i j)= times' (beacon A s i) (beacon B s j) := by
  have H : beacon (A.tensorProd B) s=Phys.strap (beacon A s) (beacon B s) := crossing fun i j=>by
    rw [Phys.straps,takes]; simp only [beacon,on_ket,Labels.tensorProd]
    cases A.cost s i <;> cases B.cost s j <;> simp
  rw [H,straps]
lemma beacon_l (s p) : beacon (A.directSum B) s (leftU p)=leftU (beacon A s p) := by
  have H : beacon (A.directSum B) s ∘ₗ leftU=leftU ∘ₗ beacon A s:= ket_ext fun i=>by
    simp only [LinearMap.comp_apply, leftU,on_ket,beacon,Labels.directSum,Sum.elim_inl, Sum.map_inl]; cases A.cost s i <;> simp [YM.GaugeFieldConstruction.pay]
  exact LinearMap.congr_fun H _
lemma beacon_r (s p) : beacon (A.directSum B) s (rightU p)=rightU (beacon B s p) := by
  have H : beacon (A.directSum B) s ∘ₗ rightU=rightU ∘ₗ beacon B s:= ket_ext fun i=>by simp only [LinearMap.comp_apply,rightU,on_ket,beacon,Labels.directSum,Sum.elim_inr,Sum.map_inr]; cases B.cost s i <;> simp [YM.GaugeFieldConstruction.pay]
  exact LinearMap.congr_fun H _

/-- Actual argument covariance. `Fast` for Lie action, `Match` proper H action. -/
def Fast (P : Cell α) := ∀ (s : Signed) B i, beta P (conjS s.ortho B) (beacon A s i) = beacon A s (beta P B i) -- annotate

def Match (P : Cell α):=∀ s : Signed, signBit s=false→∀ i,bill (P.active s.ortho) i=beacon A s i

variable {A B} {P : Cell α} {Q : Cell β}
-- s det for V version incl improper matches natural
lemma axis_l (s : Signed) (p): bill s.ortho.val p=beacon Raw.v s p := by
  have h: bill s.ortho.val=beacon Raw.v s := ket_ext fun i=> by
    rw [beacon,on_ket]; ext1 j; rw [entry]; change (↑(s.matrix j i):ℂ)=_
    rw [Signed.matrix_at]; by_cases v:s.perm i=j <;> cases e:s.flip i <;> simp [v,e,ket,Finsupp.single_apply]
  rw [h]
lemma merit : Match Raw.v UnitV := fun s _ i=>axis_l ..
lemma brisk : Fast Raw.v UnitV := by
  intro s B i; rw [← axis_l,← axis_l]
  suffices H : UnitV.beta (conjS s.ortho B) * bill s.ortho.val=bill s.ortho.val * UnitV.beta B by exact LinearMap.congr_fun H _
  change bill _ * bill _=bill _*bill _; rw [success,success]; congr 1
  change s.ortho.val*B.val*star s.ortho.val*s.ortho.val=s.ortho.val*B.val; rw [mul_assoc (s.ortho.val*B.val), s.ortho.property.1,mul_one]
lemma match_twist (h : Match A P):Match A.twist P:= fun s v i=>by rw [twistB,v]; exact h s v i
lemma fast_twist (p : Fast A P):Fast A.twist P:= by
  intro s v i; rw [twistB,twistB]; cases signBit s <;> simp only [pay_true,pay_false,map_neg] <;> rw [p s v]
lemma stoke (P : Cell α) (Q : Cell β) (u r p) : beta (P.sum Q) u (leftU r+rightU p)= leftU (P.beta u r)+rightU (Q.beta u p) := by
  have e: beta (P.sum Q) u ∘ₗ leftU=leftU ∘ₗ beta P u:= ket_ext fun i=>by change beta (P.sum Q) u (leftU _) = _; rw [leftU,on_ket]; exact input1 P Q u i
  have f: beta (P.sum Q) u ∘ₗ rightU=rightU ∘ₗ beta Q u:= ket_ext fun i=>by change beta (P.sum Q) u (rightU _)=_; rw [rightU,on_ket]; exact input2 ..
  rw [map_add,← LinearMap.comp_apply,e,← LinearMap.comp_apply _ rightU,f]; rfl
lemma match_cross (h : Match A P) (p : Match B Q): Match (A.tensorProd B) (P.wings Q) := by
  intro s hS i; apply LinearMap.congr_fun (ket_ext fun v=>?_)
  rw [← takes v.1 v.2]; change bill (_ ⊗ₖ _) _=_; rw [cran,h s hS,p s hS,beacon_cross]
lemma fast_cross (h : Fast A P) (p : Fast B Q): Fast (A.tensorProd B) (P.wings Q) := by
  intro s V i; have H : beta (P.wings Q) (conjS s.ortho V) ∘ₗ beacon (A.tensorProd B) s=beacon (A.tensorProd B) s ∘ₗ beta (P.wings Q) V := by
    apply crossing; intro i j; rw [optionB,optionB]; simp only [LinearMap.comp_apply,beacon_cross,split_legs,map_add]
    rw [h s V,p s V]
  exact LinearMap.congr_fun H _
lemma match_sum (h : Match A P) (p : Match B Q): Match (A.directSum B) (P.sum Q) := by
  intro s g i; apply LinearMap.congr_fun (f:=bill ((P.sum Q).active s.ortho))
  apply ket_ext; intro x
  cases x with
  | inl v=>
    have hp : bill ((P.sum Q).active s.ortho) (ket (.inl v))=leftU (bill (P.active s.ortho) (ket v)) := by simp only [bill,on_ket,leftU,map_sum,map_smul,Fintype.sum_sum_type,Cell.sum]; simp
    rw [hp,h s g,← beacon_l A B]; simp [leftU]
  | inr v=>
    have hp: bill ((P.sum Q).active s.ortho) (ket (.inr v))=rightU (bill (Q.active s.ortho) (ket v)) := by simp only [bill,on_ket,rightU,map_sum,map_smul,Fintype.sum_sum_type,Cell.sum]; simp
    rw [hp,p s g,← beacon_r A B]; simp [rightU]
lemma fast_sum (h : Fast A P) (p : Fast B Q): Fast (A.directSum B) (P.sum Q) := by
  intro s V i; have H : beta (P.sum Q) (conjS s.ortho V) ∘ₗ beacon (A.directSum B) s=beacon (A.directSum B) s ∘ₗ beta (P.sum Q) V := by
    have ht a b : beta (P.sum Q) (conjS s.ortho V) (beacon (A.directSum B) s (leftU a+rightU b))=beacon (A.directSum B) s (beta (P.sum Q) V (leftU a+rightU b)) := by rw [map_add, beacon_l,beacon_r, stoke P Q, stoke P Q, h s V,p s V,map_add,beacon_l,beacon_r]
    apply ket_ext; intro j; simp only [LinearMap.comp_apply]; rcases j with w|w
    · rw [show ket (Sum.inl (β:=β) w)=leftU (ket w)+rightU 0 from by simp [leftU]]; apply ht
    rw [show ket (Sum.inr (α:=α) w)=leftU 0+rightU (ket w) from by simp [rightU]]; apply ht
  exact LinearMap.congr_fun H _
end Cell
end YM.GaugeFieldConstruction.Stage
