import YM.CF.Mir.Motion

/-! Spin flips and sea-sector interchange. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Mir
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology Kronecker
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant MeasureTheory Phase Finset
attribute [local instance] opCStarAlgebra
variable {N m B : Side}
section
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
lemma reblock (A : I→Op J) : jump (Equiv.refl I) A=Matrix.reindex (Equiv.prodComm J I) (Equiv.prodComm J I) (Matrix.blockDiagonal A) := by
  ext i j; by_cases g:i.1=j.1 <;> simp [jump_apply,Matrix.blockDiagonal,g,Matrix.reindex_apply]
lemma jump_det (A : I→Op J) : (jump (Equiv.refl I) A).det=∏ i:I,(A i).det := by rw [reblock,Matrix.det_reindex_self,Matrix.det_blockDiagonal]
lemma Safe.inverseF [Nonempty I] {A : Op I} (h : Safe A) : Safe (-A) := ⟨h.self.neg,(by rw [norm_neg]; exact h.bound),(by rw [neg_sq]; exact h.margin)⟩
lemma minusP [Nonempty I] {A : Op I} (h : Safe A) : projector (-A)=1-projector A := by
  unfold projector polarity; have hp : rsEval (-A)=rsEval A := by unfold rsEval; simp_rw [rsTerm,slack,neg_sq]
  rw [hp, smul_neg,neg_mul]; module
end
-- fixed orientation
lemma field_det_match {x y : Site N→Vect} (h : ∀ i, ‖x i‖=1) (g : ∀ i, ‖y i‖=1) : (Cfield x).det = (Cfield y).det := by
  unfold Cfield; simp only [jump_det,localPair,Matrix.det_kronecker]; refine prod_congr rfl ?_; intro i _; rw [(SU.Pair.full_laws (x i) (h i)).2.1, (SU.Pair.full_laws (y i) (g i)).2.1]

def pin (i : Axis) : Op SpinIdx := gammaOp i*grading
lemma pinS (i) : star (pin i)= -pin i := by rw [pin,star_mul,gammaAdj,gradingAdj, gradingSwap] -- adj order
lemma pin_square (i) : pin i*pin i= -1 := by
  let A := gammaOp i; let B := grading
  unfold pin; change A*B*(A*B)=_
  rw [←mul_assoc,mul_assoc A,show B*A= -(A*B) from gradingSwap i,mul_neg,neg_mul,← mul_assoc A A, gammaOne,one_mul, gradingOne] -- tune
lemma pin_U (i) : pin i∈unitary _ := by constructor <;> simp [pinS,pin_square]
def pinM (N : Side) (i : Axis) : UNI (Model N) := ⟨spin N Slot (pin i),jump_unitary _ _ (fun x=> Matrix.kronecker_mem_unitary (pin_U i) (one_mem (unitary (Op Slot))))⟩
lemma pin_grades (i : Axis) : twist (pinM N i) (spin N Slot grading)= -(spin N Slot grading) := by
  apply twist_comm; change spin N Slot _ * _= _ * spin N Slot _; rw [← spin_neg,spin_mul,spin_mul,pin]
  apply congrArg
  rw [neg_mul, ←mul_assoc, gradingSwap, neg_mul,neg_neg]
lemma pin_self (i : Axis) : twist (pinM N i) (spin N Slot (gammaOp i))= -(spin N Slot (gammaOp i)) := by
  apply twist_comm; change spin N Slot _ * _= _ * spin N Slot _; rw [← spin_neg,spin_mul,spin_mul,pin]; apply congrArg; rw [mul_assoc, gradingSwap,mul_neg, neg_mul]
lemma pin_other (i j : Axis) (h : i≠j) : twist (pinM N i) (spin N Slot (gammaOp j))=spin N Slot (gammaOp j) := by
  apply twist_comm; change spin N Slot _ * _= _*spin N Slot _; rw [spin_mul,spin_mul,pin]
  apply congrArg; rw [mul_assoc,gradingSwap,mul_neg,← mul_assoc,gammaSwap i j h, neg_mul,neg_neg,mul_assoc]
lemma pin_shift (i j : Axis) (U : Bkg N) (c : Site N) : twist (pinM N i) (shift matter U c j)=shift matter U c j := twist_comm _ _ _ (spin_shift ..).eq -- syntax tune
lemma pin_field (i : Axis) (v : Site N →Vect) : congrC (pinM N i) (Cfield v)=Cfield v := by
  let C := pinM N i
  have he : pin i * spinJ=spinJ * cc (pin i) := by rw [pin,mul_assoc,spinJ_grading, ←mul_assoc, spinJ_inter,cc_mul,mul_assoc]
  have hm : C.val * Cfield v=Cfield v*(ccU C).val := inter_spin v _ he
  rw [congr_form,hm,mul_assoc,show (ccU C).val*star _=1 from (ccU C).property.2,mul_one]
section
variable {I : Type*} [Fintype I] [DecidableEq I]
lemma congr_layers (U V : UNI I) (C : Op I) : congrC (U*V) C=congrC U (congrC V C) := by
  unfold congrC; change U.val*V.val*C*(U.val*V.val)ᵀ= _; rw [Matrix.transpose_mul]; simp [mul_assoc]
end
namespace Trip
variable (b : Trip m) {U : Skin m B}
def pinTrip (i : Axis) (B : Side) := pinM _ i*siteM (fperm m B b)
lemma seaH (i : Axis) (h : ∀ j, b.glare j=true ↔ j=i) (U : Skin m B) (c : Phase.Part m B) :
    twist (b.pinTrip i B) (wiel m B c U)= -(wiel m B (far B b c) (through B b U)) := by
  let A := b.pinTrip i B
  let F := frame matter (links U) c; let T := frame matter (links (through B b U)) (far B b c)
  have he j : twist A (F.inc j)= T.inc j := by
    let X := F.T j; let Y := T.T j
    by_cases l:j=i
    · subst j
      have hm : twist A X=star Y := by unfold A pinTrip; rw [Fock.twin, show twist _ X=star Y from (tram B b U c i).trans (if_pos ((h i).mpr rfl)),map_star, show twist (pinM _ i) Y=Y from pin_shift i i _ _] -- tune
      have hx : twist A (F.gamma i)= -T.gamma i := by unfold A pinTrip; rw [Fock.twin, show twist (siteM _) (F.gamma i)=T.gamma i from siteSpin ..]; exact pin_self _
      unfold WilsonFrame.inc WilsonFrame.diff WilsonFrame.lap; simp only [map_mul,map_add,map_sub,map_one,map_smul,map_star,hx]
      rw [show twist A (F.T i)=star (T.T i) from hm,star_star, add_comm (star _), show star (T.T i)-T.T i= -(T.T i-star (T.T i)) by abel,smul_neg,neg_mul_neg]
    have hm : twist A X=Y := by unfold A pinTrip; rw [Fock.twin, show twist (siteM _) X=Y from (tram B b U c j).trans (if_neg (fun g=>l ((h j).mp g)))]; exact pin_shift ..
    have hx : twist A (F.gamma j)=T.gamma j := by unfold A pinTrip; rw [Fock.twin, show twist (siteM _) (F.gamma j)= T.gamma j from siteSpin ..]; exact pin_other i j (Ne.symm l)
    unfold WilsonFrame.inc WilsonFrame.diff WilsonFrame.lap; simp only [map_mul,map_add,map_sub,map_one,map_smul,map_star,hx]; rw [show twist A (F.T j)=T.T j from hm]
  have hp : twist A F.chir= -T.chir := by rw [show A=pinM _ i*siteM (fperm m B b) from rfl,Fock.twin, show twist (siteM _) F.chir=T.chir from siteSpin ..]; exact pin_grades i
  change twist A F.H= -T.H; unfold WilsonFrame.H WilsonFrame.H0; rw [map_mul,map_add,map_neg,map_one,map_sum,hp]; simp_rw [he, neg_mul]
lemma careH (h : ∀ j, b.glare j=false) (U : Skin m B) (c : Phase.Part m B) :
    twist (siteM (fperm m B b)) (wiel m B c U)=wiel m B (far B b c) (through B b U) := by
  let V := siteM (fperm m B b); let F := frame matter (links U) c; let T := frame matter (links (through B b U)) (far B b c)
  have he j : twist V (F.T j)=T.T j := (tram B b U c j).trans (if_neg (by rw [h j]; decide))
  have ht j : twist V (F.inc j)=T.inc j := by
    unfold WilsonFrame.inc WilsonFrame.lap WilsonFrame.diff; simp only [map_mul, map_sub,map_add,map_one,map_star,map_smul,he,show ∀ j, twist V (F.gamma j)=T.gamma j from fun _=> siteSpin ..]
  change twist V F.H=T.H; unfold WilsonFrame.H WilsonFrame.H0; simp only [map_mul,map_add,map_neg,map_one, show twist V F.chir=T.chir from siteSpin .., map_sum,ht]
lemma shade_pin (U : Skin m B) (s : ArrayF m) q (i) : bow m B (through B b U) (b.riseF s) q=congrC (pinTrip b i B) (bow m B U s q) := by rw [bow,played, pinTrip,congr_layers,bow,siteField,pin_field]
end Trip
end YM.CF.Mir
