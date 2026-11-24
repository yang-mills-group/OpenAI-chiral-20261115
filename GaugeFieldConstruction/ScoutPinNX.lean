import YM.SU5.Celeste.Banquet
-- recheck/spell out private helpers from Banquet.Lead for new spin applications
set_option autoImplicit false
set_option maxHeartbeats 470000
noncomputable section
namespace YM.CF.Buffered.Ballad
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Lifted Bilinear Window Skye
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
variable {R:ℕ}{B N:Side}
open YM.CF.Lamour.Bridge.Celeste
open Py.Rate.LocalLimit.Papal (Weaver household)
open Kea
open Flare
namespace Lead
variable (i:Axis)
def bkNX_scaledn (a:Fin 2):ℂ := pin i (upSpin (shuffle i a)) (dnSpin a)
def bkNX_scaleup (a:Fin 2):ℂ := pin i (dnSpin (shuffle i a)) (upSpin a)
@[local simp] lemma bkNX_sh00 : shuffle 0 0=1 := by decide
@[local simp] lemma bkNX_sh01 : shuffle 0 1=0 := by decide
@[local simp] lemma bkNX_sh10 : shuffle 1 0=1 := by decide
@[local simp] lemma bkNX_sh11 : shuffle 1 1=0 := by decide
@[local simp] lemma bkNX_sh20 : shuffle 2 0=0 := by decide
@[local simp] lemma bkNX_sh21 : shuffle 2 1=1 := by decide
@[local simp] lemma bkNX_sh30 : shuffle 3 0=0 := by decide
@[local simp] lemma bkNX_sh31 : shuffle 3 1=1 := by decide
@[local simp] lemma bkNX_upp0 : upSpin 0=0 := by decide
@[local simp] lemma bkNX_dwn0 : dnSpin 0=2 := by decide
@[local simp] lemma bkNX_upp1 : upSpin 1=1 := by decide
@[local simp] lemma bkNX_dwn1 : dnSpin 1=3 := by decide
set_option maxHeartbeats 1200000 in
lemma bkNX_pinned (j:SpinIdx)(a:Fin 2) : pin i j (upSpin a)=(if j=dnSpin (shuffle i a) then bkNX_scaleup i a else 0) ∧ pin i j (dnSpin a)=(if j=upSpin (shuffle i a) then bkNX_scaledn i a else 0):=by
 fin_cases i <;> fin_cases j <;> fin_cases a <;> norm_num [pin,bkNX_scaledn,bkNX_scaleup, show (⟨0,by decide⟩:Axis)=(0:Axis) from rfl,show (⟨1,by decide⟩:Axis)=(1:Axis) from rfl,show (⟨2,by decide⟩:Axis)=(2:Axis) from rfl,show (⟨3,by decide⟩:Axis)=(3:Axis) from rfl, Matrix.cons_val_zero, Axis, Fin.ext_iff, gammaOp,grading,Matrix.mul_apply,SpinIdx,Fin.sum_univ_succ]
 all_goals norm_num [show Fin.addNat (0:Fin 2) 2 = (2:Fin 4) from rfl,show Fin.addNat (1:Fin 2) 2 = (3:Fin 4) from rfl,show (2:Fin 4)=Fin.succ (1:Fin 3) from rfl,show (3:Fin 4)=Fin.succ (2:Fin 3) from rfl,show (2:Fin 3)=Fin.succ (1:Fin 2) from rfl]
 all_goals simp only [show (2:Fin 4)=Fin.succ (1:Fin 3) from rfl,show (3:Fin 4)=Fin.succ (2:Fin 3) from rfl,show (2:Fin 3)=Fin.succ (1:Fin 2) from rfl, Matrix.cons_val_succ]; norm_num
 all_goals first | rfl | exact ⟨rfl,rfl⟩ | (simp only [show (2:Fin 4)=Fin.succ (1:Fin 3) from rfl,show (3:Fin 4)=Fin.succ (2:Fin 3) from rfl,show (2:Fin 3)=Fin.succ (1:Fin 2) from rfl,Matrix.cons_val_succ]; norm_num)

lemma bkNX_paid (a:Fin 2): -(bkNX_scaledn i a*star (bkNX_scaleup i a))=(if i=3 then (1:ℂ) else -1):=by
 fin_cases i <;> fin_cases a <;> norm_num [pin,bkNX_scaledn,bkNX_scaleup, show (⟨0,by decide⟩:Axis)=(0:Axis) from rfl,show (⟨1,by decide⟩:Axis)=(1:Axis) from rfl,show (⟨2,by decide⟩:Axis)=(2:Axis) from rfl,show (⟨3,by decide⟩:Axis)=(3:Axis) from rfl, Matrix.cons_val_zero, Axis, Fin.ext_iff, gammaOp,grading,Matrix.mul_apply,SpinIdx,Fin.sum_univ_succ]
 all_goals norm_num [show Fin.addNat (0:Fin 2) 2 = (2:Fin 4) from rfl,show Fin.addNat (1:Fin 2) 2 = (3:Fin 4) from rfl,show (2:Fin 4)=Fin.succ (1:Fin 3) from rfl,show (3:Fin 4)=Fin.succ (2:Fin 3) from rfl,show (2:Fin 3)=Fin.succ (1:Fin 2) from rfl]
 all_goals simp only [show (2:Fin 4)=Fin.succ (1:Fin 3) from rfl,show (3:Fin 4)=Fin.succ (2:Fin 3) from rfl,show (2:Fin 3)=Fin.succ (1:Fin 2) from rfl, Matrix.cons_val_succ]; norm_num
 all_goals first | rfl | exact ⟨rfl,rfl⟩ | (simp only [show (2:Fin 4)=Fin.succ (1:Fin 3) from rfl,show (3:Fin 4)=Fin.succ (2:Fin 3) from rfl,show (2:Fin 3)=Fin.succ (1:Fin 2) from rfl,Matrix.cons_val_succ]; norm_num)

#print axioms bkNX_pinned
#print axioms bkNX_paid
end Lead
end YM.CF.Buffered.Ballad
end
