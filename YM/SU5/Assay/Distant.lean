import YM.SU5.Assay.SeenBox
import YM.SU5.Assay.Lamp
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
variable {P:Spine}{j:Axis}{s v w:ℕ}{f g:P.Test}
local notation "Λ"=> P.par
local notation "Y"=> P.run
local notation "K"=> P.calibration
local notation "H"=> P.large
local notation "b"=> ruler (Λ).block
local notation "V"=> P.law
local notation "L"=> (Λ).R.L.val
local notation "π"=> P.history
local notation "Qt"=> P.projection.clipped
local notation "C₀"=> P.room j
local notation "σ"=> P.shifts j

local notation "μ"=> P.meanBox
local notation "ν"=> P.euclOp
local notation "T"=> P.shiftOp
local notation "Ν"=> whenly (timeMesh (Λ))
local notation "Ω"=> P.floorVec
local notation "S"=> enclave K
variable (P j s)
lemma heats_join (t u:ℝ≥0): ν j (t+u)=ν j t * ν j u:=advance_smag ..
lemma heats_star (t:ℝ≥0): star (ν j t)=ν j t:=advance_adjoint ..
lemma heat_floor (t:ℝ≥0):ν j t (Ω j)=Ω j:= advance_vacuum ..

/-- Euclidean forward difference at distant horizons. -/
lemma distant (u:ℝ≥0):Tendsto (fun n:ℕ=>ν j (u+Ν s n)-ν j (Ν s n)) atTop (𝓝 0):=by
 let a(n):ℝ:= Ν s n
 have hp:Tendsto a atTop atTop:= by
   have h:0<((mill (timeMesh Λ) s):ℝ):=mill_pos _ _
   simpa only [a,whenly,NNReal.coe_mul,NNReal.coe_natCast] using
    (tendsto_natCast_atTop_atTop (R:=ℝ)).atTop_mul_const' h
 let X:= (clockdrive Y H V (π).circuit j 0 false C₀).monoAxis j
 have h':Tendsto (fun n=> 2/a n* ‖(u:ℝ)‖) atTop (𝓝 0):=by
   simpa using (tendsto_const_nhds.div_atTop hp (a:=(2:ℝ))).mul_const ‖(u:ℝ)‖
 apply squeeze_zero_norm' _ h'
 filter_upwards [hp.eventually (eventually_gt_atTop 0)] with n p
 have h' : a n≤ ↑(u+Ν s n:ℝ≥0):=NNReal.coe_le_coe.mpr (le_add_self)
 have z:= X.wax_shaking p h' le_rfl
 unfold OS.Semigroup.wax a at z
 rw [Real.toNNReal_coe,Real.toNNReal_coe,NNReal.coe_add,add_sub_cancel_right] at z
 exact z

lemma warms_to_all (x:P.Hil j)(p:ν j (Ν s 1) x=x)(t:ℝ≥0): ν j t x=x:=by
 have u (n:ℕ):ν j (Ν s n) x=x:=by
   induction n with
   | zero=>rw [when_zero,euclOp,advance_source]; rfl
   | succ n h=>rw [when_add,P.heats_join,ContinuousLinearMap.mul_apply,p,h]
 have h:= ((continuous_id.clm_apply (continuous_const (y:=x))).tendsto (0:(P.Hil j).Op)).comp (P.distant j s t)
 change Tendsto (fun n=>(ν j (t+Ν s n)-ν j (Ν s n)) x) atTop (𝓝 (0:(P.Hil j))) at h
 have z: ν j t x - x =0:=by
   refine tendsto_nhds_unique tendsto_const_nhds (h.congr (fun n=>?_))
   simp only [ContinuousLinearMap.sub_apply,P.heats_join,ContinuousLinearMap.mul_apply,u]
 exact sub_eq_zero.mp z
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
