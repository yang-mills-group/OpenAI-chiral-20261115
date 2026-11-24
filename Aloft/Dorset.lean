import Ridgetop.Gw
import Crape.Halo
import Ridgetop.Origin
import Risa.Warehouse
import Preen.Chey
-- pilot price exactly zero, all. 
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option maxHeartbeats 360000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
namespace PledgeT
open Calico
open Aria Casting Set
open scoped Pointwise
open Calico
namespace MiterT
open _root_.YM.Gleam.Luster.Risa CF.BProof AnalyticBridge.VerifiedReset
open Py.Rate.LocalLimit Py Py.Dyad Papal _root_.YM.CF.Pannier.Chancel Cliplet Precision
variable (P:Spine) (s A:ℕ)(o:Bool→ Cover)(b:Bool)
namespace Aloft
open _root_.YM.Preen
local notation "SP" s:max=> P.spotMesh s
local notation "L"=> (P.par.R.L.val:ℝ)
local notation "τ"=>((timeMesh P.par).base:ℝ)
private lemma spotter(s:ℕ): (SP s)=τ/L^s:=by unfold spotMesh mill; rw [NNReal.coe_div,NNReal.coe_pow,NNReal.coe_natCast]; rfl
lemma sizeJoint : Tendsto (fun d:ℕ=> (girder P d:ℝ)*P.spotMesh (stackW d)) atTop (𝓝 0):=by
 have hl:1 < L:=by exact_mod_cast (show 1<P.par.R.L.val from P.par.R.coarse.trans_lt' (by norm_num))
 have hg:0<L:=zero_lt_one.trans hl
 obtain ⟨A,u,t⟩:=polyRise P
 let θ:= (L)⁻¹
 have he:‖θ‖<1:=by unfold θ; rw [norm_inv,Real.norm_of_nonneg hg.le,inv_lt_one₀ hg]; exact hl
 have ec: Tendsto (fun s:ℕ=> (1+(s:ℝ))^6*θ^s) atTop (𝓝 (0:ℝ)):=by
    let f(n:ℕ):= (n:ℝ)^6*θ^n
    have H0:Summable f:= summable_pow_mul_geometric_of_norm_lt_one _ he
    apply Summable.tendsto_atTop_zero
    apply Summable.congr ( ((summable_nat_add_iff 1).2 H0).mul_right θ⁻¹)
    intro n; unfold f; rw [Nat.cast_add,Nat.cast_one,pow_succ θ, mul_assoc _ _ θ⁻¹,mul_inv_cancel_right₀ (show θ ≠0 from (by unfold θ; positivity)),add_comm]
 have B:Tendsto (fun d:ℕ=> (1+(hikeV d:ℝ))^6 / (L)^(hikeV d)) atTop (𝓝 0):= by simpa only [θ,inv_pow,← div_eq_mul_inv,Function.comp_def] using ec.comp (show Tendsto hikeV atTop atTop from goes_town)
 let v:= ((idleCar P):ℝ)
 refine squeeze_zero (fun d=>by have he:0 ≤ P.spotMesh (stackW d):=(spotMesh_pos ..).le; positivity) (g:=fun d=> (A+v)*((1+(hikeV d:ℝ))^6/L^(hikeV d))*τ) (fun d=>?_) ?_
 · unfold girder; rw [travelCast, spotter P (stackW d),show stackW d=hikeV d+stairW d from rfl,pow_add]
   let K:=L^(stairW d); let J:= L^(hikeV d); let Z:= (1+(hikeV d:ℝ))^6; have hp: 1 ≤ 1+(hikeV d:ℝ):=by have h:0 ≤ ((hikeV d:ℕ):ℝ):=Nat.cast_nonneg _; linarith
   have he:1 ≤ Z:=one_le_pow₀ hp
   change (K*(reachQ P (hikeV d):ℝ)+v)*(τ/(J*K))≤(A+v)*(Z/J)*τ
   have hv:0≤v:=Nat.cast_nonneg _; have ht:0 ≤ τ:= NNReal.coe_nonneg _
   have hk:1 ≤ K:=one_le_pow₀ hl.le; have hj:0<J:=pow_pos hg _
   calc _ = (τ/J)*( (reachQ P (hikeV d):ℝ) + v/K):= by field_simp [hj.ne', show K≠0 from (lt_of_lt_of_le zero_lt_one hk).ne']
        _ ≤ (τ/J)*(A*Z+v*Z):=by apply mul_le_mul_of_nonneg_left _ (by positivity); exact add_le_add (t _) ((div_le_self hv hk).trans (le_mul_of_one_le_right hv he))
        _ = _ :=by ring
 simpa using (B.const_mul (A+v)).mul_const (τ)
lemma goes_mesh:Tendsto (fun d=>SP (stackW d)) atTop (𝓝 0):= squeeze_zero (fun _=>(P.spotMesh_pos _).le) (f:=fun d=>SP (stackW d)) (fun d=>le_mul_of_one_le_left (spotMesh_pos ..).le (by exact_mod_cast measure_min P d)) (sizeJoint P)
-- advanced ruler multiply by S spurs
variable (n:ℕ)
def bootH(P:Spine)(m d:ℕ):Cover:=fun j=> if j=(3:Axis) then (m:ℤ)*spindle P d (stairW d) 3 else spindle P d (stairW d) j
lemma portal_small:
 Tendsto (fun d=> P.gridSpot (stackW d) (bootH P n d)-P.gridSpot (stackW d) 0) atTop (𝓝 0):=by
 rw [tendsto_pi_nhds]; intro i; simp_rw [Pi.sub_apply, P.gridSpot_mul, Pi.zero_apply,Int.cast_zero,zero_mul, sub_zero]
 by_cases u:i=(3:Axis)
 · subst i; let ν:ℝ:= (n:ℝ)*4
   have he:= (sizeJoint P).const_mul ν; rw [mul_zero] at he; refine he.congr ?_; intro d; unfold bootH spindle; rw [if_pos rfl,if_pos rfl]; push_cast; unfold ν; ring
 let ν:= 4*(idleCar P:ℝ)
 have he:= (goes_mesh P).const_mul ν; unfold ν at he; rw [mul_zero] at he; refine he.congr ?_; intro d; unfold bootH spindle; rw [if_neg u,if_neg u]; push_cast; rfl
#print axioms portal_small
end Aloft
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
