import MarchC.Jungle
import Crape.Creature
import Preen.Fitted
import SatinLocalChron
import Preen.Travel
import GlazeS.Incline
import GlazeS.Room
import SatinFacet
import Crape.Halo
import Crape.Adjust
import Crape.Supple
import Crape.TimeLine
import Nankin.Bern
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
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
set_option maxRecDepth 6000
set_option maxHeartbeats 700000
open Aria Casting Set
open scoped Pointwise
namespace MiterT
namespace Mido
open Calico
variable (P:Spine)(F:ℕ)
local notation "T"=>timeMesh P.par
local notation "σ"=>P.spotMesh
local notation "R"=>ruler P.par.block
local notation "Lx"=>P.par.R.L
lemma tin_joint :Tendsto (fun s:ℕ=> (reachQ P s:ℝ)*σ s) atTop (𝓝 0):=by
 let L:ℝ:=P.par.R.L.val; let τ:ℝ:=(T).base; let θ:=L⁻¹
 have hl:1 < L:=by unfold L; exact_mod_cast (show 1<P.par.R.L.val from P.par.R.coarse.trans_lt' (by norm_num))
 have he:‖θ‖<1:=lt_of_le_of_lt (le_of_eq (Real.norm_of_nonneg (inv_nonneg.mpr (zero_le_one.trans hl.le)))) ((inv_lt_one₀ (zero_lt_one.trans hl)).mpr hl)
 have ec: Tendsto (fun s:ℕ=> (1+(s:ℝ))^6*θ^s) atTop (𝓝 (0:ℝ)):=by
    let f(n:ℕ):= (n:ℝ)^6*θ^n
    have H0:Summable f:= summable_pow_mul_geometric_of_norm_lt_one _ he
    apply Summable.tendsto_atTop_zero
    apply Summable.congr ( ((summable_nat_add_iff 1).2 H0).mul_right θ⁻¹)
    intro n; unfold f; rw [Nat.cast_add,Nat.cast_one,pow_succ θ, mul_assoc _ _ θ⁻¹,mul_inv_cancel_right₀ (show θ ≠0 from (by unfold θ; linarith [inv_pos.mpr (zero_lt_one.trans hl)])),add_comm]
 obtain ⟨A,h,t⟩:=polyRise P
 have hT: Tendsto (fun s:ℕ=>A*((1+(s:ℝ))^6*θ^s)*τ) atTop (𝓝 0):=by simpa using (ec.const_mul A).mul_const τ
 refine squeeze_zero (fun s=> mul_nonneg (Nat.cast_nonneg _) (P.spotMesh_pos _).le) ?_ hT
 intro s
 have hr: σ s=τ/L^s:=by unfold spotMesh mill τ L; rw [NNReal.coe_div,NNReal.coe_pow,NNReal.coe_natCast]; rfl
 exact (mul_le_mul_of_nonneg_right (t s) (P.spotMesh_pos _).le).trans (le_of_eq (by rw [hr]; unfold θ; rw [inv_pow]; ring))
lemma tin_mesh:Tendsto (σ) atTop (𝓝 0):=by
 apply squeeze_zero (fun _=> spotMesh_pos ..|>.le) (f:=σ) _ (tin_joint P); intro s
 apply le_mul_of_one_le_left (P.spotMesh_pos _).le; exact_mod_cast (show 1 ≤ reachQ P s by unfold reachQ minB Calico.amount; omega)
lemma wharves(a:Axis)(b:Bool)(i:Axis): Tendsto (fun s:ℕ=> (fitting P s (tablet P F s a b)).realWidth P i) atTop (𝓝 0):=by
 let K:ℝ:=P.calibration.ℓ + (23:ℕ); have h:Tendsto (fun s:ℕ=>(reachQ P s:ℝ)*σ s+K*σ s) atTop (𝓝 0):=by simpa using (tin_joint P).add ((tin_mesh P).const_mul K)
 have e(s:ℕ)(o:Cover): (fitting P s o).realWidth P i = ((beamU P o i:ℤ):ℝ)*σ s:=rfl
 apply squeeze_zero _ _ h
 · intro s; rw [e]; exact mul_nonneg (by exact_mod_cast Nat.zero_le _) (P.spotMesh_pos _|>.le)
 intro s; rw [e,←add_mul]; apply mul_le_mul_of_nonneg_right _ (P.spotMesh_pos s|>.le)
 let o:=tablet P F s a b; have hx:=tablet_abs P F s a b i
 have hv:(beamU P o i:ℤ) ≤ (reachQ P s:ℤ)+(P.calibration.ℓ+23:ℕ):=by
    let x:= nodeC o i; obtain ⟨h1,h2⟩:= abs_le.mp hx; rcases Int.natAbs_eq x with h|h <;> unfold beamU <;> unfold x o at * <;> omega
 unfold K; exact_mod_cast hv
lemma tin_center(a:Axis)(b:Bool): Tendsto (fun s:ℕ=> optic P s (tablet P F s a b)) atTop (𝓝 0):=by
 rw [tendsto_pi_nhds]; intro i; apply tendsto_zero_iff_norm_tendsto_zero.mpr
 let R':ℝ:= (R:ℤ); have hp:0 < R':=by unfold R'; exact_mod_cast ruler_gene ..
 have he:Tendsto (fun s:ℕ=> (reachQ P s:ℝ)*σ s /R') atTop (𝓝 0):=by simpa using ((tin_joint P).div_const R')
 refine squeeze_zero (fun s=> norm_nonneg _) ?_ he
 intro s; let x:=nodeC (tablet P F s a b) i; have hv: |(x:ℝ)|≤reachQ P s:=by exact_mod_cast tablet_abs P F s a b i
 rw [Real.norm_eq_abs]; change |markZ P.par s x/2|≤_
 rw [←measureCatch]; change |(x:ℝ)/R'*σ s|≤_; rw [abs_mul,abs_div,abs_of_pos (P.spotMesh_pos _),abs_of_pos hp,mul_comm_div]
 rw [← mul_div_assoc]
 exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hv (P.spotMesh_pos _).le) hp.le
lemma leaseZ(s:ℕ)(y o:Cover): optic P s (metro P y o)-optic P s o=P.gridSpot s y:=by
 ext i; rw [Pi.sub_apply]; unfold optic; rw [metro_cal, ←measureCatch,←measureCatch,P.gridSpot_mul]
 have hp:(↑(R:ℤ):ℝ) ≠0:=Int.cast_ne_zero.mpr (ruler_gene _).ne'; unfold measured; rw [Int.cast_add,Int.cast_mul]; unfold spotMesh; field -- push_cast maybe ruler reduce. prefer field_simp
lemma leaseK(s j:ℕ)(h:j ≤ s)(o:Cover): optic P s (orbitB Lx o (s-j))= optic P j o:=by
 ext i; unfold optic; rw [dutyT _ _ P.par.R.odd_side]; simp only [Pi.smul_apply,nsmul_eq_mul]; rw [←measureCatch,←measureCatch]; push_cast; exact marks_rec P _ _ _ h
noncomputable abbrev centreA(s:ℕ)(a:Axis)(b:Bool):Vantage:= optic P s (tablet P F s a b)
noncomputable def indi(s j:ℕ)(a:Axis)(b:Bool):Cover:= ((fun i:Axis=>(P.par.R.L.val:ℤ)^(s-j)*sap P F j a b i:Cover)- sap P F s a b)
lemma leaseC(s j:ℕ)(h:F ≤ j)(u:j ≤ s)(a:Axis)(b:Bool): P.gridSpot s (indi P F s j a b)=centreA P F j a b - centreA P F s a b:=by
 unfold centreA; rw [←leaseZ P s (indi P F s j a b) (tablet P F s a b), ← show orbitB Lx (tablet P F j a b) (s-j)=metro P (indi P F s j a b) (tablet P F s a b) from stands P F s j h u b a, leaseK P s j u]
lemma lease_pos(s:ℕ)(a:Axis)(b:Bool):0 < centreA P F s a b a:=by
 have hp:= tablet_born P F s a b
 let x:= nodeC (tablet P F s a b) a; have hr:0<(x:ℝ):=by exact_mod_cast (show 0 < x by unfold x; omega)
 have he:0 < precisionAt P.par s:= Tapestry.positiveScale ..
 change 0< (x:ℝ)/_/_; positivity
#check mul_comm_div
#print axioms leaseC
#print axioms tin_mesh
end Mido
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
