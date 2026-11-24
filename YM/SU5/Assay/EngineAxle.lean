import YM.SU5.Assay.Axle
import YM.SU5.Assay.RawLag
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set OS.Semigroup
variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "K"=> P.calibration
local notation "H"=> P.ColorHil j x
local notation "B"=> P.ManyF j x
local notation "X"=> (P.ColorHil j x).Op
local notation "Y"=> (P.ManyF j x).Op
local notation "Lag"=>ℝ→ℝ→(P.ManyF j x).Op
local notation "S"=> P.seasons j x
local notation "U"=> P.physicalEnergy j x
local notation "ω"=> (P.seasons j x).wax
local notation "W"=> P.cartage j x
local notation "θ"=> P.tableau j x
local notation "E"=> P.enter j x
local notation "R"=> P.wealth j x
local notation "Vac"=> P.colorZero j x
local notation "Ω"=> P.heaven j x
/-! Uncompressed counterpart of `Axle`. -/
local notation "ι"=>P.reprise j x
local notation "μ"=>P.seenBox j x
local notation "σ"=>P.shifts j
local notation "β"=>P.rawBase j x
variable (s w:ℕ)
noncomputable def engineAxle (f:P.Test):P.RawLag j x:=
 (U).hang (P.tock s w) (μ s (w+w) (σ w f))
lemma rawBase_engineAxle (D:P.Apron): β D=P.engineAxle j x D.s (D.u j) D.F:=by unfold rawBase engineAxle; rw [P.engine_seen];rfl

local notation "λ'"=>P.engineAxle j x s w
local notation "τ"=>P.tock s
variable {P j w}{a b:ℝ}{f g:P.Test}{D:P.Apron}{p:ℤ}
-- absolute cost
lemma engineAxle_pay (t:P.Focused j w f)(a b:ℝ): ‖λ' f a b‖≤ ‖P.meanBox j s (w+w) (σ w f)‖:=
 ((U).hang_pay ..).trans (seenBox_pay s x t.1 (P.shifts_keep j w t.2))

lemma engineAxle_shift (h:D.s=s)(v:Jaw (D.u j) (w+p) (w+w))(u:τ w≤a)(y:τ w≤b):
 λ' (σ p D.F) a b=β D (a+τ p) (b-τ p):=by
 -- parse β D (a+τ p) ok
 subst s
 have h := P.jaw_seen j x D v
 change _ = β D _ _ at h
 obtain ⟨e,t⟩:= (jaw_real P D.s).1 v
 rw [Nat.cast_add,P.tock_add,P.tock_add] at h t
 rw [P.tock_add] at e
 let c:= P.tock D.s; let q:=c (D.u j); let r:=c w; let z:=c p
 have e:q≤r+z:=e; have t:q≤r+r-(r+z):=t
 have v:r+z≤a+z:=add_le_add_left u _ -- add_le_add_left? direction tune
 have ha:r+r-(r+z)≤b-z:=by change r≤b at y; linarith only [y]
 unfold engineAxle hang
 rw [shifts_sum,h]
 refine Eq.trans ?_ (P.rawBase_step j x D e t v ha).symm
 exact congrArg₂ ((U).sand _) (show a-r=a+z-(r+z) by abel) (show b-r=b-z-(r+r-(r+z)) by abel)
lemma engineAxle_widen (h:D.s=s)(v:D.u j≤w)(u:τ w≤a)(y:τ w≤b):
 λ' D.F a b=β D a b:=by
 have e:Jaw (D.u j) (w+(0:ℤ)) (w+w):=Jaw.shifted (by omega) (by omega)
 have t:=engineAxle_shift x s h e u y
 rwa [P.shifts_zero,P.tock_zero,add_zero,sub_zero] at t
lemma engineAxle_smul (t:P.Focused j w f)(z:ℂ)(a b:ℝ):λ' (z•f) a b=z• λ' f a b:=by
 unfold engineAxle hang sand
 rw [map_smul,seenBox_smul s x t.1 (P.shifts_keep _ _ t.2),mul_smul_comm,smul_mul_assoc]
lemma engineAxle_sub (t:P.Focused j w f)(q:P.Focused j w g)(a b:ℝ):λ' (f-g) a b=λ' f a b-λ' g a b:=by
 unfold engineAxle hang sand
 rw [map_sub,seenBox_sub s x t.1 q.1 (P.shifts_keep _ _ t.2) (P.shifts_keep _ _ q.2),mul_sub,_root_.sub_mul]
lemma engineAxle_add (t:P.Focused j w f)(q:P.Focused j w g)(a b:ℝ):λ' (f+g) a b=λ' f a b+λ' g a b:=by
 unfold engineAxle hang sand
 rw [map_add,seenBox_add s x t.1 q.1 (P.shifts_keep _ _ t.2) (P.shifts_keep _ _ q.2),mul_add,add_mul]
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
