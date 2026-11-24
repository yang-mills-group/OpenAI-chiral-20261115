import YM.SU5.Assay.Jaw
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
/-! Centered scoring device, tested with uniform *time* caliper w ticks in
 each direction (no assumed support across other axes). Use with the time lags
 paying at that width. Equality from the whole mark works for ***all*** lags
 with clip if widths equal; and for genuine lags with padding whenever
 w covers the stencil been charged. -/
local notation "ι"=>P.reprise j x
local notation "μ"=>P.seenBox j x
local notation "σ"=>P.shifts j
local notation "β"=>P.base j x
variable (s w:ℕ)
noncomputable def axle (f:P.Test):Lag:=
 (S).hang (P.tock s w) (ι (μ s (w+w) (σ w f)))
lemma base_axle (D:P.Apron): β D=P.axle j x D.s (D.u j) D.F:=by unfold base axle; rw [P.engine_seen];rfl

local notation "λ'"=>P.axle j x s w
local notation "τ"=>P.tock s
variable {P j w}{a b:ℝ}{f g:P.Test}{D:P.Apron}{p:ℤ}
abbrev Focused (P:Spine)(j:Axis)(w:ℕ)(f:P.Test):Prop:=
  P.BEntry j (w+w) (P.shifts j w f) ∧ f ∈ enclave P.calibration
-- absolute cost
lemma axle_pay (t:P.Focused j w f)(a b:ℝ): ‖λ' f a b‖≤ ‖P.meanBox j s (w+w) (σ w f)‖:=
 ((S).hang_pay ..).trans ((P.reprise_pay ..).trans (seenBox_pay s x t.1 (P.shifts_keep j w t.2))) -- placeholder

lemma axle_shift (h:D.s=s)(v:Jaw (D.u j) (w+p) (w+w))(u:τ w≤a)(y:τ w≤b):
 λ' (σ p D.F) a b=β D (a+τ p) (b-τ p):=by
 -- parse β D (a+τ p) ok
 subst s
 obtain ⟨_,h⟩:=P.jaw_base j x D v
 obtain ⟨e,t⟩:= (jaw_real P D.s).1 v
 rw [Nat.cast_add,P.tock_add,P.tock_add] at h t
 rw [P.tock_add] at e
 let c:= P.tock D.s; let q:=c (D.u j); let r:=c w; let z:=c p
 have e:q≤r+z:=e; have t:q≤r+r-(r+z):=t
 have v:r+z≤a+z:=add_le_add_left u _ -- add_le_add_left? direction tune
 have ha:r+r-(r+z)≤b-z:=by change r≤b at y; linarith only [y]
 unfold axle hang
 rw [shifts_sum,h]
 refine Eq.trans ?_ (P.base_step j x D e t v ha).symm
 exact congrArg₂ ((S).sand _) (show a-r=a+z-(r+z) by abel) (show b-r=b-z-(r+r-(r+z)) by abel)
lemma axle_widen (h:D.s=s)(v:D.u j≤w)(u:τ w≤a)(y:τ w≤b):
 λ' D.F a b=β D a b:=by
 have e:Jaw (D.u j) (w+(0:ℤ)) (w+w):=Jaw.shifted (by omega) (by omega)
 have t:=axle_shift x s h e u y
 rwa [P.shifts_zero,P.tock_zero,add_zero,sub_zero] at t
include x in
lemma Focused.shift (h:Jaw (D.u j) (w+p) (w+w)):P.Focused j w (σ p D.F):= by
 rw [Focused,P.shifts_sum]
 -- x may not exist? jaw_base needs Spectrum0. instead BEntry.pad via helper separate widen? use Apron BFits of u j all axes? d0 not. x explicit include
 exact ⟨(P.jaw_base j x D h).1,P.shifts_keep j p D.realM⟩
include x in
lemma Focused.widen (h:D.u j≤w):P.Focused j w D.F:=by
 have e:Jaw (D.u j) (w+(0:ℤ)) (w+w):=Jaw.shifted (by omega) (by omega)
 have t:=Focused.shift x e; rwa [P.shifts_zero] at t

lemma axle_smul (t:P.Focused j w f)(z:ℂ)(a b:ℝ):λ' (z•f) a b=z• λ' f a b:=by
 unfold axle hang sand
 rw [map_smul,seenBox_smul s x t.1 (P.shifts_keep _ _ t.2),P.reprise_smul,mul_smul_comm,smul_mul_assoc]
lemma axle_sub (t:P.Focused j w f)(q:P.Focused j w g)(a b:ℝ):λ' (f-g) a b=λ' f a b-λ' g a b:=by
 unfold axle hang sand
 rw [map_sub,seenBox_sub s x t.1 q.1 (P.shifts_keep _ _ t.2) (P.shifts_keep _ _ q.2),P.reprise_sub,mul_sub,_root_.sub_mul]
lemma axle_add (t:P.Focused j w f)(q:P.Focused j w g)(a b:ℝ):λ' (f+g) a b=λ' f a b+λ' g a b:=by
 unfold axle hang sand
 rw [map_add,seenBox_add s x t.1 q.1 (P.shifts_keep _ _ t.2) (P.shifts_keep _ _ q.2),P.reprise_add,mul_add,add_mul]
lemma Focused.smul (t:P.Focused j w f)(z:ℂ):P.Focused j w (z•f):=by
 rw [Focused,map_smul];exact ⟨t.1.smul z,(enclave ..).smul_mem t.2 z⟩
lemma Focused.sub (t:P.Focused j w f)(q:P.Focused j w g):P.Focused j w (f-g):=by
 rw [Focused,map_sub]; exact ⟨t.1.sub q.1,(enclave K).sub_mem t.2 q.2⟩
lemma Focused.add (t:P.Focused j w f)(q:P.Focused j w g):P.Focused j w (f+g):=by
 rw [Focused,map_add]; exact ⟨t.1.add q.1,(enclave K).add_mem t.2 q.2⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
