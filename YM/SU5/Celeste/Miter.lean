import YM.SU5.Celeste.Custodian
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition
variable (P:Spine)(R : P.Register)(j:Axis)
local notation "Ω"=>P.Hil j
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "W"=> P.calibration
local notation "ℓ"=> P.calibration.ℓ
local notation "Z"=> P.par
local notation "Q"=> P.par.block
local notation "Ticket"=> Lamour.Bridge.Celeste.Voice
local notation "oneT"=> Lamour.Bridge.Celeste.Voice.one
open Buffered Ballad
variable {F G:Weaver}{U T:Finset Cover}(p:Lamour.Bridge.Celeste.Voice F U)(q:Lamour.Bridge.Celeste.Voice G T)
lemma songsAg {S V:Finset Cover} {F H:Weaver} (h:Lamour.Bridge.Celeste.Voice F S)(v:Ticket H V)(e:F=H): P.tuneK h=P.tuneK v:=by subst H; rfl
lemma celebrity : P.tuneK p∈ Tapestry.enclave W := (enclave_spec W).mpr fun n=> p.2 _ -- tune
variable (w:P.Spectrum0 j)(a:Tower.region j 0 P.calibration.ℓ U)(e:Tower.region j 0 P.calibration.ℓ T)(s:ℕ)
local notation "V"=> P.ColorHil j w
local notation "ψ"=> P.province j w
local notation "κ" => P.warming j w
local notation "X" => P.gnsIn j w
local notation "Σ" => P.singleState j s w
local notation "A₀"=> P.voxTest j s
local notation "ω" => P.colorZero j w
def mantra (p:Lamour.Bridge.Celeste.Voice F U)(a:Tower.region j 0 P.calibration.ℓ U)(s:ℕ): P.naturalVox j s:=⟨P.songK j p a s,P.celebrity p⟩
noncomputable def coinK (t:Lamour.Bridge.Celeste.Voice F U)(w:P.Spectrum0 j)(a: Tower.region j 0 P.calibration.ℓ U)(s:ℕ) : P.ColorHil j w:= P.province j w s (P.mantra j t a s)
lemma refrain : inner ℂ (P.coinK j p w a s) (P.coinK j q w e s)=(Σ) (P.reflectTest j (P.tuneK p)*P.tuneK q):=by rw [← LinearIsometry.inner_map_map (X),coinK,coinK,P.coincides,P.coincides,P.gram_at]; rfl
lemma themeVox (t:P.Vox j s): inner ℂ (P.emptyV j w) (P.stateVox j w s t)=P.singleState j s w (P.voxTest j s t):=by
 obtain ⟨l,h,v,rfl⟩:= P.fits j s t; rw [P.from_entry j w s l h v]; exact (gns_state (P.portion j w) (P.atSide j s l h v)).trans (P.room_single ..)
lemma anthem : inner ℂ (P.colorZero j w) (P.coinK j p w a s)= (Σ) (P.tuneK p):=by rw [← LinearIsometry.inner_map_map (X),coinK,P.coincides,P.present0]; apply P.themeVox j w s (P.songK j p a s) -- tune definitional
lemma norms_color : ‖P.colorZero j w‖=1:=origin_norm _ (P.unit_too j w)
lemma colorVacuum (t:ℝ≥0):P.warming j w t ω=ω:= (X).injective (by rw [P.warmTransit,P.present0,P.at_full])
lemma songUnity {S:Finset Cover}(h:Tower.region j 0 P.calibration.ℓ S) : P.coinK j (oneT S) w h s= P.colorZero j w:= by
 let T:= P.PortionHil j w; let F:=unity P.run P.large j 0 false s; let P':= SlabMark.identity P.run P.large s j false 1; have ht:P.atSide j s 1 zero_lt_one P'= P.Eucl j (whenly (timeMesh P.par) s 1):=Subtype.ext (SlabMark.ticket_birth P.run P.large P.law s P.history P.projection.clipped j false (P.room j) 1 zero_lt_one)
 apply (X).injective; rw [coinK,P.coincides,P.present0]; change P.stateVox j w s P'.val= _; rw [P.from_entry j w s 1 zero_lt_one,fromPlane,ht]; exact P.at_full j w _
noncomputable def shaded (x:ℂ):Ticket (F-x • 1) U:=p.sub ((oneT U).hushed x) -- proof? def Prop.noncomp
lemma songShade (c:ℂ): P.coinK j (shaded p c) w a s=P.coinK j p w a s-c • P.colorZero j w:=by
 apply (X).injective; rw [map_sub,map_smul,← P.songUnity j w s a]; simp_rw [coinK,P.coincides];
 let K:= P.stateVoxLinear j w s; let u:= P.songK j p a s; let t:= P.songK j (oneT U) a s;
 change K (u - c • t)= K u-c • K t; rw [map_sub,map_smul] -- not defeq using u - c smul t? sub may defeq
lemma reordered (u t:P.Test): u*t=t*u:=by exact mul_comm u t -- ring comm even
lemma cadet (k:ℕ): inner ℂ (P.coinK j p w a s) (P.warming j w (P.halfTime s k) (P.coinK j q w e s))= (Σ) (P.reflectTest j (P.tuneK p)*P.halfShift j k (P.tuneK q)) := by rw [← LinearIsometry.inner_map_map (X),P.warmTransit,coinK,coinK,P.coincides,P.coincides,← P.every_tick,P.gram_at]; rfl
lemma colorAdj (t:ℝ≥0): ContinuousLinearMap.adjoint (P.warming j w t)=P.warming j w t:= by
 have h:= P.physicalEnergy j w |>.sym t; exact h -- eq or form
-- general projection billing
section Billing
variable {G₀:Hilbert}
lemma hue(x y:G₀)(c:ℂ)(p:inner ℂ x y=0)(t:‖x‖=1): ‖y+c•x‖^2=‖y‖^2+‖c‖^2:=by
 have h:inner ℂ y (c• x)=0:= by rw [inner_smul_right,←inner_conj_symm (𝕜:=ℂ),p,map_zero,mul_zero]
 rw [sq,sq ‖y‖,sq ‖c‖,norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h,norm_smul,t,mul_one] -- name
end Billing
noncomputable def centered (p:Lamour.Bridge.Celeste.Voice F U)(a:Tower.region j 0 P.calibration.ℓ U)(s:ℕ): V := P.coinK j p w a s- ((P.singleState j s w) (P.tuneK p)) • (P.colorZero j w)
-- params order w p after def given
lemma center_value(p:Lamour.Bridge.Celeste.Voice F U)(a:Tower.region j 0 P.calibration.ℓ U)(s:ℕ): inner ℂ ω (P.centered j w p a s)=0:=by rw [centered, inner_sub_right,inner_smul_right, P.anthem,inner_self_eq_norm_sq_to_K,P.norms_color]; simp
lemma coined (p:Lamour.Bridge.Celeste.Voice F U)(a:Tower.region j 0 P.calibration.ℓ U)(s:ℕ): P.coinK j p w a s=P.centered j w p a s+(P.singleState j s w (P.tuneK p)) • ω:= (sub_add_cancel ..).symm -- sigma notation shadow
lemma center_norm(p:Lamour.Bridge.Celeste.Voice F U)(a:Tower.region j 0 P.calibration.ℓ U)(s:ℕ): ‖P.coinK j p w a s‖^2=‖P.centered j w p a s‖^2+‖P.singleState j s w (P.tuneK p)‖^2:=by rw [P.coined]; exact hue (G₀:=V) _ _ _ (P.center_value ..) (P.norms_color ..)
lemma center_bill(p:Lamour.Bridge.Celeste.Voice F U)(a:Tower.region j 0 P.calibration.ℓ U)(t:ℝ≥0)(z:ℂ)(s:ℕ): Complex.re (inner ℂ (P.centered j w p a s) ((κ) t (P.centered j w p a s)))≤ Complex.re (inner ℂ (P.coinK j (shaded p z) w a s) ((κ) t (P.coinK j (shaded p z) w a s))):= by
 let f:=P.centered j w p a s; let Z₁:=P.singleState j s w (P.tuneK p)-z; let x:= (Z₁) • ω
 rw [P.songShade (p:=p), (P.coined j w p a s)]; rw [show f + P.singleState j s w (P.tuneK p) • P.colorZero j w-z • ω=f+x from (by unfold x Z₁; simp only [sub_smul]; abel)]
 let K:=(κ) t; have ht:K x=x:= by unfold x; rw [map_smul]; exact congrArg (Z₁ • ·) (P.colorVacuum j w t);
 have h:inner ℂ x f=0:=by unfold x; rw [inner_smul_left]; exact (by rw [show inner ℂ (P.colorZero j w) f=0 from P.center_value ..,mul_zero]);
 have he:inner ℂ x (K f)=0:=by unfold K; nth_rw 1 [←P.colorAdj j w t]; rw [ContinuousLinearMap.adjoint_inner_right,ht,h]
 change _ ≤ (inner ℂ (f+x) (K (f+x))).re; rw [map_add,ht,inner_add_right,inner_add_left,inner_add_left,he, show inner ℂ f x=0 from (by rw [←inner_conj_symm (𝕜:=ℂ),h,map_zero]),zero_add,add_zero, Complex.add_re]; exact le_add_of_nonneg_right ((_root_.inner_self_nonneg (𝕜:=ℂ) (x:=x)))
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.center_bill
