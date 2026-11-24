import YM.SU5.SatinWard.Resolution.Polaris
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 700000
set_option maxRecDepth 8000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
open MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
open Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
open scoped ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
open Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus QuadClock Ione Vow Swell
open _root_.Zephyr.Chern
universe uΩ


open Papal CF.Papyrus.Franc.SatinForce CF.Pannier.Chancel Checkers

open CF.Papyrus.Franc.Loaves
-- CP3 package. PUBLIC, no topology/order changes
open Moon
open Horizons FoliageP BareProgram Moonlit Moonlit.SwitchC
open _root_.YM.Regis.Head.Brecht _root_.YM.Regis.Circuit _root_.YM.Regis.Circuit.SpringDay
open SlabMark VelourBoard Papal.SkyTax Cygnet VelourWiggle
open YM.Stationary (Gaia)
open SwitchC.Garland SwitchC.Garland.Terrace SwitchC.Garland.Terrace.Juniper
open Abacus CheckerFlag SlopeCharge Maxwell
open scoped RealInnerProductSpace ContDiff
namespace Fame
open BProof Pressure
namespace Regulator

open _root_.YM.Gleam.Luster.Almanac Grade
open Papal.SkyTax
open _root_.YM.Regis.Head
open _root_.YM.Gleam.Luster.Almanac Grade
open _root_.YM.CF.Py.Rate.LocalLimit.Preparation _root_.YM.CF.Py.Rate.LocalLimit.Preparation.Tabletop Shrine Ione.Clock Moto
variable (P:Spine)
local notation "W★"=>P.calibration
local notation "Ω★"=>P.run.meter
open Preparation.Yoke Spine.Gingham Spine.Gingham.Diary
open ShapeLab ResolutionFrame Shrine 
open SatinWard

open Worth Pays BProof Aria Casting MacroGrid Selected OS.Semigroup OS.Semigroup.Marble PSE MarbleFace
namespace Polaris
variable (pv:skit)(ℓ:ℝ)(i:Axis) (x:P.Spectrum0 i) (A B:P.LagOp i x)
local notation "Θ"=> P.seasons i x
local notation "Ω"=> P.heaven i x
local notation "HI"=> P.ManyF i x
local notation "OpW"=> (P.ManyF i x).Op
local notation "ℛ"=> P.locate i x
local notation "h♢" t:max => Harbor P i x A B pv t
local notation "c◇" t:max => Cruise P i x A B pv t
local notation "uQ" v:max=> P.locate i x v
local notation "GapX" p:max=> ((p:skit) true i-p false i-2*ℓ)
-- for notations.F.Valid. `Fierce_POS` x exclus.
local notation "P₀" p:max=> (p:skit) false
lemma unitH (b:ℂ)(c:ℂ): Cruise P i x (b• A) (c• B) pv ℓ= b*c*(c◇ ℓ):=by
 unfold Cruise scepter hotPair Marble.whisper; simp only [Pi.smul_apply,P.locate_smul,smul_mul_assoc,mul_smul_comm]; simp only [smul_apply,inner_smul_right]; ring
lemma unitS (b:ℂ)(c:ℂ): Harbor P i x (b • A) (c • B) pv ℓ= b*c*(h♢ ℓ):=by
 unfold Harbor scepter; simp only [Pi.smul_apply,P.locate_smul,seam_smul,seam_smul_right]; ring
lemma unitSolo (c:ℂ)(pv:Vantage): SingleF P i x (c • A) pv ℓ=c* SingleF P i x A pv ℓ:=by
 unfold SingleF scepter; simp only [Pi.smul_apply,P.locate_smul]; exact inner_smul_right ..
lemma shift_act (pv:Vantage) : SingleF P i x A pv ℓ=Marble.whisper Ω (A ℓ ℓ):=P.cart_wash ..
variable (q:(P.seasons i x).Credits 0 A)(d:(P.seasons i x).Credits 0 B)
local notation "Gx" a:max=> scepter P i x a ℓ ℓ
local notation "G"=> ((Θ).wax)
open ContinuousLinearMap
lemma single_pay (b:Vantage):‖SingleF P i x A b ℓ‖≤‖A ℓ ℓ‖:=by
 rw [shift_act]; change ‖inner ℂ Ω (A ℓ ℓ Ω)‖ ≤ _; refine (norm_inner_le_norm ..).trans ?_; rw [(imMemo P i x).unit,one_mul]; simpa only [(imMemo P i x).unit,mul_one] using (A ℓ ℓ).le_opNorm Ω
lemma v_norm : ‖Cruise P i x A B pv ℓ‖≤‖A ℓ ℓ‖ * ‖B ℓ ℓ‖:=by
 let u:=pv false; let v:=pv true; let g:= (GapX pv); let U:= ℛ u (A ℓ ℓ); let V':= ℛ v (B ℓ ℓ); let X:= U *(Θ).wax g* V'; change ‖inner ℂ Ω (X Ω)‖≤ _; refine (norm_inner_le_norm ..).trans ?_; rw [(imMemo P i x).unit, one_mul]; let p':= X.le_opNorm Ω; rw [(imMemo P i x).unit,mul_one] at p'; apply p'.trans; change ‖U *(Θ).wax g* V'‖≤ _; refine (norm_mul_le ..).trans (mul_le_mul_of_nonneg_right (?_:‖U*(Θ).wax g‖≤‖U‖) (norm_nonneg _)|>.trans_eq (?_)); exact (norm_mul_le ..).trans (mul_le_of_le_one_right (norm_nonneg _) ((Θ).wax_pay _)); unfold U V'; rw [P.locate_cost,P.locate_cost]
lemma cargo : Harbor P i x A B pv ℓ= Cruise P i x A B pv ℓ-SingleF P i x A (pv false) ℓ*SingleF P i x B (pv true) ℓ:=rfl
-- do not require continuity of actors in position at any fixed or limiting height: consume BSOT. enough for compact local positive at pc.Even Width=0? not for specs. Uses above.t lag.E not giro rotating. Need separate for analytic.D.Mark future.
variable {I:Type*}{L:Filter I}{g:I→ skit}
variable {F' T':I→ P.LagOp i x}
variable (pF:Tendsto (fun n=> F' n ℓ ℓ) L (𝓝 (A ℓ ℓ))) (tF:Tendsto (fun n=> T' n ℓ ℓ) L (𝓝 (B ℓ ℓ)))
include pF
lemma solo_w {p:Vantage}{f:I→Vantage}(h:Tendsto f L (𝓝 p)): Tendsto (fun n=>SingleF P i x (F' n) (f n) ℓ) L (𝓝 (SingleF P i x A p ℓ)):= tendsto_const_nhds (x:=Ω)|>.inner (𝕜:=ℂ) ((P.locate_limit i x h (BSOT.fromNorm pF)).showAt Ω)
variable (t:Tendsto g L (𝓝 pv))
include t tF
lemma cruise_w: Tendsto (fun i'=> Cruise P i x (F' i') (T' i') (g i') ℓ) L (𝓝 (c◇ ℓ)):=by
 let q(i:Bool):= tendsto_pi_nhds.mp t i; let v(b):= tendsto_pi_nhds.mp (q b) i; let Q:= P.locate_limit i x (q false) (BSOT.fromNorm pF); have t':= P.locate_limit i x (q true) (BSOT.fromNorm tF); let e:=(Θ).wax_limit (((v true).sub (v false)).sub_const (2*ℓ)); exact tendsto_const_nhds (x:=Ω)|>.inner (𝕜:=ℂ) (((Q.mul e).mul t').showAt Ω)
omit t pF tF
lemma cruise_cozy : Continuous (fun pv:skit=> Cruise P i x A B pv ℓ):= continuous_iff_continuousAt.mpr fun y=> cruise_w P y ℓ i x A B (F':=fun _=>A) (T':=fun _=>B) tendsto_const_nhds tendsto_const_nhds tendsto_id
lemma harbor_cozy : Continuous (fun pv:skit=> Harbor P i x A B pv ℓ):=by
 simp_rw [cargo,shift_act]; exact (cruise_cozy P ℓ i x A B).sub continuous_const
include q
lemma proud(l r:ℝ)(h:0<l)(p:0<r)(e:0<ℓ): Marble.whisper Ω (A l r)=Marble.whisper Ω (A ℓ ℓ):=by
 let K:=max l ℓ; let Q:=max r ℓ; have he(a b:ℝ)(u:0<a)(v:0<b)(p:a≤K)(t:b≤Q): Marble.whisper Ω (A a b)=Marble.whisper Ω (A K Q):=by rw [q u v p t, missed (Θ) Ω (imMemo ..)]
 exact (he l r h p (le_max_left ..) (le_max_left ..)).trans (he ℓ ℓ e e (le_max_right ..) (le_max_right ..)).symm
-- Interpolating h. use later equally pose operator estimation.
include d
lemma still_pair (u:0<ℓ)(ha:straight i ℓ pv)(b:ℝ) (k:0<b)(p:b≤ℓ): Cruise P i x A B pv b=c◇ ℓ:=by
 let X:=scepter P i x (pv false) b b A; let Y':=scepter P i x (pv true) b b B; let vx:=ℓ-b
 have h(A:P.LagOp i x)(v:Vantage)(u:(Θ).Credits 0 A): (Gx v) A= (Θ).sand (scepter P i x v b b A) vx vx:= by unfold scepter; rw [u k k p p, P.locate_sand]
 let u₀:= GapX pv; unfold Cruise; rw [h A _ q, h B _ d, outsidePair (Θ) Ω u₀ (imMemo ..) vx vx vx vx X Y' (sub_nonneg.mpr p) (sub_nonneg.mpr p) (sub_nonneg.mpr (show 2*ℓ ≤ pv true i-pv false i from ha.le))] -- Need fold scepter args first for rewrite X.App
 rw [show vx+u₀+vx= pv true i-pv false i-2*b from by unfold vx u₀; ring]
#print axioms cruise_w
end Polaris
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
