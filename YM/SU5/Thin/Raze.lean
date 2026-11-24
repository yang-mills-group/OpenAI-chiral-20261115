import SatinFixedContrastNovember4
import YM.SU5.Thin.Touch

set_option autoImplicit false
set_option maxHeartbeats 240000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Spine
open Aria Casting Six
open PadThin Sifter
namespace PadThin
/-- Compression & transport routine -- protected from rewrites with the large P fields. -/
def carries {X Y: Hilbert}(C:X→L[ℂ]Y)(D:Y→L[ℂ] X)(A:X.Op):Y.Op:= C.comp (A.comp D)
variable {X Y:Hilbert}(C:X→L[ℂ]Y)(D:Y→L[ℂ]X) (S:OS.Semigroup X (3:Axis))(T:OS.Semigroup Y (3:Axis)) (A:X.Op)
variable (u:∀ t x,C (S.E t x)=T.E t (C x))(p:∀ t x,D (T.E t x)=S.E t (D x))
include u p
lemma balance (a b:ℝ≥0) : sent Y T a b (carries C D A)= carries C D (sent X S a b A) := by
  ext1 x; simp only [carries,sent, ContinuousLinearMap.comp_apply,u,p]
omit u p
lemma scooped (X Y:Hilbert)(C:X→L[ℂ]Y)(D:Y→L[ℂ]X) (B:ℕ→X.Op) (v:Scoop) : carries C D (v.recipe B)=v.recipe (fun i=> carries C D (B i)) := by
  ext1 x; rw [v.evaluates Y]; change C (v.recipe B (D x))= _; rw [Scoop.evaluates X]; unfold Scoop.recipe; simp_rw [map_sum,map_smul]; rfl
lemma intoCarries {U:Type*}{l:Filter U} {B:U→X.Op} (b:∀ x,Tendsto (fun i=>B i x) l (𝓝 (A x))) (z:Y): Tendsto (fun i=> carries C D (B i) z) l (𝓝 (carries C D A z)):= C.continuous.continuousAt.tendsto.comp (b _)
end PadThin
section origin
variable (P:Spine)(x:P.Spectrum0 3)
local notation "ξ"=> P.otherSpectrum 3 3 x
local notation "H'"=> P.ColorHil 3 ξ
local notation "H"=> P.ManyF 3 ξ
local notation "ν"=> P.physicalEnergy 3 ξ
local notation "σ"=> P.seasons 3 ξ
local notation "ω"=> P.wealth 3 ξ
local notation "κ"=> P.enter 3 ξ
local notation "R"=> P.cartage 3 ξ
local notation "ψ"=> P.truck 3 ξ
variable (p:P.VMark)(v:Vantage)(lo hi:ℝ)
variable (G:P.Apron)
local notation "CW" => R v
local notation "PW" => R (-v)
local notation "V" => P.tableau 3 ξ v
local notation "S" => P.charter 3 ξ p
-- both loose and compressed: use `carries` for coherence
lemma plateauThermal (Z_:(P.ColorHil 3 ξ).Op) (a b:ℝ≥0): sent H σ a b (V Z_)=V (sent H' ν a b Z_):=
  let T:= (CW).comp (ω)
  let T':= (κ).toContinuousLinearMap.comp (PW)
  balance (X:=H') (Y:=H) T T' ν σ Z_
    (fun t x' => (congrArg (CW) (P.bankHeat 3 ξ t x')).trans (P.warm_drive 3 ξ v t (ω x')).symm)
    (fun t x' => (congrArg (fun y:H=>κ y) (P.warm_drive 3 ξ (-v) t x').symm).trans (P.soleHeat 3 ξ t (PW x'))) a b
lemma charterThermal (Z_:(P.ColorHil 3 ξ).Op) (a b:ℝ≥0): sent H' ν a b (S Z_)=S (sent H' ν a b Z_):=
  balance (X:=H') (Y:=H') (ψ p) (ψ (-p)) ν ν Z_ (P.sixWard_truck_heat 3 ξ p) (P.sixWard_truck_heat 3 ξ (-p)) a b

/-- real-units, including the warm times to complete this slab. Keep gap qualifications
on all physical purchases, even though operators can be priced without them. -/
def centralPage : (H').Op:= sent H' ν (v 3-G.realWidth P 3-lo).toNNReal (hi-(v 3+G.realWidth P 3)).toNNReal (G.engine P 3 ξ)
lemma native_eval : P.raze 3 ξ G lo hi p= S (P.centralPage x (P.laysM p) lo hi G):= P.charterThermal x p (G.engine P 3 ξ) _ _
lemma real_eval : P.pillar 3 ξ G lo hi v= V (P.centralPage x v lo hi G):= P.plateauThermal x v (G.engine P 3 ξ) _ _
lemma pivot_eval (f:(H').Op) : V f=carries (X:=H') (Y:=H) ((CW).comp ω) ((κ).toContinuousLinearMap.comp (PW)) f := rfl
variable {X:Type*}[TopologicalSpace X]
lemma central_contHeat (X':Hilbert)(a:X→ℝ)(b:X→X') (ν':OS.Semigroup X' (3:Axis))(u:Continuous a) (t:Continuous b): Continuous (fun i=>ν'.E (a i).toNNReal (b i)) :=
  continuous_iff_continuousAt.mpr fun x => firmly (fun i:X=>ν'.E (a i).toNNReal) zero_le_one (Eventually.of_forall fun i=> ν'.shrinks _) (show ContinuousAt (fun i : X=> ν'.E (a i).toNNReal (b x)) x from (((ν'.continuousE _).comp continuous_real_toNNReal).comp u).continuousAt) t.continuousAt
lemma central_cont (F:X→H') (q:X→Vantage) (u:Continuous q) (r:Continuous F) : Continuous (fun i=>P.centralPage x (q i) lo hi G (F i)) :=
  let w:= G.realWidth P 3
  let t(i:X):= q i 3
  have hu : Continuous t:= (continuous_apply (3:Axis)).comp u
  have ht: Continuous (fun i:X=> hi-(t i+w)):= continuous_const.sub (hu.add continuous_const)
  have h:Continuous (fun i:X=> (t i-w)-lo):= (hu.sub continuous_const).sub continuous_const
  central_contHeat H' _ _ ν h ((G.engine P 3 ξ).continuous.comp (central_contHeat H' _ F ν ht r))
lemma pillar_cont (F:X→H) (q:X→Vantage) (u:Continuous q) (r:Continuous F) : Continuous (fun i=>P.pillar 3 ξ G lo hi (q i) (F i)) :=
  let w:= G.realWidth P 3
  let t(i:X):= q i 3
  have hu : Continuous t:= (continuous_apply (3:Axis)).comp u
  have ht: Continuous (fun i:X=> hi-(t i+w)):= continuous_const.sub (hu.add continuous_const)
  have h:Continuous (fun i:X=> (t i-w)-lo):= (hu.sub continuous_const).sub continuous_const
  central_contHeat H _ _ σ h (P.tablets 3 ξ (G.engine P 3 ξ) _ _ u (central_contHeat H _ F σ ht r))
lemma pillarPay : ‖P.pillar 3 ξ G lo hi v‖≤‖G.engine P 3 ξ‖:=
  (halfNorm H σ _ _ (V (G.engine P 3 ξ))).trans (P.tableau_pay ..)
end origin
#print axioms native_eval
#print axioms real_eval
#print axioms pillar_cont
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
