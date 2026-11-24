import Gingham.Banding
import WakeRoad.PinArc
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 200000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical ContDiff
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set
open OS.Semigroup YM.OS.Semigroup.Gingham
open Boundary Probe
namespace Spine.NativeSeam
open YM.OS YM.OS.Semigroup SatinRegistration YM.Velour YM.SatinMacro
variable (P:Spine)(x:P.Spectrum0 3)
local notation "jₓ"=> (3:Axis)
local notation "ξ"=> P.advocate 3 x jₓ
local notation "G"=> P.ManyF jₓ ξ
variable (B D:P.Apron) (F U:SampleDose)(δ M:ℝ)
local notation "lₙ" n:max=>P.prepared n B F
local notation "rₙ" n:max=>P.prepared n D U
open _root_.YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.Gingham
abbrev island(i n j:ℕ)(W:P.Test): Parts:= let e:= Gingham.tariff P n W j; let T:= CarrierB P i n; let L:= T (lₙ i); let R:= T (rₙ i); (e (L*R),e L,e R)
section regulator
open Diary
structure MirrorCase(i n:ℕ)(W:P.Test):Prop where
    sealL:P.asked_at n (CarrierB P i n (lₙ i)) (P.spacePrice B F)
    sealR:P.asked_at n (CarrierB P i n (rₙ i)) (P.spacePrice D U)
    safeL:CarrierB P i n (lₙ i)∈enclave P.calibration
    safeR:CarrierB P i n (rₙ i)∈enclave P.calibration
    separate: CarrierB P i n (lₙ i*rₙ i)=CarrierB P i n (lₙ i)*CarrierB P i n (rₙ i)
    brief: Lodgment P n (M+1) W
    scanR : ∀ᶠ j in atTop, Ferry P.run n (irr P j) (uvv P j) ∧ rawE P n j (magnet P W 1)≠0 ∧ Topaz (island P B D F U i n j W) (EuCosts P x B D F U) δ
-- choose real M enclosing all placements including apertures. additional phases x-dependent screens.
lemma ballast_disjoint (h:Ballast P x D B F U δ): Disjoint (P.spacePrice B F) (P.spacePrice D U):=
    Set.disjoint_left.mpr (fun _ g u=> lt_irrefl _ ((h.toHallmark.spacing P x D g u).1 jₓ))
theorem journal_cleared (h:Ballast P x D B F U δ) :
    ∀ᶠ i:ℕ in atTop,∃ n W,i≤n ∧ MirrorCase P x B D F U δ M i n W:=by
    let E:= EuCosts P x B D F U
    filter_upwards [h.gridJ,eventually_ge_atTop (B.s+D.s)] with i p c
    let f:Option Bool→P.Test:=fun e=>match e with
     | none=>lₙ i * rₙ i
     | some true=>lₙ i
     | some false=>rₙ i
    let V:Set (Option Bool→ℂ):= {z| Topaz (lever z) E δ}
    have o:IsOpen V:=isOpen_iff_mem_nhds.mpr fun z y=>
     (show Continuous lever from (continuous_apply _).prodMk
       ((continuous_apply _).prodMk (continuous_apply _))).continuousAt.preimage_mem_nhds (likelier _ (lever z) y)
    obtain ⟨t,v,u,A,H⟩:= after_knives P x i f o p (M+1)
    let T:= CarrierB P i t; have l: P.asked_at i (lₙ i) (P.spacePrice B F):= P.prepared_at _ _ _ (by omega)
    have r:P.asked_at i (rₙ i) (P.spacePrice D U):= P.prepared_at _ _ _ (by omega)
    have ht:T (lₙ i * rₙ i)=T (lₙ i)*T (rₙ i):=held_apart P _ _ _ _ _ _ l r (ballast_disjoint P x B D F U δ h)
    refine ⟨t,u,v,hold_asked P _ _ _ _ l v,hold_asked P _ _ _ _ r v,P.refine_keeps _ _ (P.prepared_color _ _ _) _, P.refine_keeps _ _ (P.prepared_color _ _ _) _,ht,A,H.mono fun j x=>⟨x.1,x.2.1,?_⟩⟩
    unfold island; change Topaz (Gingham.tariff P _ u j (T (lₙ i)*T (rₙ i)),_,_) _ _
    rw [←ht];exact x.2.2
#print axioms journal_cleared
lemma cellar (A:P.Apron)(F:SampleDose): ∃ M:ℝ, ∀ u∈ P.spacePrice A F,u (3:Axis)≤M ∧ -M≤u (3:Axis):=by
    obtain ⟨N,t⟩:= (F.budget.image (continuous_apply (3:Axis)|>.abs)).bddAbove
    refine ⟨N+A.realWidth P 3,?_⟩; intro u v; obtain ⟨p,g,e⟩:= Set.mem_iUnion₂.mp v
    have hx:=abs_le.mp (e (3:Axis)); have h:=abs_le.mp (t (Set.mem_image_of_mem _ g)); constructor <;> linarith only [hx.1,hx.2,h.1,h.2]
def Luminous (M:ℝ):Prop:= ∀ p∈P.spacePrice B F∪P.spacePrice D U, |p (3:Axis)|≤M
lemma cellars : ∃ M:ℝ, Luminous P B D F U M:=by
    obtain ⟨l,p⟩:=cellar P B F; obtain ⟨v,q⟩:=cellar P D U
    exact ⟨max l v,fun a t=> t.elim (fun h=>(abs_le.mpr (p _ h).symm).trans (le_max_left ..)) (fun h=>(abs_le.mpr (q _ h).symm).trans (le_max_right ..))⟩
structure LinkedSpectrum : Prop extends Ballast P x D B F U δ where
    attendance : ∃ (M:ℝ), Luminous P B D F U M ∧ ∀ᶠ i:ℕ in atTop,∃ n W,i≤n ∧ MirrorCase P x B D F U δ M i n W
theorem LinkedSpectrum.of_ballast (h:Ballast P x D B F U δ) : LinkedSpectrum P x B D F U δ:=by
    obtain ⟨m,p⟩:= cellars P B D F U; exact ⟨h,m,p,journal_cleared P x _ _ _ _ δ _ h⟩
end regulator
end Spine.NativeSeam
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
