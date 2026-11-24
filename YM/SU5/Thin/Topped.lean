import SatinFixedContrastNovember4
import YM.SU5.Thin.DoseOp

set_option autoImplicit false
set_option maxHeartbeats 180000
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
/-!
# Operator smearing directly on the physical formula

Input vector for this limit is in ManyF; conclude in FULL X. Don't replace
the grid sampler by averaging the readings in each aperture with a t-dependent
choice of another smearing. Uses its actual cost order.
-/
open Sifter PadThin MacroGrid
variable (P:Spine)(x:P.Spectrum0 3)(J:P.Ellis 3 x)(t:ℕ) (F:SampleDose)(A:P.Apron)(lo hi:ℝ)
local notation "ξ"=> P.advocate 3 x 3
local notation "H'"=> P.ColorHil 3 ξ
local notation "H"=> P.ManyF 3 ξ
local notation "ω"=> P.wealth 3 ξ
local notation "κ"=> P.enter 3 ξ
local notation "ν"=> P.physicalEnergy 3 ξ
local notation "σ"=> P.seasons 3 ξ
local notation "Ψ"=> P.cartage 3 ξ
local notation "Γ"=> P.truck 3 ξ
local notation "u"=> P.meshPose t
-- as private pose_grid lemma in Seam.lean
private lemma one_grid (X:Hilbert)(f:Vantage→X)(T:Cover → X.Op):
 MacroGrid.poseApprox X (fun z:Vantage=>(F.val z:ℂ) • f z) T (P.macroStep t) =
   ∑ i∈ P.usedGrid t F, P.activation t F i • T i (f (u i)) := by
 let g:=fun i:Cover=> T i ((F.val (u i):ℂ) • f (u i))
 have he(i:Cover)(x:i∉P.usedGrid t F): g i=0:= by
    have hu : F.val (u i)=0:=by by_contra p; exact x ((P.usedPose t F i).2 (subset_closure p))
    unfold g; rw [hu,Complex.ofReal_zero,zero_smul,map_zero]
 refine (room_price _ (P.macroStep_pos t) g (P.usedGrid t F) he).2.trans ?_
 rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro i h
 unfold g
 rw [map_smul,show Fintype.card Axis=4 by rfl, ← Complex.coe_smul ((P.macroStep t)^4), smul_smul]
 push_cast [activation]; rfl

namespace CashSum
variable (X:Hilbert)(I:Type*)
lemma payout (s:Finset I)(v:I→ℂ)(F:I→ X.Op)(x:X)(A:I→ X)(h:∀ i∈s,F i x=A i) :
    (∑ i∈s,v i • F i) x=∑ i∈s,v i • A i:= by simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply]; exact Finset.sum_congr rfl fun i e=> by rw [h i e]
lemma bound (s:Finset I)(v:I→ℂ)(F:I→ X.Op)(M:ℝ)(e:∀ i∈s,‖F i‖≤ M) : ‖(∑ i∈s,v i • F i)‖≤ (∑ i∈s,‖v i‖)*M:=by
  rw [Finset.sum_mul]; exact (norm_sum_le ..).trans (Finset.sum_le_sum fun i h=> by rw [norm_smul]; exact mul_le_mul_of_nonneg_left (e i h) (norm_nonneg _))
end CashSum

-- one position, stem recipe before summing over different widths.
def gridPage : (H').Op := ∑ i∈P.usedGrid t F,P.activation t F i • P.raze 3 ξ A lo hi (P.vtile t i)
lemma rawPageBill : ‖P.gridPage x t F A lo hi‖≤ P.doseTotal F t * ‖A.engine P 3 ξ‖ :=
  CashSum.bound H' _ _ _ _ _ (fun i _=> P.raze_pay 3 ξ A lo hi (P.vtile t i))

def fullPage : (H).Op := DoseBill.issue H F ‖A.engine P 3 ξ‖ (P.pillar 3 ξ A lo hi)
      (fun x' => P.pillar_cont x lo hi A _ _ continuous_id continuous_const) (fun i=> P.pillarPay x i lo hi A)
local notation "Z" i:max=> P.centralPage x i lo hi A
include J
lemma page_grid (y:H) : Tendsto (fun t=> P.gridPage x t F A lo hi (κ y)) atTop (𝓝 (κ (P.fullPage x F A lo hi y))) := by
  let f(i:Vantage):= (Z i) (κ (Ψ (-i) y)) -- parse
  let g(i:Vantage): H' := (↑(F.val i):ℂ) • f i
  have h: HasCompactSupport g:= F.budget.mono fun i w p=> w ((congrArg (fun x:ℝ=>(x:ℂ) • f i) (show F.val i=0 from p)).trans (zero_smul ℂ _))
  have e: Continuous f:= P.central_cont x lo hi A _ _ continuous_id ((κ).continuous.comp ((P.cart_cont ..).comp continuous_neg))
  have he: Continuous g:= (Complex.continuous_ofReal.comp F.smooth.continuous).smul e
  have hp(i): Ψ i (ω (g i))=(↑(F.val i):ℂ) • P.pillar 3 ξ A lo hi i y := by
    let W:= (Ψ i).comp ω; let c:ℂ:= (F.val i:ℂ)
    refine (map_smul W _ (f i)).trans (congrArg (fun z:(H).Op=> c • z y) (P.real_eval x i lo hi A).symm)
  have hw: (∫ i:Vantage, Ψ i (ω (g i)))= P.fullPage x F A lo hi y:= integral_congr_ae (Eventually.of_forall hp)
  let L:= P.fullPage x F A lo hi y
  refine Eq.mp (congrArg (fun x':H=> Tendsto _ _ (𝓝 (κ x'))) hw) ((P.macroRiemann x 3 J g h he).congr fun t=> ?_)
  -- tune metas
  refine (one_grid P t F H' f (Γ ∘ P.vtile t)).trans (CashSum.payout H' _ _ _ _ _ _ (fun i _=>?_)).symm
  let p:= P.vtile t i
  let X:= P.meshPose t i
  let D:= Z X
  refine (congrArg (fun z:(H').Op=> z (κ y)) (P.native_eval x p lo hi A)).trans (congrArg (fun z:H'=> Γ p (D z)) ?_)
  exact (P.cart_and 3 ξ (-p) y).trans (congrArg (fun z:Vantage=> κ (Ψ z y)) (P.lays_neg p))
omit J
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.page_grid
