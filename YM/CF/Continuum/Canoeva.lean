import YM.CF.Continuum.Caravan
import YM.CF.Continuum.CanYo
import YM.CF.Continuum.CarnI
import YM.CF.Continuum.Ramp
import YM.CF.Continuum.Scope
import YM.CF.Continuum.Episode
import YM.CF.Continuum.Symmetric
import YM.CF.Continuum.Allowed
/-!
# Which expanding periods? Retain astronaut and grants

Details: use the SAME reconstruction apparatus on the old UV-limit witness and
on new periods. No separate positive measures. We express the non-anchored
inhabitance range and produce history witnesses `Session`s and normalized limit
on this permit. At anchor mark-specialized; may choose same f. This is phase I,
period extension NOT common-limit yet. Stamp requirements don't connect bare-data
values across those periods (including β_l). Need cross-period bounds.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Period
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Ione Nor Haro Beau Salt Vow
set_option maxHeartbeats 800000
variable {U:Grasp V.U B d}{W:GivenX V U}
variable (a:ℝ)(p i N0 k₀:ℕ)
variable {N':Side}(J:Robes N' V W)(q:Chi)(h:ℝ)(R0 δ:ℝ→ℝ)
local notation "Lr"=>dleaf R.L
open CF.Mint MeasureTheory
open CF.Window
open Graph Girt
variable {M M0 : Side}
local notation "hatQ" => hat R.L x
open Push.GridApprox
variable (PX: Carousel V a p i N0 J q h R0 δ x M l)
namespace Carousel
local notation "PS" j => Vale.mesh M R.L j
local notation "KT" j=> cell M B R.L j
abbrev buoyG (j:ℕ):= V.L.op (PX.top-1-j) (kint M B R.L j)
local notation "Wl" j=> buoyG V a p i N0 J q h R0 δ PX j
-- Deliberately pull gauge probes whose final support after all dilations
-- has room on its designated side.
include PX
lemma actualG (j:ℕ) : (buoyG V a p i N0 J q h R0 δ PX j).patch=R ∧ (Wl j).ratio= ratio (apt M B R.L j) ∧ (Wl j).patch.Branches (Wl j).kernel SU.group:=by
 refine ⟨V.L.lent _, Hom.rat_eq (show (apt M B R.L j).count= _ from (V.L.lent_L ..).symm),?_⟩; unfold buoyG; rw [V.L.patch_x]; exact V.L.cloth
lemma rise_tilt (j:ℕ)(v:j<PX.top):Nonempty (Girt.BaseL U (apt M B R.L j) (PX.E (j+1)) (PX.Y j) (PX.Y (j+1)) q J.d):=by
 let g:=apt M B R.L j; let T':=(V.L.mint (PX.top-1-j) (kint M B R.L j)); let S:= (Wl j)
 have he:= sized_F (N:=mesh M R.L j) (P:=mesh M R.L (j+1)) (B:=B) (S:=S) (T:=T') V a p i N0 PX.val M PX.tip PX.top PX.main PX.day j _ (PX.owns _ v) v (PX.sift _ v)
 exact rig V U W J q (PX.roof j) (PX.Y _) (PX.roof _).paid _ he.sound rfl (PX.legal (j+1) v)
abbrev garner (j:ℕ)(T:Pane (cell M B R.L j)→ℂ):= back (buoyG V a p i N0 J q h R0 δ PX j) (PX.E (j+1)).beta T
abbrev θValue(j:ℕ)(F:Evaluation (cell M B R.L j)):= finiteForm V.U U (PX.E j) (PX.Y j) F
local notation "Z_V" j => θValue V a p i N0 J q h R0 δ PX j
local notation "Z_G" j => garner V a p i N0 J q h R0 δ PX j
lemma hhgo (j:ℕ)(v:j<PX.top)(F:Pane (cell M B R.L j)→ℂ)(e: Envelope F): (Z_V j) (bosonic _ F) = (Z_V (j+1)) (bosonic _ ((Z_G j) F)) := by
 obtain ⟨d⟩:= rise_tilt V a p i N0 J q h R0 δ PX j v
 have he:=actualG V a p i N0 J q h R0 δ PX j
 have hZ:=PX.owns j v.le
 have hp:Rue.IsleB SU.group (PX.E j).p.threshold:= hZ.width ▸ PX.mark j
 unfold θValue; rw [Window.by_denominator,Window.by_denominator]; exact congrArg₂ (·/·) (Scree.fly_QM d he.2.1 he.2.2 (PX.Q j) F e hp (PX.wear j v)) ((PX.balance _ v.le).trans (PX.balance _ v).symm)
noncomputable def liftV (j:ℕ)(T:Pane (cell M B R.L j) →ℂ) : (k:ℕ)→ Pane (cell M B R.L (j+k))→ℂ
 | 0=>T
 | k+1=> (Z_G (j+k)) (liftV j T k)
local notation "PΞ" j=>liftV V a p i N0 J q h R0 δ PX j
variable (s:Axis){α:ℕ}(F F1:Pane (cell M B R.L α)→ℂ)(hv:ξTape s R _ F)(ht:ξTape s R _ F1)
include hv
lemma liftCost (k:ℕ) : ξTape s R _ ((PΞ α) F k):=by
 induction k with|zero=> exact hv|succ n ih=>exact ξ_fwd R _ _ (actualG V a p i N0 J q h R0 δ PX (α+n)).1 (actualG V a p i N0 J q h R0 δ PX (α+n)).2.2 ih _
include ht
-- EXACT reflected products of all these sectors.Generator theta same localObs; on intervening levels stencils if needed may be approximated arbitrarily BOREL bounded; see DockSmooth.
theorem liftSquareG (k:ℕ)(v:α+k ≤ PX.top): (Z_V α) (flipTime (Vale.mesh M R.L α) B s (bosonic _ F)*bosonic _ F1) =(Z_V (α+k)) (flipTime (Vale.mesh M R.L (α+k)) B s (bosonic _ ((PΞ α) F k))*bosonic _ ((PΞ α) F1 k)):=by
 simp_rw [θ_bosonic,boseP]; induction k with
 | zero=>rfl
 | succ k ih=>
    let j:=α+k; have hz:j<PX.top:=v; let a₀:= (PΞ α) F k; let a₁:= (PΞ α) F1 k; let Y:= (θBack s a₀) * a₁; have p₀:= liftCost V a p i N0 J q h R0 δ PX s F hv k; have p₁:= liftCost V a p i N0 J q h R0 δ PX s F1 ht k; have v₀: Envelope a₀:=⟨p₀.borel,p₀.cost⟩; have v₁: Envelope a₁:=⟨p₁.borel,p₁.cost⟩
    rw [ih (by omega)]; change (Z_V j) (bosonic _ Y)=(Z_V (j+1)) (bosonic _ ((θBack s ((Z_G j) a₀))* ((Z_G j) a₁))) -- notation space
    rw [hhgo V a p i N0 J q h R0 δ PX j hz Y ((θ_back_env s v₀).mulC v₁)]; apply congrArg ((Z_V (j+1)) ∘ bosonic (cell M B R.L (j+1))); exact ξ_fact R s _ (actualG V a p i N0 J q h R0 δ PX j).2.2 v₀ v₁ p₀.localSites p₁.localSites _
end Carousel
end YM.CF.Py.Period
#print axioms YM.CF.Py.Period.Carousel.liftSquareG
