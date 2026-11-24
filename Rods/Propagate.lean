import Rods.Fold
import YM.SU5.FiniteGaugeData.Pannier.Sketch
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief VolumeRate
open Roots Buffered LocalLimit LocalLimit.Papal Dyad Dyad.Keeping Mew Compass Drift
attribute [-instance] instDecidableEqLex
set_option quotPrecheck false
open Buffered Advance Afterglow YM.CF.Pannier.Chancel
namespace Decaf
open Stencil Push.SectorMeasure Larch
variable {K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group}{V:Grace K R L}{e kL:ℝ}{B:Side}{P:Grasp V.U B e}{qχ:Chi}(A:SiteLedger V P kL qχ){φ:Vxpert V A}{D0 f v D Q U:ℕ}(J:PaperTrace V A f v φ D0)(S:Tickets V D0 D Q R.L A f v)(h:Margin R.L D0 D Q U)
local notation "N" j:max=>mid (A.side j) B
variable {I:Type}[LinearOrder I][Fintype I]{j r:ℕ}(i:Axis){s:ℤ}(x:f ≤ j)(p:j≤ r)(t:r≤v)(o:I→Site (mid (A.side j) B))(b:I)
open Stencil
local notation "Gc"=> A.ratio j
local notation "E"=> (ratio Gc).embed
include A J S
lemma moves_one : center (N (j+1)) i ((R.L.val:ℤ)*s) (adapt V A j o b) = adapt V A j (center (N j) i s ∘ o) b:=by
 apply yu; rw [placing]
 have he (a: I→ Site (N j)) : node (adapt V A j a b)=(ratio Gc).embed (node (a b)):=Py.claw Gc (J.odd j) _
 rw [he,he]; change _= E (node (center (N j) i s _)); rw [placing, Shape.foldsT,plane_broad, S.side]
include p
omit p in
lemma moves_frames2 (j r₁:ℕ)(i:Axis)(s:ℤ)(e₁:j ≤ r₁)(o:I→Site (Scree.mid (A.side j) B))(b:I): center (N r₁) i ((R.L.val:ℤ)^(r₁-j)*s) (liftCanvas V A j r₁ o b) = liftCanvas V A j r₁ (center (N j) i s∘o) b:=by
 by_cases e:j<r₁; swap; · have t:j=r₁:=le_antisymm e₁ (Nat.le_of_not_lt e); subst r₁; simp [liftCanvas,hop_here]
 unfold liftCanvas; simp_rw [hop_step (h:=e)]; change center (N r₁) i _ (liftCanvas V A (j+1) r₁ _ b)= liftCanvas V A (j+1) r₁ _ b
 have ht:(r₁-j)=(r₁-(j+1))+1:=by omega
 have h:= moves_frames2 (j+1) r₁ i ((R.L.val:ℤ)*s) e (adapt V A j o) b
 rw [ht,pow_succ, mul_assoc,h]; refine congrArg (fun o=> liftCanvas V A (j+1) r₁ o b) (funext fun i=> ?_); exact moves_one A J S (s:=s) _ _ i -- V not explicit
termination_by r₁-j
decreasing_by omega
include x t h
lemma stages(g:j< v) {F:Mark (mid (A.side j) B)} (vA:AtSupport false (band _ i s U) F) : AtSupport false (band (N (j+1)) i ((R.L.val:ℤ)*s) U) (φ j F) ∧
                                φ j (reflMark i s F) = reflMark i ((R.L.val:ℤ)*s) (φ j F):=by
 obtain ⟨ns,a,Vt,⟨G⟩,b,eqR,T,W⟩:=J.clock j x g
 obtain ⟨a0,Y,a1,b1,C1⟩:=G.cap
 obtain ⟨fQ,hO⟩:= S.ask j x g
 rw [J.choice j]; unfold seatLect; let G₁:=A.gram (j+1)
 constructor
 · -- use margin adjusted with J≤Q: convert h Margin Q to Margin smaller
    have hu: Margin R.L D0 D (A.job j).patch.J U:=by unfold Buffered.Margin r₃ at h ⊢; omega
    exact (surround Gc (A.job j) K.j (A.opT j) _ (J.odd _) qχ kL _ (A.plant j) (G.power.symm ▸ Vt) b1.bill b G.legal.1 G.legal.2 _ vA fQ eqR).mono (margin_band i s hu Gc (S.side _) R.coarse)
 rw [←S.side j]; exact rising Gc (A.job j) K.j _ _ _ _ _ _ _ _ _ eqR vA b b1 (G.power.symm ▸ Vt) G.legal.1 G.legal.2
#check surround
#check rising
end Decaf
end YM.CF.Py.Rate
end
