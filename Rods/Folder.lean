import Rods.Stage
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
local notation "Sm" j:max=> mid (A.side j) B
variable {I:Type}[LinearOrder I][Fintype I]{r j:ℕ}(i:Axis)(z:ℤ)(x:f ≤ j)(p:j ≤ r)(t:r≤v)
-- assemble sport instance at Sm j. orient roles incl both p and gap. heat $Y.v$ on layout. link $W m = Sm j cast proof.Specialize m:=Vale.mesh.Paper. Wrapper define new Sport by lifting K using equivalence types(local cast via general N proposition). 
abbrev Si (n:Side):Type:= PairKey (Site n) -- instances LinearOrder Site n unavailable? lex [order zmod n], Fin c equivalence. Try
#check Seat
-- instead tags Site n×Bool, pose at arbitrary i via Fin 1 presentation.Pay identify later. 
abbrev Tix(j:ℕ):Type:= Site (mid (A.side j) B)×Bool
variable (j r:ℕ)(e:Tix A j)(a:Axis)(s:ℤ)(c d:ℝ)
def pose2(v:ℕ)(φ:Vxpert V A)(C D:ℕ→ℝ):Mark (Sm v):=
   let o:=fun _:Fin 1=> e.1; playto (fun k=>cameo (liftCanvas V A r v (liftCanvas V A j r o) k) (A.gram v).p (A.money v)) (fun k=>blaze V A φ r v (cameo (liftCanvas V A j r o k) (A.gram r).p (A.money r))) (shareT R.L C D r v j) (shareS R.L r j) ((0,e.2):PairKey (Fin 1)) -- include V φ? φ implicit not in sig! need add to var form
abbrev ward (e:Tix A j):= sitepad e.1 22
#check pose2
variable (C D₁:ℕ→ℝ)
variable (uA:f≤ j)(uQ:j≤r)(uE:r≤v)
include uA uQ uE h J S
lemma folded2 (fe:ward A j e⊆band _ a s U): AtSupport false (band (Sm v) a ((R.L.val:ℤ)^(v-j)*s) U) (pose2 A j r e v φ C D₁)∧ pose2 A j r ((center _ a s e.1,e.2):Tix A j) v φ C D₁= reflMark a ((R.L.val:ℤ)^(v-j)*s) (pose2 A j r e v φ C D₁):=by
 let m:=fun _:Fin 1=>e.1; let m' :=center _ a s∘m
 let s':=(R.L.val:ℤ)^(r-j)*s; let s0:=(R.L.val:ℤ)^(v-r)*s'; have hz:(R.L.val:ℤ)^(v-j)*s = s0:=by unfold s0 s'; rw [show v-j=(v-r)+(r-j) from by omega,pow_add,mul_assoc]
 rw [hz]; let o':=liftCanvas V A j r m; let ov:=liftCanvas V A r v o'
 let Fr:=cameo (o' 0) (A.gram r).p (A.money r)
 let Tq:=blaze V A φ r v
 let Fv:=cameo (ov 0) (A.gram v).p (A.money v)
 let Q:PairKey (Fin 1):=(0,e.2); let Bc:=shareT R.L C D₁ r v j Q; let Bd:=shareS R.L r j Q
 change AtSupport _ _ (Bc • Fv + Bd • Tq Fr) ∧ Bc • cameo (liftCanvas V A r v (liftCanvas V A j r m') 0) _ _ + Bd • Tq (cameo (liftCanvas V A j r m' 0) _ _)=reflMark _ _ (Bc • Fv + Bd • Tq Fr)
 have hf:= fitsV A J S h a s j r uQ m 0 fe; have hv:= fitsV A J S h a s' r v uE o' 0 hf
 have hd:AtSupport false (band (Sm r) a s' U) Fr:= (scheduleY V A r _ _).mono hf
 obtain ⟨vK,xM⟩:= cargoV A J S h r a s' (uA.trans uQ) uE Fr hd
 have he: AtSupport false (band _ a s0 U) Fv:= (scheduleY V A v _ _).mono hv
 refine ⟨(he.smulM Bc).addM (vK.smulM Bd),?_⟩
 have q:liftCanvas V A j r m'= center _ a s' ∘ o':=funext fun k=> (moves_frames2 A J S j r a s uQ m k).symm
 have v2:liftCanvas V A r v (center _ a s'∘o') 0=center _ a s0 (ov 0):=(moves_frames2 A J S r v a s' uE o' 0).symm
 rw [q,v2]; change Bc • cameo (center (Sm v) a s0 (ov 0)) (A.gram v).p (A.money v)+Bd • Tq (cameo (center (Sm r) a s' _) _ _) = _
 -- use have rewrites instead
 rw [cameo_fold,cameo_fold]; change Bc • reflMark a s0 Fv+ Bd • Tq (reflMark _ s' Fr)=_; rw [show Tq (reflMark a s' Fr)= _ from xM]
 funext i; unfold reflMark; simp only [Pi.smul_apply,Pi.add_apply,theta_add,theta_smul]; have hc: star Bc=Bc:=by unfold Bc shareT; split <;> exact Complex.conj_ofReal _
 have hm: star Bd=Bd:=by unfold Bd shareS; split; exact Complex.conj_ofReal _; simp
 rw [hc,hm]
#check folded2
end Decaf
end YM.CF.Py.Rate
end
