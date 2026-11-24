import Rods.Case
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
variable(j r p:ℕ){G:Calibration}{m:Side}(u₁: U=G.ℓ)(hf:f≤ j)(hr:j≤r)(hv:r≤ v)(hp:22≤ p)(C D₁:ℕ→ℝ)(he:Scree.mid (A.side j) B=G.c m)
local notation "tK"=> sportT A h j r p u₁ J S h hf hr hv u₁ hp C D₁ he
local notation "Σs" k:max=>mid (A.side k) B
variable (l:List (Tix A j))
abbrev queueTag:List (PairKey (Fin l.length)):= (List.finRange l.length).map (fun i=> ((i,(l.get i).2): Fin l.length×Bool))
abbrev roster(i:Fin l.length) : Site (mid (A.side j) B):= (l.get i).1 -- syntax
lemma noDouble : (wrap0 (queueTag A j l)).Nodup:=by
 change ((List.map _ _).map _).Nodup; rw [List.map_map,show Drift.yard ∘ (fun i:Fin l.length=> ((i,(l.get i).2):PairKey _)) = id from rfl,List.map_id]; exact List.nodup_finRange ..
#check List.pairwise_iff_get
#check List.map_get_finRange
lemma canvas_at (W Y:Type)[LinearOrder W][Fintype W][LinearOrder Y][Fintype Y](i:ℕ)(k:ℕ)(p:i≤k)(a:W→ Site (mid (A.side i) B))(b:Y→Site (mid (A.side i) B))(v:W)(u:Y)(t:a v=b u):liftCanvas V A i k a v=liftCanvas V A i k b u:=by
 rcases p.eq_or_lt with e|r; · subst i; simp [liftCanvas,hop_here,t]
 unfold liftCanvas; rw [hop_step (h:=r),hop_step (h:=r)]; exact canvas_at W Y (i+1) k r (adapt V A i a) (adapt V A i b) v u (congrArg (Hove.heel (A.ratio i)) t)
termination_by k-i
decreasing_by omega
lemma revenue_equator{I:Type}[LinearOrder I][Fintype I](x:Tix A j)(o:I)(p':I→ Site (mid (A.side j) B))(c:p' o=x.1)(hq:j≤r)(a:r≤v): pose2 A j r x v φ C D₁= playto (fun i:I=>cameo (liftCanvas V A r v (liftCanvas V A j r p') i) (A.gram v).p (A.money v)) (fun i:I=>blaze V A φ r v (cameo (liftCanvas V A j r p' i) (A.gram r).p (A.money r))) (shareT R.L C D₁ r v j) (shareS R.L r j) ((o,x.2):PairKey I):=by
 let m:= fun _: Fin 1=> x.1; let Q:=liftCanvas V A j r m; let Q':=liftCanvas V A j r p'
 have ht:= canvas_at A (Fin 1) I j r hq m p' 0 o c.symm
 have he:= canvas_at A (Fin 1) I r v a Q Q' 0 o ht
 unfold pose2 playto; dsimp only; change shareT R.L C D₁ r v j ((0,x.2):PairKey (Fin 1)) • cameo (liftCanvas V A r v Q 0) (A.gram v).p (A.money v) + shareS R.L r j ((0,x.2):PairKey (Fin 1)) • blaze V A φ r v (cameo (liftCanvas V A j r m 0) (A.gram r).p (A.money r))= _
 rw [ht,he]
include J S h u₁ hf hr hv hp
lemma links : Sport.film tK l = braidP (Yz:=φ) (v:=v) V A j r (roster A j l) C D₁ (queueTag A j l):=by
 unfold braidP spreadE queueTag Sport.film; rw [List.map_map]; apply congrArg List.prod
 conv_lhs => arg 2; rw [←List.map_get_finRange l]
 rw [List.map_map]
 apply List.map_congr_left; intros i t
 exact revenue_equator A j r C D₁ (l.get i) i (roster A j l) rfl hr hv
#print axioms links
end Decaf
end YM.CF.Py.Rate
end
