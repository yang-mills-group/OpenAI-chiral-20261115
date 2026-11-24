import YM.CF.Paxos.Fern
import YM.CF.BPress.Age.Lune

/- Adapted from FiniteGaugeData proofs in corresponding imported modules. Strengthening as in VolumeB-gate:
   keep q_P lower speed in same grant emitted while d, threshold still adjustable. This version is for
   B-main and any ordinary `MeterQ`, independent of comparison uses. -/
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
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
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
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
open Oath
lemma interval_pC(j k p:ℕ)(a:ℝ)(ht:6≤k)(hp:2≤p)(hb:4≤j)(u:Even j)(ha:0<a) : ∃ (K:Teller SU.group)(L:ChartRatio SU.group), K.j=j ∧ LocalRatio L ∧ K.top.clip.direct≤1 ∧∃ (C:ℝ)(n:ℕ),∀ (P:Patch),n≤ P.L.val→P.J=j→∃ (V:Grace K P L)(T:Acorn.Repair K.j)(l:ℕ),∀ B0:ℕ,l≤B0→∃ e yP:ℝ,0<yP∧0<e ∧∀ q:Chi,∀ d:ℝ,0<d→ d ≤ e→∃ (U:Grasp V.U (P.L^B0) d)(W:GivenX V U)(M:Side)(J:Robes M V W),W.pearl.q=yP∧ U.baseline ≤ T.d∧ J.k≤ J.roomX ∧ ∀ᶠ h:ℝ in atTop,∃ N₀:ℕ, Coffer (p:=p) (k:=k) V U W q a J.d J.n C N₀ J.k J.roomX h∧∀ m0:ℕ,∃ Q0 E G D:ℝ→ℝ,sizeK P.L 2 Q0∧Litt P 2 E∧ Litt P 2 G∧ Chill_v D∧∀ y:ℝ,∃ z:ℝ,y<z∧∃ S:Month z a k p N₀ V W,MeterQ V a p k N₀ J q h Q0 D z S:=by
 obtain ⟨K,L,z,Lr,k',D,Z,A,G,C,n,Y⟩:= lumen_pPS j k p a ht hp hb u ha; obtain ⟨i,h0⟩:=exists_nat_gt (4*C)
 refine ⟨K,L,z,Lr,k',C,n+i,fun P pP uP=>?_⟩; obtain ⟨V,T,l,U_⟩:=Y _ (by omega) uP; refine ⟨V,T,l,fun B hp'=>?_⟩; obtain ⟨e,aP,pa,x,hQ⟩:=U_ B hp'
 refine ⟨e,aP,pa,x,fun q d s t=>?_⟩; obtain ⟨U,W,M,J,Uφ,h,u,D⟩:= hQ q d s t; refine ⟨U,W,M,J,Uφ,h,u,?_⟩
 filter_upwards [D,eventually_ge_atTop (1:ℝ)] with H hz v; obtain ⟨N',z⟩:=hz; refine ⟨N',z,fun m0=>?_⟩; have hu:C/(P.L.val:ℝ)≤1/4:=by rw [div_le_iff₀ (by positivity)]; linarith [(h0.trans_le (Nat.cast_le.mpr (Nat.le_trans (Nat.le_add_left i n) pP)))]
 obtain ⟨R0,E,G,D,x1,x2,x3,x4,w,hs⟩:= form_T V a p k N' J q H C hu z m0
 exact ⟨R0,E,G,D,x1,x2,x3,x4,fun y=>prism_C V a p k N' m0 J q H R0 E G D w hs ht hp ha v y⟩
end YM.CF.Py


