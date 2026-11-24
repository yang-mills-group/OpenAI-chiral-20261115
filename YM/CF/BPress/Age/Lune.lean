import YM.CF.Paxos.Luz
import YM.CF.BPress.Age.Elm

/- Adapted from FiniteGaugeData proofs in corresponding imported modules. Strengthening as in VolumeB-gate:
   keep q_P lower speed in same grant emitted while d, threshold still adjustable. This version is for
   B-main and any ordinary `MeterQ`, independent of comparison uses. -/
set_option autoImplicit false
set_option maxHeartbeats 1160000
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
-- certify.WAGES off all granted tasks
variable {u Hh pK qK a γ vS dS kL w:ℝ}{r p i:ℕ}{X: GramM (mid N B)}{Y: GramM (mid P B)}{U:Grasp V.U B d}
open Oath Feu Feu.Corset Nor
lemma lumen_pPS (j k p:ℕ)(w:ℝ)(ht:6≤k)(hp:2≤p)(hb:4≤j)(u:Even j)(ha:0<w):∃ (K:Teller SU.group)(L:ChartRatio SU.group),K.j=j ∧ LocalRatio L ∧ K.top.clip.direct≤1 ∧∃ (D Z A:ℝ) (κ: SuitP k D),∃ C:ℝ,∃ N:ℕ,∀ (P:Patch),N ≤ P.L.val → P.J=j→ ∃ (V:Grace K P L)(T:Acorn.Repair K.j)(l:ℕ),∀ B:ℕ,l ≤ B → ∃ e yP:ℝ,0<yP∧0<e ∧∀ q:Chi,∀ d:ℝ,0<d→ d ≤ e →∃ (U:Grasp V.U (P.L^B) d)(W:GivenX V U)(M:Side)(J:Robes M V W),W.pearl.q=yP∧ U.baseline ≤ T.d∧ J.k≤ J.roomX ∧ (∀ᶠ h:ℝ in atTop,∃ n:ℕ,Coffer (p:=p) (k:=k) V U W q w J.d J.n C n J.k J.roomX h):=by
 obtain ⟨K,L,ζq,P0,hK,C,Z,A,κ,N,Y⟩:= elm_Bp j k p w ht hp hb u ha
 have hu: Even K.j:= ζq.symm ▸ u; let Q:= Classical.choice (waver K.j p (by omega) hp hu)
 obtain ⟨Aχ,uA,Dχ⟩:= Taxi.ori_u k; obtain ⟨Γχ,hQ,DG⟩:= Taxi.psalmB k
 obtain ⟨Wk,tW,wT⟩:= Haro.nova; let Yv:= pond_X k p w ht hp ha; let Cu:=(Beau.tax_E Yv K.below.clip K.below.width K.below.paths Aχ Γχ + 1)*νC Yv Wk*ray_T p k Z w Q.C 1
 refine ⟨K,L,ζq,P0,hK,C,Z,A,κ, Cu,N,fun L pL hL=>?_⟩
 obtain ⟨V,T,i,tQ⟩:=Y L pL hL; refine ⟨V,T,i,fun B' v=>?_⟩
 obtain ⟨e,yP,pp0,u,P⟩:=tQ B' v; obtain ⟨d,a',b0,c0,hδ,ht',hz,hW,n2,M⟩:=ores V Yv Wk (by omega) tW
 refine ⟨min e d,yP,pp0,lt_min u hδ,fun q e' h v=>?_⟩
 obtain ⟨U,W,M',J,Uφ,p_,x,l⟩:=P q e' h (v.trans (min_le_left ..))
 obtain ⟨qX,κ0,Jp,hU⟩:=l
 refine ⟨U,W,M',J,Uφ,p_,x,?_ ⟩; filter_upwards [hU 3,eventually_ge_atTop (1:ℝ),hW] with H h t wH
 obtain ⟨F,Z',n,Vv,ηp,Aq,ε⟩:=h; have hp':=ore_M V U W q q J.k w J.roomX J.d J.hr J.ht x J.n qX C κ Jp F Z' n H t 3 Z Vv ε
 exact ⟨n+n2, tree_PS (U:=U) V U W P0 q q J.k w J.roomX J.d Aq ha ht hp J.hr J.ht x J.n qX C κ Jp F Z' n H t 3 Z Vv hK Q Aχ Γχ Dχ DG uA hQ Wk a' b0 c0 d n2 (J.hr.le.trans (v.trans (min_le_right ..))) (by omega) tW wT M ht' hz wH ηp (by omega) hp'⟩
end YM.CF.Py


