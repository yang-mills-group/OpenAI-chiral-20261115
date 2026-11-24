import YM.CF.Yaw.Holly
import YM.CF.Pig.Mixed
import YM.CF.Yaw.Heron
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Yaw
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Eire Jet Scroll Push.AbsoluteSums.Trees PetalP
variable {I N P B:Side}(S:StepData (Domain N B) (Domain P B)) (G:Ratio (mid N B) (mid P B)){r d k l D:ℕ}
open Rush Scroll Paige Vault Phase Acorn Spire
variable {ι:Type}[Fintype ι][DecidableEq ι](X:ι→ Palot.leaf (Site (Domain N B)))
local notation "m"=> mid P B
local notation "V'"=> Domain P B
local notation "H_"=> Eire.Ride S
local notation "S_"=> Eire.Folk S r ι
local notation "τ"=> Oboe (Single (mid P B))
local notation "χ"=> (LeanV (Single (mid P B)))
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
variable{S G}
variable (L:List (Kite S r))(U:List (Rust (mid P B)))(W:List ι)
local notation "Z'"=> weave_g L U W
open Eire Dress
variable {e A Q:ℝ}(R:GramM (mid P B))(M:E→Monk SU.group S)(T: ∀ i:E, Dress G S e r D (M i) R k X)
variable (eK:ℕ)(Q':Hos S r→ Sweep (mid P B))(G_u: ∀ O:Hos S r, Support (Domain P B) →ℝ)
variable (P': Tints P B e)(Gm:∀ i:Support (Domain P B), Lend P B e i)(U':Ids (mid P B))
variable (HX:TailB→Support (Domain P B)→Toll (Iota G))(HY:Grave→Support (Domain P B)→Toll (Iota G))
variable {B_:ℝ}
local notation "QU"=> facesH eK Q' G_u Gm
local notation "Z₁"=> (Z').toFinset
open Esti Oriented
variable (Y:Raid (LeanV (Single (mid N B))))(C:Rust (mid P B)→ Raid (LeanV (Single (mid P B))))(Yp: Folk S r ι→ Raid (LeanV (Single (mid N B))))(a0:Ride S)(z:E)
local notation "F₀"=>sign_l G S k eK HX
local notation "W₀"=>sign_z G S k eK HY
local notation "Q₁"=>BranchX (ι:=ι) S X k
local notation "Q₀"=> ξH G S HX HY k eK Y
variable (wK:0≤C)(g:L.Nodup)(p:U.Nodup)(v:W.Nodup) (H:∀ i∈weave_g L U W,0≤ Yp i)(y:∀ i∈L,0≤ (facesH eK Q' G_u Gm i).led)
variable (VX: Meter TailB G e)(WX:Meter Grave G e)
variable (x:∀ i F, Suite (badge _) (pinH G e true) (pinH G e false) F (HX i F) (VX i F))(u:∀ i F, Suite (badge _) (pinH G e true) (pinH G e true) F (HY i F) (heal G e WX i F))
include y x u wK H g p v
lemma bounty_k {n₀:ℕ}(h:n₀≤eK) (s:ℕ)(Kp:ℝ)(q:Turner Y)(c:SpiritX Kp e eK): ∃ S1: Track (Eire.Ride S) (Raid (LeanV (Single (mid N B)))),0≤S1 ∧ rateT Y S1≤ payH (railsB X eK Q' G_u Gm HX HY Y C Yp s) (weave_g L U W) ∧∀(E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](z:E)(M:E→ Monk SU.group S)(x' Ah b:ℝ)(l:ℕ)(G_:Ids (mid P B))(R:GramM (mid P B))(T:(i:E)→Dress G S e r D (M i) R s X)(A':Ride S),
 let V(y:E):= (T y).blazon x' l (weave_g L U W).toFinset A'
 (z∈tsupport V → MixedL X L U W eK Q' G_u P' Gm G_ C Yp z n₀ A' M R T x' l VX WX Kp Ah b) → Woody n₀ (fun y=>(V y).val) z (S1 A'):=by
 have hx:=one_r L U W eK Q' G_u Gm C wK y; -- order
 obtain ⟨S',t,b,w⟩:= prism_p (J:=Eire.mint S) (D:=Eire.rayB) (X:=BranchX (r:=r) S X s) Y (ξH G S HX HY s eK Y) (weave_g L U W) (boast C) (feral QU) Yp (firm_p G S e VX WX HX HY s eK x u Y q) (fun i p=>(hx i p).1) (fun i p=>(hx i p).2) H -- check
 refine ⟨S',t,b,fun E _ _ _ z M x' Ah b l U' R T A' p'=>w _ _ _ _ _ fun v'=>?_⟩ -- h is let var
 exact ⟨_,capM X L U W R M T eK Q' G_u P' Gm U' HX HY C Yp A' z VX WX x u h _ c x' Ah b l g p v (p' v')⟩
-- distinguish
end YM.CF.Yaw
