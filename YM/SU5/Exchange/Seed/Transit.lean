import YM.SU5.Exchange.Seed.Ship
import YM.SU5.Exchange.Seed.Zero
import YM.SU5.Exchange.Seed.Keys
import YM.SU5.Exchange.Seed.Marks
import YM.CF.Rive.New
import YM.CF.Song.Pads
import SatinThinTopic
set_option autoImplicit false
set_option maxHeartbeats 950000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Vow
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
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
open Rue
namespace TreasuryFog

open QuadClock Waxy Push.AbsoluteSums Trees Rue Rive Vow Larch Stax Sour Cadre Mew Ione Gas Ursell
open Roots Oise
open Py
open scoped YM.CF.Mew
-- exact kinenter preserving root budget identity
variable {N B₁:Side}{L:Side}{j:ℕ}{ho:Odd L.val}{Y:Pricing j L ho (Thread j)}{e u:ℝ}
local notation "n1"=>mid N B₁
variable {R:GramM (mid N B₁)}
variable (U:Grasp Y B₁ e)(A:Scree.Loom (mid N B₁))(V:Orbit (mid N B₁))
variable (M :Op (Single (mid N B₁)))

variable {I:Type}[LinearOrder I][Fintype I]
variable (C:Occlus R.p)
variable (F:ForceBudget (mid N B₁))(K : Key I→ Rinse (Seat (mid N B₁)) (Copy (mid N B₁))) {z b: Aura (mid N B₁)→ℝ} {r:Aura (mid N B₁)→Support (More (mid N B₁))→ℝ}
variable (σ:I→Seat (mid N B₁))(q:ℕ)(M:Key I→ Orbit (mid N B₁)→ Aura (mid N B₁)→ FC (Dwell (mid N B₁))) (T:OrbitRack C σ q R.K h K z b r M) (s:ℕ)(p:1≤h)(τ:Ids (mid N B₁))
local notation "Ψg"=>lensG (P:=R.p) (R.K) K s
local notation "DK"=>lensD (P:=R.p) (R.K) K s τ
local notation "DV"=>lensPort (P:=R.p) (R.K) K s
local notation "Θ"=>lensCells (R.K) K s
local notation "η"=>layerRay C R.K K σ q M T s p
local notation "Υ"=> Phys n1
local notation "P'"=> (settleK R.K)
open Bake Spire Dial
include p T
lemma flows_D (i:Scree.Hub (mid N B₁))(u:Pane (mid N B₁)) : River (fun z=> DK z i u):=by
 change River (fun z=> bassH (lagE i) • (Ψg z (lagE i) (u,τ)))
 exact bScale _ (lensSimpleR C R.K K σ q M T s p (lagE i) (u,τ)) _ -- tune
lemma flows_K (i:Force (mid N B₁))(u:Orbit (mid N B₁)): River (fun z=> DV z i u):=by
 change River (fun z=> bassH (lordD i) • lensK (P:=R.p) _ _ _ z (lordD i) _ u); unfold lensK
 refine bScale _ (moto_R (P:=R.p) Θ 0 η (fun _ _ _ V=>zeroR _) (lensSimpleR C R.K K σ q M T s p) _ _ u) _ -- order? explicit P. eta notation used
omit T p
local notation "Pᵣ"=>spar j R.J.M (A V)
variable (dS:IsStarProjection (spar j R.J.M (A V)))
def pilotH (U:Grasp Y B₁ e) (R:GramM (mid N B₁))(A:Scree.Loom (mid N B₁))(V:Orbit (mid N B₁))(dS:IsStarProjection (spar j R.J.M (A V))):
 Wave (Dwell (mid N B₁))→L[ℂ] Phys (mid N B₁):= (Complex.exp (R.betaL A V)) •
  ((Sault.ballL (nursery _ dS) (relV U R.J (A V))).toContinuousLinearMap.comp ((acts (exp (exponentL R.p R.F V.1+exponentL R.p R.slip V.1):Cipher _).val))) -- acts is CLM? inspect. parentheses
local notation "H"=> pilotH U R A V dS
-- price.Raw goes through compressed Fock via left multiplication from exterior exponent.
variable (l:List I)(v:ψS σ l)

lemma showUp (G:RegBudget (mid N B₁))(F:ForceBudget (mid N B₁)) : denZ (color_b R R.beta (R.F+G) R.slip F R.v) U A V= pilotH U R A V dS (Cadre.poseL _ (exp (exponentL R.p G V.1)*fueled R.p F V)):=by
 letI :NormedAlgebra ℚ (Cipher n1):= NormedAlgebra.restrictScalars ℚ ℂ _; let K:=exponentL R.p R.F V.1+exponentL R.p R.slip V.1
 let E:= exponentL R.p G V.1; let T:= color_b R R.beta (R.F+G) R.slip F R.v; let Q:=fueled R.p F V
 have hQ:T.board V=exp K*(exp E*Q):=by
    change exp (exponentL R.p (R.F+G) _+ _)*_= _
    rw [(exp_gain (P:=R.p) (i:=V.1) R.F G 0).2,add_right_comm _ (exponentL _ _ _)]; rw [exp_add]; exact mul_assoc ..
 unfold denZ; rw [hQ]; let J:=nursery _ dS; let D:=J.cook (exp K*(exp E*Q)); let u:=relV U R.J (A V); let w:=Sault.ballL J u
 change _ • acts D u=(Complex.exp (R.betaL A V)) • w (acts (exp K).val (acts (exp E*Q).val (vacuum (Dwell _)))) -- infer `tank` using defeq? `tower ships`
 rw [←act_mul]; exact congrArg ((Complex.exp (R.betaL A V)) • ·) ((Sault.loaf J u _).symm)

variable (E:I→RegBudget (mid N B₁))(β0:∀ i U, exponentL R.p (E i) U= exponentL R.p (νΦX (lensD (P:=R.p) R.K K s τ) {i}) U)
local notation "Vξ"=> awake σ DK E
local notation "Vζ"=> bustle σ DV
def slither (z:Key I):GramM (mid N B₁):= color_b R R.beta (R.F+ (Vξ z)) R.slip (R.K+ (Vζ z)) R.v
include T p v β0
lemma rackKey (M':I→ FC (Single (mid N B₁)))(Pq:FleetS R.p.threshold V.1) (w:l.length ≤ s)(pM:l.Pairwise (fun i j=> Commute (M' i) (M' j)))(ht:∀ z∈hill I,∀ X: Wave (Dwell (mid N B₁)),pilotH U R A V dS (acts (∑ Y:Aura n1,M z V Y) X)=acts (Liss.waveΦ M' z) (pilotH U R A V dS X)) :
 tipI (fun z=> denZ (slither (R:=R) K σ s τ E z) U A V) l= acts (l.map M').prod (denZ R U A V):=by
 let P:=settleK R.K; let D:= fun z:Key I=> Θ z; let O:=flags R.p.threshold V.1
 let Wp(z:Key I):=exp (exponentL R.p (Vξ z) V.1)*fueled R.p (R.K+ (Vζ z)) V; let K': Cipher n1→ₗ[ℂ] Phys n1:= ⟨⟨fun i=>H (Cadre.poseL _ i),fun x y=> (congrArg (fun v=>H v) (act_add ..)).trans (map_add ..)⟩,fun x y=> (congrArg (fun v=>H v) (act_smul ..)).trans (map_smul ..)⟩
 let L:= K'.toContinuousLinearMap
 have he(x:Key I): denZ (slither (R:=R) K σ s τ E x) U A V=L (Wp x):= showUp U A V dS _ _
 let V'(z:Key I):= exp (exponentL R.p (DK z) V.1)*fueled R.p (R.K+(DV z-DV 0)) V
 have BV :Soft l (fun x=>L (V' x)) (fun x=>L (Wp x)) := by
    have hg:= castEra (P:=R.p) σ DK E (lensOrigin C R.K K σ q M T s p τ).1 (flows_D (R:=R) C K σ q M T s p τ) β0 l v V.1
    have hK:= castFuel (n:=n1) (P:=R.p) σ DV (flows_K (R:=R) C K σ q M T s p) l v R.K V
    exact ((((hg).expΩ (uS_b σ v)).mul hK (uS_b σ v)).graph L)
 let f(z:Key I):= H (Cadre.poseL _ (hGas O (hailV O (D z) V)))
 have hv: Set.EqOn f (fun x=> L (V' x)) (hill I):=by
    intro z w; change H _=H _; exact congrArg (fun k:Cipher n1=> H (Cadre.poseL _ k)) (lensCash C R.K K σ q M T s p τ z V Pq w)
 rw [funext he,← BV.tip l (List.Sublist.refl _),←show tipI f l=tipI (fun x=> L (V' x)) l from lace_C l hv roots]
 let c:= pilotH U R A V dS (poseL _ (hGas O (hailV O P V)))
 have hξ:tipI f l= acts (l.map M').prod c := (concreteTip P r T.pigment K _ T.price (zero_le_one.trans p) V Pq T.gamb H (Liss.waveΦ M') l s w ht).trans (Liss.ketTip M' l (uS_b σ v) pM c)
 rw [hξ]; apply congrArg (acts _)
 have hr:= showUp (R:=R) U A V dS 0 R.K
 have hp:exponentL R.p 0 V.1=0:=by simp [exponentL,numbE]
 rw [hp,exp_zero,one_mul,add_zero] at hr
 change H (poseL _ (hGas O (hailV O P V)))= _
 rw [totGas C R.K K σ q M T p, settleSelf V Pq]
 exact hr.symm

end TreasuryFog
end YM.CF.Vow

#print axioms YM.CF.Vow.TreasuryFog.rackKey
