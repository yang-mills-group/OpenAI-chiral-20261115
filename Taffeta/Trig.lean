import Taffeta.Est
import Taffeta.Linen
import Taffeta.Quote
import Sparkle.Curvature
import Sparkle.Seed
import YM.CF.Buffered.StepIdentity
set_option autoImplicit false
set_option maxHeartbeats 2200000
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
open Oath Feu Feu.Corset Haro Nor Siete PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Footprint Jade Py
-- earnings profiles quant issued b through \ell. Accept permit Rent
open Larch Vow Bake Mew Roots Rive Neon
local notation "BN"=> mid N B
local notation "Η"=> Scree.Hub (mid N B)
local notation "Θ"=> X.p.supportExponent
variable {J:Type}[LinearOrder J][Fintype J]
variable (σ:J→Site (mid N B))(K_ E0:Key J→ RegBudget (mid N B))(F_:Key J→ ForceBudget (mid N B))
variable (Xo Yo:Key J→ RegBudget (mid P B))(Zo:Key J→ ForceBudget (mid P B)) {G₀:Scree.Loom (mid N B)}{G₁:Scree.Loom (mid P B)} (Xi:Op SU.Slot){q:Chi}{h:ℝ}
local notation "Tz"=> Cube.node ∘ σ
local notation "P_"=> X.p
variable (Q:J→ℝ)(qE:J→ArcΦ)(qΨ:J→ ArcΦ)(s:J→ℂ)
variable {Vp Va Bk Cμ Wη Eμ Cx ZΨ QΦ ξQ:ℝ} -- remove
variable (Fκ:Cause_P V U G S G₀ G₁ X Y Xo Yo Zo Xi q kL h Vp Va σ Q qE K_ F_ qΨ s Bk Cμ Wη Eμ Cx ZΨ QΦ)
open Roots Mew Rive Oise
variable {α:Type}[DecidableEq α]
open scoped YM.CF.Mew
local notation "Ω"=> mid N B
local notation "qμ"=> (Cube.node ∘σ)
local notation "Ωk"=> MixT σ
open Drift Oise
attribute [-instance] instDecidableEqLex
open Compass
namespace Dyad
open Swell Compass Taxi Ione Tune Grain AnalyticBridge.VerifiedReset
open Buffered Larch
open Mew Keeping
variable {iS:Side}{I:Type}[Fintype I][LinearOrder I]
variable (F G:I→Mark iS)
local notation "PK"=>PairKey I
variable (α β:PairKey I→ℂ)
abbrev playto : PairKey I→Mark iS:=fun i=> α i • F i.1 + β i • G i.1
abbrev spreadE(l:List PK) :Mark iS:= (l.map (playto F G α β)).prod
abbrev F_prod(F:I→ Mark iS)(l:List I):=(l.map F).prod
-- Respect ordered mix.D.Value recurrence. AnnCouse. Linear only over benign (universal support). no need finset. prove terms.FEPI
variable (P0:∀ i,benign (F i))(P1:∀ i,benign (G i))(H:∀ i j x y, Commute ((G i) x) ((F j) y))
structure Reports (S0:Mark iS → ℂ):Prop where
  adds (F G:Mark iS): benign F → benign G → S0 (F+G)=S0 F+S0 G
  scale (F:Mark iS)(c:ℂ):S0 (c •F)=c*S0 F
variable (S0:Mark iS→ℂ)(d0:Reports S0)
include H
lemma supportComm (i:I)(l:List I):Commute (G i) (F_prod F l):=by
 induction l
 case nil=> exact Commute.one_right ..
 case cons j l e=>
   change Commute _ (F j* _); exact Commute.mul_right (show Commute (G i) (F j) from funext fun x=> (H i j x x).eq) e
omit H
lemma spread_at {W:Type}(X:W→Mark iS)(hq:∀ i:W,benign (X i))(L:List W):benign ((L.map X).prod):=by induction L with|nil=>exact AtSupport.oneM _|cons i L ih=>exact (hq i).mulM ih
lemma mul_scal(A B:Mark iS)(c:ℂ):A * (c • B)= c • (A*B):= funext fun i=> Algebra.mul_smul_comm c (A i) (B i)
lemma scal_mul(A B:Mark iS)(c:ℂ):(c • A)*B=c•(A*B):=funext fun i=>Algebra.smul_mul_assoc c (A i) (B i)
include H d0 P0 P1
lemma productQuote (l:List PK): S0 (spreadE F G α β l)= levy α β (fun u v=> S0 (F_prod F u * F_prod G v)) l:=by
 induction l generalizing S0
 case nil=> exact congrArg S0 (show (1:Mark iS)=1*1 from (one_mul _).symm)
 case cons i l ih=>
   let A:=F i.1; let B:=G i.1; let C:=spreadE F G α β l
   have hC:benign C:= spread_at _ (fun v=> ((P0 v.1).smulM (α v)).addM ((P1 v.1).smulM (β v))) l
   have hQ (Q:Mark iS)(p:benign Q): Reports (fun x=> S0 (Q*x)):=⟨fun F G u v=> (mul_add Q F G) ▸ d0.adds _ _ (AtSupport.mulM p u) (p.mulM v),fun F c=>(mul_scal Q F c) ▸ d0.scale (Q*F) c⟩ -- ▸ wrong orientation maybe
   have he(Fg:Mark iS)(p:benign Fg): S0 (Fg*C)= levy α β (fun u v=> S0 (Fg*(F_prod F u*F_prod G v))) l:= ih _ (hQ _ p)
   unfold spreadE levy; rw [List.map_cons,List.prod_cons]; change S0 ((α i • A+β i • B)*C)=_ ; rw [add_mul,d0.adds, scal_mul,scal_mul,d0.scale,d0.scale,he A (P0 _), he B (P1 _)]; swap; · exact ((P0 _).smulM _).mulM hC
   swap; · exact ((P1 _).smulM _).mulM hC
   refine congrArg₂ _ (congrArg ((α i)* ·) (levy_c _ _ _ _ _ ?_)) (congrArg (β i * ·) (levy_c _ _ _ _ _ ?_))
   · intro u t _ _; unfold F_prod; rw [List.map_cons,List.prod_cons,mul_assoc]
   intro v w _ _; have ht:= supportComm F G H i.1 v
   change S0 (B * (_ * F_prod G w))= S0 (_*(B*F_prod G w)); rw [←mul_assoc, ht.eq,mul_assoc] -- ht defeq B.H.
#check Reports
omit H d0 P0 P1
lemma genuineDesk (P:Grasp V.U B d)(G:GramM (mid N B))(f:Scree.Loom (mid N B))(h:Measurable f)(p:Integrable (denZ G P f) (city _)): Reports (station V (U:=P) (X:=G) (G₀:=f)):=by
 constructor
 · intro F H x y; unfold station; rw [mark_add h x.env y.env p,add_div]
 intro F c; unfold station; rw [mark_smul,mul_div_assoc]
lemma cameo_comm (X:BudgetPoint)(a:ℝ)(o:I→Site iS)(i j:I)(G:Mark iS)(x y: Fields iS):Commute (G x) ((cameo (o j) X a) y):= (Commute.one_right (G x)).smul_right ((tariffB (o j) X a y.1:ℝ):ℂ)
#print axioms genuineDesk
#print axioms productQuote
end Dyad
end YM.CF.Py
end
