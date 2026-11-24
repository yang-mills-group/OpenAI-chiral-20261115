import YM.CF.Vp929.Stage.Bundle
import YM.CF.Vp929.Canon.Verv
set_option autoImplicit false
set_option quotPrecheck false
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
open Ione Beau Haro Cascade Fief
open scoped Mew

open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
open Eire Girt
open VolumeRate
variable {d:ℝ} {m n N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
variable {A C' Pay h ρ f ff ag Cg x β β' : ℝ} {D : Treaty J q A C' Pay h ρ} {c:Estimate}
variable {w:Location (R:=R) B m n} {p p' : BudgetPoint}
namespace Pitching

namespace Focus
open Sour.MatchW Sour.MatchW.Technique Cycle929 Tap Lilt Vow Ione Beau
open Sour Stockpile Test TestW QuiltB
local notation "τ0"=> mid m B
namespace Shop
open BudgetPoint
variable {r:ℝ}[Nonempty (Haro.ΘS r)]
variable (s:Shop w J p p' q h x r)
local notation "ι"=> Scree.mid m B
local notation "ηt"=> Scree.mid n B
local notation "Er"=> (ΘS r)
local notation "Tp"=> (Pair (Haro.ΘS r))
local notation "μ"=> ↥SpaceM
local notation "Eμ"=> Pair ↥SpaceM
variable {y:ℂ}{G H:Corr (Scree.mid n B)}{S:Set ℂ}
local notation "Shf"=> w.freq
local notation "φE"=> (houseP p K s.Aχ s.Γχ s.Λf)
local notation "dr"=> s.A0.dream
local notation "VE"=> shownP (A0:=s.A0) (Lp:=s.Lp) s.Ty
local notation "Ex"=> verseX (Lp:=s.Lp) (A0:=s.A0) s.Ty
local notation "EkX"=> verseY (Lp:=s.Lp) (A0:=s.A0) s.Ty
local notation "δφ"=> rollGX K.j s.s.k R.L.val (houseP p K s.Aχ s.Γχ s.Λf) h
local notation "xm"=> w.output.M
local notation "xT"=> pointW ι K.j s.s.k xm
local notation "sx"=> treeΘ p R.L.val
local notation "Sch"=> Client K R x w.input p' h
local notation "Sub"=> Pair (RegBudget ι)
local notation "Wp"=> s.multiplier
local notation "Sx"=> s.stepV
include s
open Rue Push.BetaTransport
local notation "Bζ"=> (β:ℂ)

variable {h' r' x':ℝ}[Nonempty (ΘS r')]
variable {R0 R1:BudgetPoint}(T:Shop w J R0 R1 q h' x' r') {u v u₁ v₁:ℂ}

local notation "X0"=> w.buildIn V p' β G u
local notation "X1"=> w.buildIn V R1 β H v
local notation "CΓ"=> Client K R x' w.input R1 h'
local notation "Pδ"=> s.pickW (β:ℂ) (G,0)
local notation "Pδ'"=> T.pickW (β:ℂ) (H,0)
local notation "δm"=> Pδ.1
local notation "δm'"=> Pδ'.1
local notation "δQ" Z:max=> waveTest Shf Z K.j xm
variable (q₀: Client K R x w.input p' h (β:ℂ) (G,0))(q₁: Client K R x' w.input R1 h' (β:ℂ) (H,0))(e: denZ (w.buildIn V p' β G u) U w.fine =ᵐ[city (Scree.mid n B)] denZ (w.buildIn V R1 β H v) U w.fine) {E E': Corr (mid m B)}{t g:ℝ}
include s T e

lemma lookover (Y: μ) (Vζ:Orbit ι) : Scree.stove U w.coarse X0 w.fine w.G (w.step V) q J.d Y.val Vζ= Scree.stove U w.coarse X1 w.fine w.G (w.step V) q J.d Y.val Vζ:=by
 unfold Scree.stove; apply MeasureTheory.integral_congr_ae; filter_upwards [e] with W hv; apply congrArg (_ • ·); apply sum_congr rfl; intro F t; unfold Scree.carrier; rw [hv]
lemma landed {Y Z:μ}(eb:Y=Z)(L:Launch p p' w U q J.d E G β t u u₁ Y)(L':Launch R0 R1 w U q J.d E' H β g v v₁ Z) (A:Orbit ι)(hp:Rue.FleetS p.threshold A.1)(ht:Rue.FleetS R0.threshold A.1): denZ (w.buildOut V p (β+w.movement V-t) E u₁) U w.coarse A=denZ (w.buildOut V R0 (β+w.movement V-g) E' v₁) U w.coarse A:=by rw [L.wear A hp,L'.wear A ht,eb, lookover s T e]
variable {N0:ℕ}(pQ:Location.Request V U W J q w N0 x p p')
local notation "Vh"=> closedBall (0:Eμ) (r/2)
local notation "Wh"=> closedBall (0:Eμ) (r'/2)
include pQ
lemma patrol: p.power=2 ∧ R0.power=2:=⟨pQ.boot.power,T.ownership.symm ▸ (let_X HI x').2.1⟩
omit T pQ e

local notation "θw"=> makeK (A0:=s.A0) (Lp:=s.Lp) s.Ty
lemma emits (q₀:Sch (β:ℂ) (G,0))(i:Eμ)(hi:i∈Vh)(hm:i.2=0) (u:ℂ): let X:= s.stepV (β:ℂ) (G,0) i; X.2=0∧ IncX Utrue X.1 p h φE ∧ ∃ (c:ℝ)(v: ℂ)(KX:ForceBudget ι), Launch p p' w U q J.d (X.1,KX) G β c u v i.1 := by
 intro X; let t:= inwardP r i; let z:=t.1; have he:=s.real_I hi hm; change t=rePoint z at he; have hu:=s.half_room hi; let V0:= intent1 (mem_ball_zero_iff.mp hu); have hp': sunny (rePoint z):= he ▸ V0; let E:=VE t (β:ℂ) (G,0); obtain ⟨b,x,zE,w₀,v,Lt,-⟩:= exhibit s.qL s.s s.Th s.S0 s.Ty s.coin s.pH s.Mp s.solv z hp' q₀
 change E.2=0 ∧IncX Utrue E.1 p h _∧ ∃ _ _ _, Launch _ _ _ _ _ _ (E.1,_) _ _ _ _ _ _; unfold E; rw [he]; let Z:= house_r (A0:=s.A0) s.qL s.s s.Th s.S0 s.Ty _ q₀ _ hp'; have hx:z.val=i.1:=congrArg Prod.fst (intent0 i (mem_ball_zero_iff.mp hu).le)
 rw [hx] at Lt; exact ⟨x,Z.1.1.1,_,_,_, by simpa only [zero_add] using Lt.adjust u⟩
include T q₀ q₁ pQ e
lemma perspective (Y:Eμ)(h:Y∈ Vh)(g:Y∈ Wh)(pS:Y.2=0): s.multiplier Bζ (G,0) Y=T.multiplier Bζ (H,0) Y:=by
 obtain ⟨a,uP,d,vx,Q,L⟩:=s.emits q₀ Y h pS u; obtain ⟨p,uK,d',vx',Q',L'⟩:=T.emits q₁ Y g pS v
 let H:= landed s T e rfl L L'; let k:=s.patrol T e pQ; let ht:= Plum.trace_agree H (J.gran.trans pQ.rocket.size) pQ.rocket.paid J.hr.le pQ.pole
 obtain eU:= ovis R0 uP uK ht (dr).floor k.1 T.A0.dream.floor k.2 s.GraspY s.s.k
 refine Prod.ext (congrArg (Y.1+·) eU) ((s.real_aim q₀ Y h pS).trans (T.real_aim q₁ Y g pS).symm)
lemma commonQ (t:r≤r'): Pδ=Pδ':=by
 obtain ⟨i,hz⟩:=(s.sleepsW q₀).1; have u:Pδ∈Wh:=closedBall_subset_closedBall (by linarith) i; exact (T.sleepsW q₁).2.1 _ ⟨u,Eq.trans (s.perspective T q₀ q₁ e pQ _ i u (s.real_pick q₀)).symm hz⟩
lemma brothers {n0:ℕ}(pT: Location.Request V U W J q w n0 x' R0 R1): s.pickW Bζ (G,0)= T.pickW Bζ (H,0):= by rcases le_total r r' with h|h; exact s.commonQ T q₀ q₁ e pQ h; exact (T.commonQ s q₁ q₀ e.symm pT h).symm
local notation "E0"=> s.operate
local notation "E1"=> T.operate
lemma prosper {n0:ℕ}(pT:Location.Request V U W J q w n0 x' R0 R1): let Z:=(E0).output V w p β G u; let Z':=(E1).output V w R0 β H v; (E0).wave β G=(E1).wave β H∧ Z.beta=Z'.beta ∧ ∀ y,FleetS p.threshold y.1→ FleetS R0.threshold y.1 → denZ Z U w.coarse y=denZ Z' U w.coarse y:=by
 intro Z Z'; obtain ⟨⟨g,k⟩,t,_⟩:= s.RepReal q₀ u; obtain ⟨⟨g',k'⟩,t',_⟩:=T.RepReal q₁ v; have hp:(E0).wave β G=(E1).wave β H:=congrArg Prod.fst (s.brothers T q₀ q₁ e pQ pT); let Q':= s.landed T e hp t t'
 let k:=s.pinK.toPiece; let hK:= k.kinSmooth (dr).floor (transverse (s:=ι) Shf); refine ⟨hp,vervP Q' (fun x=>(pQ.rocket.paid.paid x).shrink J.hr.le) (J.gran.trans pQ.rocket.size) Shf (s.careτ q₀).1.1.house.tax (T.careτ q₁).1.1.house.tax (dr).floor T.A0.dream.floor g g' ((Test.posed _).trans_le (macy s.S0.mass s.GraspY _ hK)) hK,Q'⟩
end Shop
end Focus
end Pitching
end YM.CF.Py.Rate
