import YM.SU5.Interaction.Reg.Extent
import YM.SU5.Interaction.Reg.Tapped
import YM.SU5.Interaction.Reg.Pulp
import YM.CF.Vp929.Stage.Issue

/-! (124) microscopic price of the outputs of these particular Shop's operations. -/
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
local notation "FL"=> (Pair (Corr ηt))

local notation "ℓ"=> R.L.val
local notation "θL"=> V.L.path (w.lag+1)
local notation "λS"=> K.top.clip
local notation "hΠ"=> K.below.paths
local notation "ψP"=> K.below.width
local notation "Vr"=> s.redo
local notation "rp"=> packR p θL λS Vr
local notation "rq"=> packF p θL λS R.L.val Vr s.Ty
local notation "tp"=> shipA p R.L.val λS ψP hΠ s.Aχ
local notation "tq"=> shipT p R.L.val λS ψP hΠ s.Aχ s.Γχ

open Glyph
abbrev staffingEdge (s:ℕ):= max (max 1 (mstar s)) Lunar.reach305
lemma hoodSupport (Z:RegBudget ι)(i:Scree.Hub ι)(v:staffingEdge R.L.val < coverNumber p.B i.val.2) : head_L (s.hood Z) i=0 := by
 funext V
 change cut_V (((NetX Vr p (lmap s.A0.dream (shiftM p Z R.L xm K.j s.s.k))) + _ • rp) i V)=0
 simp only [Pi.add_apply,Pi.smul_apply]
 rw [(NetHere (f:=Vr) (s.shape.expands R.L.val).choose_spec _ i ((le_max_left ..).trans_lt v)),Pi.zero_apply,zero_add,map_smul,paid0.mp (packScalar (F:=Vr) s.S0 s.Ty (dr).floor) i V,smul_zero]

variable {b:ℂ}
-- from actual RepE to verseY before Shaving but AFTER the pF consultations
lemma keepsVerse (F: Pair (Corr (mid n B)))(i:Scree.Hub ι)(v:staffingEdge R.L.val < coverNumber p.B i.val.2): head_L (s.RepE b F).1 i = head_L (verseY (Lp:=s.Lp) (A0:=s.A0) s.Ty (s.standby b F) b F).1 i := by
 let E:=(s.pF b F).1
 let u:=s.S0; let Q:=(EkX (s.standby b F) b F).1
 funext x; change cut_V (E i x+ (s.hood E) i x)=_
 rw [map_add, show cut_V (s.hood E i x)=0 from congr_fun (s.hoodSupport E i v) x,add_zero]; exact congrFun (congrFun (brolExact p θL u.mass s.Aχ u.day u.ha u.decent u.span u.n0 (dr).floor Q ℓ) i) x
end Shop
end Focus
end Pitching
end YM.CF.Py.Rate
