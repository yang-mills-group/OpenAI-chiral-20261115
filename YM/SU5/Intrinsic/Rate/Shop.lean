import YM.SU5.Intrinsic.Rate.Lunar
import YM.SU5.Intrinsic.Rate.Port
import YM.SU5.Intrinsic.Rate.Tint
import YM.CF.Vp929.Stage.Bundle
import YM.CF.Vp929.Stage.Issue

/-! # XXI payment: over the parts of the **same** Shop. -/
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

local notation "FL"=> (Pair (Corr ηt))

local notation "ℓ"=> R.L.val
local notation "θL"=> V.L.path (w.lag+1)
local notation "λS"=> K.top.clip
local notation "hΠ"=> K.below.paths
local notation "ψP"=> K.below.width

-- height-parametric expenses for appointment below
abbrev tableCost (R : Patch) (p : BudgetPoint) (r h b0 b1 b2 κ γ x : ℝ) :=
 coinW R x κ 1 (ticket_f (radiusB x) γ 1 + burnQ R x κ 1) +
 φcape (plusOneRate p) b0 (Tenant.quota^2*b1*r) (Tenant.quota^2*b2*r) h +
 Scales.g SU.group R.L x^2 + Glyph.cap1 (plusOneRate p) (BondL.øK r) h

open Appel.Rate Stockpile
variable {κq γq ff₁:ℝ} {o : Pitching w D x} {Bv:ℝ}{nₐ N₀:ℕ}{pW:WindV K.j 2} {C:stationary D c x ag Cg κq Bv nₐ}{Z0:Cellar N₀ o p p' c (allF R.L x) ag Cg}(T:Weather C Z0 pW γq)(Vq:Rill.Arch w.G d)(hv:Vq.val=1)(Ty:Ids (Scree.mid m B))

include T hv
lemma literal_art (pK:Sch (β:ℂ) (G,0)) : let F:= tapped p o Ty (Banker.Phi Z0 (β:ℂ) G); let X:=((articles (Z0:=Z0) Ty Vq).Eτ β (G,0)).1
 IncX Utrue F (plusOneRate p) h (coinW R x κq 1 (ticket_f (radiusB x) γq 1 + burnQ R x κq 1)) ∧ ∀ i:Scree.Hub ι,lunarExtent<coverNumber p.B i.val.2 → X i=F i:=by
 intro F X; refine ⟨addressed_pressure Ty T Vq hv pK, fun i v=>?_⟩
 rw [show X=pre_E (o:=o) (p:=p) (p':=p') Ty Vq (Banker.Phi Z0 (β:ℂ) G) G from congrArg Prod.fst ((billingReal T.toFocus Ty Vq hv T.fair β G).1)]
 change F i+(noncash_E (p:=p) (p':=p') (o:=o) Vq G) i=_
 have he:= (matured Ty T Vq hv _ pK).1
 rw [noncash_support T.toFocus (T.member he pK.1) Vq (he.mono (by have h:=T.buy; linarith)) _ v,add_zero]

lemma literal_boost (pK:Sch (β:ℂ) (G,0))
 (he:s.Lp=articles (Z0:=Z0) Ty Vq)
 (ht:2*(p.supportExponent+1)*Fief.tileN 1 ≤ s.b0/2*p.B):
 ∃ F':RegBudget ι, IncX Utrue F' (plusOneRate p) h (tableCost R p r h s.b0 s.b1 s.b2 κq γq x) ∧
 ∀ i:Scree.Hub ι, mstar R.L.val+1 < coverNumber p.B i.val.2 → lunarExtent<coverNumber p.B i.val.2 → head_L (s.operate.realArr β G).1 i=F' i:=by
 let H:Pair (Corr ηt):=(G,0); let Q':= s.standby β H
 let L':= s.Lp.Vφ β H; let V:=s.Lp.Eτ β H
 obtain ⟨t,u⟩:= s.A0.dream.rollHSurcharge Q'.1 ht
 let z:=(dr).nu_more s.Th Q' L' (s.qL.lens _ _ pK).1 (poise_R s.qL s.s s.Th s.Ty H Q' (s.homely pK) pK) s.Ty -- inspect Ty arg
 obtain ⟨K',B'⟩:=literal_art T Vq hv Ty pK
 let R':= Ione.addT (plusOneRate p) (Ione.addT (plusOneRate p) (Ione.addT (plusOneRate p) K' t) z) u
 refine ⟨_,(Beau.price_Q (plusOneRate p) _ R').1, fun i a b=>?_⟩
 change head_L (s.RepE β H).1 i= _; rw [RepE_long s _ _ i a]
 have ht:= (show (s.Lp.Eτ β H).1 i=tapped p o Ty (Banker.Phi Z0 (β:ℂ) G) i from by rw [he]; exact B' i b)
 funext V; apply congrArg cut_V; change (s.Lp.Eτ β H).1 i V + _ + _ + _ = _ -- tune
 rw [ht]; rfl
end Shop
end Focus
end Pitching
end YM.CF.Py.Rate
#print axioms YM.CF.Py.Rate.Pitching.Focus.Shop.literal_boost
