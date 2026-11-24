import YM.CF.Vp929.Stage.Bolts

/-!
# R124. Removing the hood and brol for long-support positive exterior portions.
Following `Shape:pole_h`, `Pso/Solo.α_Ub`, `Canon/Galley`.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Beau
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
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k' m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset Vow Rue
open Ione
local notation "N"=> P.order
local notation "Xo"=>Skye.Seat n
open Ione Larch
open Taxi Geo RG.PathData Next.Scheduling UVNext.PricedKernels Work.F03 WilsonStartup
local notation "Hz"=> Scree.Hub n
open Trees
open Salt
open Push.BetaTransport Reef
variable(P:BudgetPoint)(R:PathData SU.group){q:Clip}{σ C Λ:ℝ}(p:R.Bounds q σ C Λ)(A Γ:ℝ)(D': DayT P.order Γ)(DA: OriK P.order A)(hc:0≤Γ)(ha:0≤ A)(hw:Decent q P)(hp:Geo.Width P q σ)(hn:60 <(More n).val)
local notation "Rd"=> (P.supportExponent+1+1)
variable (T:Ids n)(hv:1 ≤ h)(hL:(P.supportExponent+1+1)/(P.B:ℝ)≤σ/8)(h6:6 ≤ P.B)(r: Rare R) (E: RegBudget n)(sL:ℕ)(p0:IncX Utrue E P h x)
local notation "T'"=> caw P sL E
local notation "T0"=>can_V P sL E
local notation "u'"=> lureC (realH T')
local notation "ER"=> Coil T' + lite_b n P R q u'+ lit_P n P R q u'
local notation "Ω"=>voids T'- ΘK T P R q u'
local notation "γ"=> rate_μ P q σ C Γ u'
local notation "uL"=>belt_K P sL Γ*x+ γ
local notation "Rb"=> rate_b P q σ C A u'
local notation "Rh"=> rate_h P q σ C A u'
local notation "ε"=>fee_l P Γ*x+Rb+Rh
-- Auth log pressure.Theorem bend Φ all.X poles.AMB. full A=abs.Bl.No losses. verify.Lane.
local notation "Eh"=> (T0+writ_E ER)
local notation "dQ"=> (writ_K Ω)
local notation "Ts"=> Sweep n
local notation "Up"=> (uL+tray_H P.order * uL)
open Iva Lilt

include p DA ha hw hp hn hv
lemma brol_exterior : head_L (brol P R q sL E)=head_L E:=by
 let Tη:= caw P sL (cry_H E); let Qb:=can_V P sL (cry_H E); let d:=lureC (realH Tη)
 have ht: Silent Tη:=by funext i V; change cut_V (Tη i V) =0; unfold Tη caw; split; exact sass (poolZ E) _ _; exact map_zero _
 have hq: Silent Qb:=by funext i V; change cut_V (Qb i V)=0; unfold Qb can_V; split; exact map_zero _; exact sass (poolZ E) _ _
 let Op:= Qb+writ_E (Coil Tη+lite_b n P R q d+lit_P n P R q d); have hA: Silent Op:= sail_g _ _ hq (light_F _ (sail_g _ _ (sail_g _ _ (sail_F0 Tη ht) (thirst P R p A d DA ha hw hp hn hv sL).2.2.1) (crown_V P R p A d DA ha hw hp hn hv sL).2.2.1))
 have hd(A B : RegBudget n): head_L (A+B)=head_L A+head_L B:= by funext i z; exact map_add cut_V _ _
 change head_L (Op+ head_L E)=_; rw [hd, show head_L Op=0 from hA, zero_add]
 have hs:=congrArg head_L (bareH E)
 rw [hd, show head_L (cry_H E)=0 from poolZ E, zero_add] at hs; exact hs
end YM.CF.Beau
end
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.flexible false
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

open Taxi RG.PathData Next.Scheduling UVNext.PricedKernels Work.F03 WilsonStartup
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset Vow Rue
namespace Test
set_option quotPrecheck false
open Cycle929 Larch Bake Salt
variable {n:Side}{L:ℕ}{Q:BudgetPoint}{A h a c d:ℝ}
local notation "D'"=> RegBudget n
local notation "H"=> Scree.Hub n
local notation "Γ_"=> (H→H)
lemma fixed_long_writ (f:D') (K:ℕ) (t:∀ i:Scree.Hub n,K<coverNumber Q.B i.val.2 → f i=0)(i:Scree.Hub n)(h:K<coverNumber Q.B i.val.2) : (writ_E f) i=0:=by
 funext x; unfold writ_E; simp only [Pi.smul_apply, Finset.sum_apply]; change plight_C n • (∑ j:Sweep n,suit_Y j⁻¹ _) = (0:Cipher n); rw [sum_eq_zero,smul_zero]; intro j _; rw [t (moveHub j i) (by rw [show coverNumber Q.B (moveHub j i).val.2= _ from glow_q j Q.B i.val.2]; exact h)]; exact map_zero _
end Test
end YM.CF.Py.Rate
end
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
local notation "θA"=> s.pA
local notation "dmP" Z:max=> shiftM p Z R.L xm K.j s.s.k
local notation "lmap'"=> TestW.lmap s.A0.dream
lemma hood_long (Z:RegBudget ι)(i:Scree.Hub ι)(hi:mstar R.L.val + 1 < coverNumber p.B i.val.2) : (head_L (s.hood Z)) i=0 := by
 let F:= lmap' (dmP Z)
 let E:= s.shape.expands (P:=p) R.L.val|>.choose_spec
 have t:Silent rp := light_F (warp_E Vr (creditR p θL λS ι)) (scalar_warp ((creditTune s.S0 s.Ty (dr).floor).2.2.1)) -- namespace search
 let f : RegBudget ι := shaveL p F
 have hx(j:Scree.Hub ι)(hj:1< coverNumber p.B j.val.2): f j=0:= if_neg (fun (v:j∈massH p) => (not_le.mpr hj) (mem_filter.mp v).2)
 have hT(j:Scree.Hub ι)(hj:mstar R.L.val + 1< coverNumber p.B j.val.2): (warp_E Vr f) j=0:=by
    unfold warp_E Larch.sunY; refine sum_eq_zero (fun k v=>?_) ; have hp: Vr k=j:=(mem_filter.mp v).2; rw [←hp] at hj
    have e:Extension ℓ p _ Vr:= E
    by_cases z: shortHub p ℓ k
    · rw [e.cap _ z] at hj; omega
    rw [e.held k z] at hj; exact hx k (by omega)
 have ha : NetX Vr p F i=0:=by
    change f i-(writ_E (warp_E Vr f)) i=0
    rw [hx i (by omega), fixed_long_writ _ _ (Q:=p) hT i hi,sub_zero]
 funext V
 change cut_V ((NetX Vr p F i) V+ θA Z • rp i V)=0; rw [ha,map_add,map_smul]; rw [sass t i V]; rw [smul_zero]; change cut_V 0 + 0= (0:Cipher _); rw [map_zero,add_zero]

lemma RepE_long (b:ℂ)(F:FL)(i:Scree.Hub ι)(hi:mstar R.L.val + 1 < coverNumber p.B i.val.2) : head_L (s.RepE b F).1 i=head_L (EkX (s.standby b F) b F).1 i:= by
 let Z:= (s.pF b F).1
 let E:= (EkX (s.standby b F) b F).1
 have hz : head_L Z=head_L E:= brol_exterior p _ s.S0.mass s.Aχ s.S0.day s.S0.ha s.S0.decent s.S0.span s.S0.n0 (dr).floor E ℓ
 funext V; change cut_V (Z i V+s.hood Z i V)=_; rw [map_add]; change head_L Z i V + head_L (s.hood Z) i V = _; rw [hood_long s Z i hi,hz]; exact add_zero _
end Shop
end Focus
end Pitching
end YM.CF.Py.Rate
#print axioms YM.CF.Py.Rate.Pitching.Focus.Shop.RepE_long
