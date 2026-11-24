import GaugeFieldConstruction.DustJ
import GaugeFieldConstruction.CannonJ
import GaugeFieldConstruction.EraJ
import GaugeFieldConstruction.SambaJ
import GaugeFieldConstruction.OromoJ
import GaugeFieldConstruction.FrijaJ
import GaugeFieldConstruction.Gloss
import GaugeFieldConstruction.QuishJ
import GaugeFieldConstruction.NorasJ
import GaugeFieldConstruction.TributoJ
import GaugeFieldConstruction.AmusaJ
import GaugeFieldConstruction.SpursJ5
import GaugeFieldConstruction.Frosts
import GaugeFieldConstruction.Legends
import GaugeFieldConstruction.Frosts
import GaugeFieldConstruction.Swirls
import GaugeFieldConstruction.Infar
import GaugeFieldConstruction.Moll
import GaugeFieldConstruction.Panther
import GaugeFieldConstruction.Kenko
import GaugeFieldConstruction.HopeQ
import GaugeFieldConstruction.Overland
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 290000
set_option maxRecDepth 4000
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
open Eire Girt
open VolumeRate
namespace Pitching
open Lich Iva
open Engine Engine.Basin Engine.Docket Dialect
open Vow Bake Salt Stax Sour Larch
namespace Focus
open Appel.Rate Stockpile
section
open Sour.MatchW Sour.MatchW.Technique Cycle929 Tap Lilt
open Next.Fluctuations.Sector
open Neon
open QuadClock Haro
open Mew Vow Rive Bake
open scoped YM.CF.Mew
open Riant
open YM.CF.Oath.BellPrice PinRack
open TableF TableF.Boom Lenten Layout Fren
section
open Mew Roots Connect Ing Ing.Iona CoeffArc Frugal
variable {I O A Y:Type}[Fintype I][LinearOrder I][Fintype O][LinearOrder O][DecidableEq A][Fintype A][DecidableEq Y][Fintype Y]
variable {L: Side}{K:Teller SU.group}{R:Patch}{N m n B:Side}{d vH x:ℝ}
variable {c:ChartRatio SU.group}
open Directory
namespace Onwards
open Larch Roots.GJ Ing Ing.Iona
variable {m B:Side}(Nkey:ℕ)(C:ℝ) {p:BudgetPoint}(σ:I→Seat N)(A:Finset I)
variable (w:I→I) (v:∀ i∈A,σ (w i)=σ i) (q:Set.InjOn w (A:Set I)) (s: ∀ i∈A,w i∉ A)
open Ione QuadClock TableF.Lenten.Bank Riant
section
variable (P:BudgetPoint)(M:Male)(T:Seat N)(H Z:RegBudget N)(L:Side)(k:ℕ)(X:Waves)(r u f e:ℝ) (t:TollsK P T M H L r u f k X)(t':TollsK P T M Z L r u e k X)
-- subtract same wave budgets. Orientation.Control
include t
lemma ArcMore (h:0≤r)(w:f ≤ e): TollsK P T M H L r u e k X:=by obtain ⟨⟨K,v⟩,t,h'⟩:=t; exact ⟨⟨K,ArenaC.moveup v (mul_le_mul_of_nonneg_right w h)⟩,t,h'⟩
include t'
lemma ArcDrop (h:0≤u): TollsK P T M (H-Z) L r u (f+e) k 0:=by
 obtain ⟨K,hP⟩:=t.funds; obtain ⟨A,hQ⟩:=t'.funds; let Lk:ℂ:= -1; let PZ:= Arena_κ Lk hQ; have he: H-Z= H+Lk • Z:=by unfold Lk; rw[neg_one_smul,sub_eq_add_neg]
 rw[he]; refine ⟨⟨K+‖Lk‖ • A, ArenaC.moveup (ArenaC.rates_plus hP PZ) (by rw [show ‖Lk‖=1 from (by unfold Lk; simp),one_mul,add_mul])⟩,fun i v=>?_,?_⟩
 · have hk:=t.control i v; have hx:=t'.control i v
   refine ⟨?_,fun j=>?_⟩
   · rw [Pi.add_apply,Layout.life_add,Pi.smul_apply, life_smul,Pi.add_apply,Pi.smul_apply,hk.1,hx.1]; simp -- tune
   rw [show (H+Lk • Z) i= H i+(Lk • Z) i from rfl,SeT_add h (hP.fits i) (PZ.fits i),show (Lk • Z) i= _ from (show (Lk • Z) i = Lk • (Z i) from rfl),BeaconΚ M Lk (hQ.fits i) h,MSlot_k,ΓWave,hk.2 j,hx.2 j]; simp only [Troot_z Packs_U Lk]; exact @add_zero Waves kinnG.toAddCommGroup.toAddMonoid.toAddZeroClass _
 · let W:=Zhub T; change MSlot _ (SealT W (H W+(Lk • Z) W) _ _ _)=_
   rw [SeT_add h (hP.fits W) (PZ.fits W),show (Lk • Z) W= _ from (show (Lk • Z) W=Lk • Z W from rfl),BeaconΚ M _ (hQ.fits W) h,MSlot_k, ΓWave,show MSlot k (SealT W (H W) (KeyUp P) u M)= _ from t.cen,show MSlot k (SealT W (Z W) (KeyUp P) u M)= _ from t'.cen]; exact (show ∀ {E:Type}(T:TPack E),letI:=T.G; letI:=T.S;∀ (i:ℂ)(x:E), i • x+(-1:ℂ) • (i • x)= i • 0 from fun {_} T=>by letI:=T.G;letI:=T.S; simp ) Packs_U _ X
end
section
variable {B:Type}[DecidableEq B]
variable (D:Directory I B)(y:B→Seat N)
structure Troop :Prop where
    τneg(i)(p:i∈ A):D.kind i=false
    τpos(i)(p:i∈A): D.kind (w i)=true
    same(i)(p:i∈A): D.own (w i)=D.own i
    owned(i)(p:i∈ A)(j)(q:j∈A)(h:w i=w j): i=j
variable (hqR:Troop A w D)
include hqR
lemma Troop_ij : Set.InjOn w (A:Set I):=fun i p j q h=>hqR.owned i p j q h
lemma Troop_no (i)(p:i∈A): w i∉ A :=fun t=>Bool.noConfusion ((hqR.τpos _ p).symm.trans (hqR.τneg _ t))
lemma Troop_out {i:I}(p:D.kind i=true): i∉A:=fun t=>Bool.noConfusion (p.symm.trans (hqR.τneg _ t))
local notation "ΤF"=> D.F_v y
lemma Troop_w(i)(p:i∈A): ΤF (w i)=ΤF i:= congrArg y (hqR.same _ p)
-- Tolls on born stamps (consuming $𝜏$)
def P_tier (H:D.TourF)(i:I)(p:i∈A): Waves:= H (D.own i) ⟨w i,hqR.same _ p,hqR.τpos _ p⟩
abbrev scribe (F Q:Finset I →RegBudget N):= Verdante ΤF (reflux A w) (CrushJ A F+Q)

variable (P:BudgetPoint)(M:Male) (F Q:Finset I→ RegBudget N)(h u e a:ℝ)(L:Side)(V':D.TourF)(Vp:D.QSign P M y (fun i=>F {i}) L h e a V')
variable (vk:∀ i:I,i∉A → Q {i}=0)
include vk
lemma Costζ (i:I)(p:i∉ A):scribe A w D y F Q {i}=F {i}:=by
 funext j t; unfold scribe; rw [vappy]; change Verdante ΤF (reflux A w) (fun i=> (CrushJ A F+Q) i j) {i} t= _; rw [vappy, crafted ΤF A w _ i p]; change CrushJ A F {i} j t+ Q {i} j t=_; rw [Crush_out _ _ p,vk i p]; exact add_zero _
lemma Costα (i:I)(p:i∈A):scribe A w D y F Q {i}=Q {i}-F {w i}:=by
 have hp:=Troop_no A w D hqR i p
 funext j t; unfold scribe; rw [vappy]; change Verdante ΤF (reflux A w) (fun i=> (CrushJ A F+Q) i j) {i} t= _; rw [vappy,Crafted ΤF A w (Troop_w A w D y hqR) _ i p]; change (CrushJ A F {i} j t+Q {i} j t)-(CrushJ A F {w i} j t+Q {w i} j t)=Q {i} j t-F {w i} j t; rw[Crush_in _ _ p,Crush_out _ _ hp,vk _ hp]; simp only [Pi.zero_apply,zero_add,add_zero]
include hqR vk Vp
-- head payload `scribe` $$ P_Weights.
lemma Quiz_m (q:0≤ h)(hQ:0≤a)(v:0≤e)(χ:∀ i:I,∀ t:i∈ A,TollsK P (ΤF i) M (Q {i}) L a h e (D.depth (D.own i)) (P_tier A w D hqR V' i t)) : D.QSign P M y (fun i=>scribe A w D y F Q {i}) L h (2*e) a V' :=by
 intro x; refine ⟨fun i=>?_, fun i=>?_⟩
 · have z:i.val∉A:=Troop_out A w D hqR i.property.2; dsimp only; rw [Costζ _ _ _ _ hqR F Q vk _ z]; exact ArcMore _ _ _ _ _ _ _ _ _ _ _ ((Vp x).1 i) hQ (by linarith)
 dsimp only; by_cases z:i.val∈A; swap; · rw [Costζ _ _ _ _ hqR F Q vk _ z]; exact ArcMore _ _ _ _ _ _ _ _ _ _ _ ((Vp x).2 i) hQ (by linarith)
 rw [Costα _ _ _ _ hqR F Q vk _ z]; obtain ⟨i,pF,dF⟩:= i; change i∈A at z; subst x; rw [show 2*e=e+e from two_mul _]; exact ArcDrop _ _ _ _ _ _ _ _ _ _ _ _ (χ _ z) ((Vp (D.own i)).1 ⟨w i,hqR.same _ z, hqR.τpos _ z⟩) q -- rw rewrites subtype i? dependent rewrite before.Meta
#print axioms Quiz_m
end
end Onwards
end
end
end Focus
end Pitching
end YM.CF.Py.Rate
end
