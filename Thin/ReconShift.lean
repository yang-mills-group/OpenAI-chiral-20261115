import Thin.KnotShift
import YM.CF.Neon.Stock
import YM.CF.Vp929.Pre.Conveyor
import YM.CF.Neon.Glass
import YM.CF.Muse.Pack
import YM.CF.Vp929.Pre.Currency
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 250000
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
local notation "G5"=> SU.group
local notation "S'"=> w.step V
local notation "ι" => Scree.mid m B
local notation "η" => Scree.mid n B
local notation "z'" => (coming D.Z 105 5*radiusB x)
variable {o : Pitching w D x}
local notation "Ys" β:max F:max=> Pitching.input (V:=V) (w:=w) p' β F
local notation "XL" β:max => Pitching.start (V:=V) (w:=w) p β
local notation "A'"=> o.muster
local notation "P'"=> D.pilot
local notation "Up" v:max=> (tint_z o.muster v)
local notation "Jq"=> (w.Φ (V:=V))
local notation "V_"=> Troupe S' z' (Words S')
local notation "Xo" => Hos S' z'

open Lich Iva
variable {F:Corr (Scree.mid n B)}
variable {Pν: ↥(Sil (w.step V) (coming D.Z 105 5*radiusB x))}{N0:ℕ}
local notation "Δ"=> (o.muster.post+90)*radiusB x
local notation "Ξ"=> (o.muster.loft+o.muster.post+200)*radiusB x
local notation "D'"=> Dwell ι
local notation "Xp"=> (stake (n:=LeanV (Tulip.Single (Scree.mid m B))) h)
open Engine Engine.Basin Engine.Docket Dialect
local notation "T_"=> Troupe S' z' (Words S')
local notation "Lo"=> Palot.leaf (Site (Domain m B))
local notation "De"=> T_→ Lo→ Raid D'
local notation "PZ"=> T_→Lo→ Copy ι
local notation "oWell"=> o.muster
local notation "Loχ"=> Palot.leaf (Site (Domain m B))
local notation "Px"=> V_→Loχ→ Copy ι
local notation "Kx"=> V_→ Loχ→ Raid (Scree.Dwell ι)
open Vow Bake Salt Stax Sour Larch
local notation "Θ'" t:max=> (cook S' (Finset.toLeft t)).flags
local notation "δ_"=> (cipherK J.n)
local notation "U_"=> (fullD (n:=ι))
variable {t bL σ κ Bv:ℝ}{nₐ:ℕ}{pW:WindV K.j 2}
variable {Z:Cellar N0 o p p' c f ag Cg} {M:Climate D.pilot R c x t bL σ κ ag Cg Bv nₐ}
namespace Focus
variable (Uq:Focus Z M pW ff)(Ty:Ids (Scree.mid m B))
local notation "Upp"=> ((tolQ p).supportExponent)
variable (i:Roc (Scree.mid n B))(O:Aura (Scree.mid m B))
local notation "Gμ"=> (subtK (r:=z') S')
local notation "ks"=> (rope_i (H:=oWell))
local notation "keep_"=> (keep_A (H:=oWell))

local notation "RΛ"=> Roc η
local notation "UΛ"=> RΛ×Lo
variable {tα:ℝ}
local notation "Υq"=> value_ R x κ
local notation "U_ν"=> (tα*Υq)
-- Unperturbed fends, Ht': tint has same H.post


local notation "host" i:max=> hostX (l:=Δ) S' i
local notation "seat" i:max=> (S').ratio.parent (i:RΛ).1.val.1


local notation "VM"=> XL β
local notation "Vω"=> Ys β F
local notation "Oτ"=> (o.tinted β)

include Uq Ty
lemma liftedRecon {Lz Lu:Px}{V':De}(pL:Seed p (Lz-Lu))(u:Harvest p h κ tα (Lz-Lu) V') (fΩ fH f'' :ℝ)(Xω:RΛ→Pane ι→Ride S'→FC D')(κ':RΛ→ℝ)
    (P0:KnotX (Xs:=VM) (Y:=Vω) (Oτ) Ty h f'' κ' (fun i=>Lu (Gμ i)) Xω fΩ fH)
    (blank : ∀ (i:RΛ)(j:Lo),¬ (host i).val⊆j.val → Lz (Gμ i) j=0):
    KnotX (Xs:=VM) (Y:=Vω) (Oτ) Ty h f'' κ' (fun i=>Lz (Gμ i)) Xω fΩ (fH+tα*Υq) :=by
 obtain ⟨B₁,B₂,a,hA,hB⟩:= P0.yield
 let W0(i:RΛ)(j:Lo):ℝ:=∑ k:Finset D',Scree.tariff p ((S').ratio.parent i.1.val.1) h k*V' (Gμ i) j k
 let W0e (i:RΛ)(j:Lo):= B₂ i j+W0 i j
 have he(v:Seat ι): (∑ i:RΛ with seat i=v,∑ j:Lo with (host i).val⊆ j.val,p.mass j.val (W0 i j))≤tα*Υq:= sum_increases Uq pL u v
 refine ⟨B₁,W0e,fun i=>?_ ,fun v=> ?_,fun v=>?_ ⟩ -- might need nested
 · let t:= (a i)
   refine ⟨fun j=>?_ ,t.tumor⟩
   obtain ⟨xP,Hp,hl⟩:=t.sustain j -- shadows x
   refine ⟨xP,fun px=>?_ ,fun px y=> ?_⟩
   · let Hp':= Hp px; let Ux:= tonK Oτ i j px
     have he:= lit_money Uq Ty i j pL u Ux rfl
     have ha:Ux.val.1=seat i:=rfl
     have hx:= prop_add p Ux Hp' he
     have hz:∀ (V₁ V₂ wr: Pane ι→ Cipher ι), (fun u=>V₂ u-wr u)+(fun u=>V₁ u-V₂ u)=(fun u=>V₁ u-wr u):=by intro tK tJ tQ; funext i; change tJ i - tQ i + (tK i - tJ i) = _; abel
     let Y₁:=fun y:Pane ι=> Lz (Gμ i) j (y,Ty); let Y₂:=fun y:Pane ι=> Lu (Gμ i) j (y,Ty)
     change PressB p _ ((fun v=> Y₂ v- (wrap_B _ _ xP v))+(fun v=>Y₁ v-Y₂ v)) h _ at hx
     rw [hz] at hx
     apply Hope.hi_p hx
     change B₁ i j + B₂ i j + W0 i j≤ B₁ i j + (B₂ i j+W0 i j)
     rw [add_assoc]
   exact ⟨congrFun (blank i j px) (y,Ty), (hl px y).2⟩
 · have hx:= he v
   have hh:= add_le_add (hA v) hx
   change (∑ i:RΛ with seat i=v,∑ j:Lo with (host i).val⊆ j.val,p.mass j.val (W0e i j))≤_
   unfold W0e BudgetPoint.mass; simp_rw [mul_add,sum_add_distrib]; exact hh
 have hh:= add_le_add (hB v) (he v)
 change (∑ i:RΛ with seat i=v, ∑ j:Lo with (host i).val⊆ j.val,p.mass j.val (B₁ i j+W0e i j))≤_
 unfold W0e; simp_rw [←add_assoc (B₁ _ _),BudgetPoint.mass,mul_add,sum_add_distrib]
 unfold BudgetPoint.mass at hh; simp_rw [mul_add,sum_add_distrib] at hh
 rw [← add_assoc]; exact hh
end Focus
end Pitching
end YM.CF.Py.Rate
