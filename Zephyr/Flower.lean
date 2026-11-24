import YM.CF.Vp929.Pre.Azure
import Zephyr.Cash
import Zephyr.Conveyor
/-!
`tapped` revenue at raised rate; we recalculate the fee with half the FeeBook scale so as to make independent of audit tightness.
-/
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

open Zephyr
namespace FeeBook
variable {bl:ℕ}{γ:ℝ}
variable (v:FeeBook bl γ 1)
include v
lemma half_rate : degreePrice bl (γ/2) 1 < 1/2:= by
 have hv := v.rate
 unfold degreePrice Trees.stretch at hv ⊢
 linarith

lemma bill2 : FeeBook bl (γ/2) 1:=
  ⟨half_pos v.coal,zero_lt_one,(half_rate v).trans (by norm_num),
    mul_nonneg (by norm_num) (stretch_pos _ (half_pos v.coal) zero_lt_one).le⟩

lemma shelf : γ ≤ 1:= by
 have hv:=v.rate
 unfold degreePrice Trees.stretch at hv
 rw [div_one] at hv
 linarith [le_mul_of_one_le_left v.coal.le (show (1:ℝ) ≤ _ from Nat.one_le_cast.mpr (Push.AbsoluteSums.Animals.neighbors_ge bl))]

lemma tab2 : ticket_f bl (γ/2) 1 ≤ 1:= by
 have h : 0 < 1 - degreePrice bl (γ/2) 1:=by linarith [half_rate v]
 unfold ticket_f
 rw [←div_eq_mul_inv,div_le_iff₀ h,one_mul]
 linarith [half_rate v, shelf v]
end FeeBook

open Nor
def flower (b:ℕ) := wren_K 6 2 + reserveT 2 6 b 1 * (2+2:ℝ)
namespace Pitching
local notation "G5"=> SU.group
local notation "S'"=> w.step V
local notation "ι" => Scree.mid m B
local notation "η" => Scree.mid n B
local notation "z'" => (coming D.Z 105 5*radiusB x)
variable {o : Pitching w D x}
local notation "Bs" v:max F:max => base (q:=q) (J:=J) (w:=w) p' v F
local notation "Ys" β:max F:max=> Pitching.input (V:=V) (w:=w) p' β F
local notation "Xs" β:max => Pitching.start (V:=V) (w:=w) p β
local notation "A'"=> o.muster
local notation "P'"=> D.pilot
local notation "Up" v:max=> (tint_z o.muster v)
local notation "Jq"=> (w.Φ (V:=V))
local notation "F₁"=> Folk S' z' (Words S')
local notation "V_"=> Troupe S' z' (Words S')
local notation "Xo" => Hos S' z'

open Lich Iva
variable {F:Corr (Scree.mid n B)}
variable {Pν: ↥(Sil (w.step V) (coming D.Z 105 5*radiusB x))}{N0:ℕ}
local notation "Δ"=> (o.muster.post+90)*radiusB x
local notation "Ξ"=> (o.muster.loft+o.muster.post+200)*radiusB x
local notation "D'"=> Dwell ι
local notation "Xp"=> (stake (n:=LeanV (Tulip.Single (Scree.mid m B))) h)
local notation "FX"=> F₁→Raid (Dwell (Scree.mid m B))
open Engine Engine.Basin Engine.Docket Dialect
local notation "T_"=> Troupe S' z' (Words S')
local notation "Lo"=> Palot.leaf (Site (Domain m B))
local notation "De"=> T_→ Lo→ Raid D'
local notation "PZ"=> T_→Lo→ Orbit ι→ Cipher ι
local notation "oWell"=> o.muster
local notation "Loχ"=> Palot.leaf (Site (Domain m B))
local notation "Px"=> V_→Loχ→ Orbit ι→ Cipher ι
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
variable (Q:β∈ Year R x)(hF:Charged p' w.input K.j R.L.val h f F)
local notation "Ys'"=> Ys β F
local notation "Υ'"=> Xs β
local notation "F_"=> (Z.toLid.crew β Q).1
local notation "A0"=> (Z.toLid.choice Q (gross_shape hF (le_refl f)))
variable {Lz:Troupe (w.step V) (coming D.Z 105 5*radiusB x) (Words (w.step V))→ Aura (Scree.mid m B)→ Orbit (Scree.mid m B)→Cipher (Scree.mid m B)}{Cp:Troupe (w.step V) (coming D.Z 105 5*radiusB x) (Words (w.step V))→ Aura (Scree.mid m B)→ Raid (Scree.Dwell (Scree.mid m B))}
open Lilt Wray
local notation "UP"=> (Cash.prominence p)
local notation "Fq"=> ticket_f
local notation "vP"=> value_ R x κ
variable {γ a b tα:ℝ}

variable (hk:Fair p R x κ γ σ)
include hk
lemma Fair.near : value_ R x κ ≤ 1:= by
 have h : 1 ≤ Vow.chi_f 6 := by norm_num [Vow.chi_f, composeCost, Nat.factorial]
 linarith [le_mul_of_one_le_left hk.beam h, hk.book.shelf, hk.gain]
variable (hp:Spirit p o Lz Ty)(gx: Harvest p h κ 1 Lz Cp)
include Uq hp gx
lemma subsistence : Cash.poise (slipP p Lz) ∧ MonoQ p h UP (slipP p Lz) 2 := by
  let e := hp.livelihood Uq Ty hk gx zero_le_one (by norm_num)
  refine ⟨e.1,?_⟩
  obtain ⟨hf,_,he⟩:=Young Uq hp.seed gx
  have hr := hk.audit Uq zero_le_one (by norm_num : (1:ℝ) ≤ 100)
  let fr:= hk.usable Uq
  exact ((fr.bill2.fee (hk.ps Uq) D.high (hf.purse hr)).sub (he.fade (le_add_of_nonneg_right zero_le_one) (zero_le_one.trans D.high))).purse (by
    linarith [fr.tab2,fr.shelf])

lemma tapHigh : IncX Utrue (tapped p o Ty Lz) (plusP p) h (flower p.B) := by
  obtain ⟨uP,tP⟩:= subsistence Uq Ty hk hp gx
  let Q:=Cash.priceRPlus D.high Ty tP uP
  let H:=pertains_plus Uq Ty hp.seed gx hp
  have hw : wren_K p.order p.power * (1 * value_ R x κ) ≤ wren_K p.order p.power :=
    mul_le_of_le_one_right (by unfold wren_K; linarith only [lucre p.order p.power])
      ((one_mul _).trans_le hk.near)
  unfold flower
  rw [←Z.request.boot.power]
  conv in wren_K 6 _ => rw [←Z.request.boot.order]
  rw [show reserveT p.power 6 = reserveT p.power p.order from by rw [Z.request.boot.order]]
  exact Ione.addT _ (Fixed.Voltage.upgradeI _ _ H hw) Q.1
#print axioms tapHigh
end Focus
end Pitching
end YM.CF.Py.Rate
