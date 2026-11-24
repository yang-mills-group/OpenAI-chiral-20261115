import YM.CF.Vp929.Pre.Extras
import YM.CF.Vp929.Pre.Conveyor
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

/-- Sweeping regular corrections doesn't spread to different cover numbers. -/
lemma writStops {Y:RegBudget m} (k r:ℕ)
    (t:∀ i:Scree.Hub m,k < coverNumber r i.val.2 → Y i=0) :
    ∀ i:Scree.Hub m,k < coverNumber r i.val.2 → writ_E Y i=0:=by
 intro i u
 unfold writ_E
 rw [Pi.smul_apply,Finset.sum_apply]
 suffices hx : ∀ j, base_Q j Y i=0 by simp_rw [hx]; simp
 intro s
 have eq : coverNumber r (moveHub s i).val.2 = coverNumber r i.val.2 := glow_q s r _
 funext V
 show suit_Y s⁻¹ (Y (moveHub s i) (flashA s V)) = 0
 rw [t _ (eq ▸ u),Pi.zero_apply,map_zero]

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
variable (Q:β∈ Year R x)(hF:Charged p' w.input K.j R.L.val h ff F)
local notation "Ys'"=> Ys β F
local notation "Υ'"=> Xs β
local notation "F_"=> (Z.toLid.crew β Q).1

variable {Lz:Troupe (w.step V) (coming D.Z 105 5*radiusB x) (Words (w.step V))→ Aura (Scree.mid m B)→ Orbit (Scree.mid m B)→Cipher (Scree.mid m B)}{Cp:Troupe (w.step V) (coming D.Z 105 5*radiusB x) (Words (w.step V))→ Aura (Scree.mid m B)→ Raid (Scree.Dwell (Scree.mid m B))}
namespace Lunar
open Prism Vow
variable (Vq:Rill.Arch w.G d)
local notation "A₂"=> Scree.Hub η → Cipher η
local notation "LΛ"=> Youth m n B→ InkD ι
local notation "RΛ"=> Roc η
local notation "Ξm"=> Youth m n B
local notation "ξ"=> seedling (p:=p) (p':=p') o Vq
local notation "S0"=> sun (p:=p) (p':=p') Vq o
local notation "RP"=> rope_i (H:=oWell)
local notation "Xi0"=> keep_A (H:=oWell)
private abbrev solar (F:LΛ) := sunY (RP) Xi0 (fun p:(Roc (Scree.mid n B)× Aura (Scree.mid m B))=> ∑ i:Ξm with i.1=p.1 ∧ i.2.1=p.2,F i)
private abbrev sunrise (F:LΛ) := sunY univ (EpR (N:=mid m B) x) (fun t=> ∑ i:Ξm with lift_I i=t,F i)

local notation "Sv"=> S0 (pennies F.1)
local notation "Gt"=> glasp (H:=Up β) (X:=Xs β) (Y:=Ys β F) V o.SheepR D.D Vq C' D.X D.jp
local notation "Lt"=> forge_P (H:=Up β) (X:=Xs β) (Y:=Ys β F) V o.SheepR D.D Vq C' D.X D.jp

abbrev brickDate : ℕ :=(305+305+1)^4

private lemma boundDawn (G:LΛ)(hb:1≤radiusB x)(i:Scree.Hub ι)
    (e:brickDate < coverNumber (radiusB x) i.val.2): sunrise (x:=x) G i=0:=by
  apply sum_eq_zero;intro j t
  have ht:= (mem_filter.mp t).2
  have hv : coverNumber (radiusB x) (EpR x j).val.2 ≤ brickDate :=
    (yard_m x j.2.1 hb).trans (by norm_num [reach_T,brickDate])
  rw [ht] at hv
  exact (e.not_ge hv).elim

private lemma gleam (y:Ξm) (g:y∉Lt) : Sv y=0:=by
  funext V'
  apply Subtype.ext
  change cars_P _ _ _ (ξ (pennies F.1) y)=0
  rw [←birth (p:=p) (p':=p') (β:=β) Vq]
  have ht:Gt y=0:=Classical.byContradiction fun e=> g (mem_filter.mpr ⟨mem_univ _,e⟩)
  rw [ht,thaw_v]

include Uq Q hF
private lemma forgeValley (y:Ξm)(g:y∈Lt):
    y.2.1.val ⊆ Lattice.halo (305*radiusB x) {(S').ratio.parent y.1.1.val.1} := by
  let e:= Uq.press_f hF
  let T0:=Uq.layout.full β Q F e
  obtain ⟨Qx,Qv,Fq⟩:= Pig.sail_t (H₀:=Ys β F) (H₁:=Xs β) V (M_:=o.SheepR)
  exact subset_union_left.trans
    (till_q V D.pilot D.Z T0.statv o.SheepR F_ D.D Vq Qx Qv Fq C' D.X D.jp y g)

private lemma boundSun (hb:1≤radiusB x)(i:Scree.Hub ι)
    (e:brickDate < coverNumber (radiusB x) i.val.2): solar (o:=o) Sv i=0:=by
  refine sum_eq_zero (fun j t=>sum_eq_zero (fun y v=>?_))
  by_cases g:y∈Lt; swap; · exact gleam Vq y g
  have hv:= (Corona.cover_mono (forgeValley Uq Q hF Vq y g) (radiusB x)).trans
    (Corona.tile _ 305 _ (show 0 < radiusB x from hb))
  have ht:y.2.1.val=i.val.2:=by
    rw [(mem_filter.mp v).2.2,←(mem_filter.mp t).2]
    exact (keep_h _).symm
  rw [ht] at hv
  exact (e.not_ge hv).elim

lemma capRadix (i:Scree.Hub ι)
    (e:brickDate < coverNumber p.B i.val.2):
    radixLin (p:=p) (p':=p') (o:=o) Vq (pennies F.1) i=0:=by
   have he : p.B=radiusB x:= Z.request.boot.B
   have hb := he ▸ p.B_pos
   apply writStops brickDate p.B _ i e
   intro j ej
   change sunrise (x:=x) Sv j - solar (o:=o) Sv j=0
   rw [boundDawn Sv hb j (he ▸ ej),boundSun Uq Q hF Vq hb j (he ▸ ej)]
   exact sub_self _
#print axioms capRadix
end Lunar
end Focus
end Pitching
end YM.CF.Py.Rate
