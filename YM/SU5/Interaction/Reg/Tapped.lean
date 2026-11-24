import YM.CF.Vp929.Pre.Azure
import YM.SU5.Interaction.Reg.High

/-! XXI Pre/Conveyor and Pre/Azure at exponent+1. -/
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
variable (i:Roc (Scree.mid n B))(O:Aura (Scree.mid m B))
local notation "Gμ"=> (subtK (r:=z') S')
local notation "ks"=> (rope_i (H:=oWell))
local notation "keep_"=> (keep_A (H:=oWell))

local notation "RΛ"=> Roc η
local notation "UΛ"=> RΛ×Lo
variable {tα:ℝ}
local notation "Υq"=> value_ R x κ
local notation "U_ν"=> (tα*Υq)
variable (pL:Seed p Lz)(u:Harvest p h κ tα Lz Cp)(hp:Spirit p o Lz Ty)
private lemma preFar: Θ' (Gμ i)=∅:= by change (penn S' (Gμ i)).flags=∅; rw [Feu.penn_p,Feu.kflags]
local notation "Tδ" x:max Xy:max O:max=> (∑ j:Finset D',Scree.tariff p x h j * Cp Xy O j)
include o
private lemma sitesChosen (i: (Roc (Scree.mid n B) × Aura (Scree.mid m B))) : (keep_ i).val.1 ∈ i.2.val := by
 rw [← keep_h (o:=o) i]; exact (keep_ i).prop
include Uq pL u

lemma placementRate (xo: Seat (Scree.mid m B)):
   (∑ i∈ ks with (keep_ i).val.1=xo, (ups p).mass (keep_ i).val.2 (Tδ (keep_ i).val.1 (Gμ i.1) i.2)) ≤ U_ν := by

 let f(i:RΛ)(j:Lo):=Tδ ((keep_ (i,j)).val.1) (Gμ i) j; let Vg(j:V_)(t:Lo):=(tolQ p).mass t.val (Tδ (chooseXC (o:=o) j t) j t); let H:= Uq.value_ch u (chooseXC (o:=o)) (chooseXC_cross Uq) xo; apply le_trans _ H
 let W₁:= Finset.univ.image ((subtK (r:=z') S'): RΛ→Troupe _ _ _)
 refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg (t:=Finset.univ) (subset_univ W₁) ?_); swap
 · exact fun i _ _=> sum_nonneg (fun j _=> mul_nonneg (Real.exp_pos _).le (Uq.value_pos i j u _))
 unfold rope_i; rw [sum_filter,sum_filter,Fintype.sum_prod_type,sum_image]; swap; · exact fun _ _ _ _ h=> injectX h
 apply sum_le_sum; intro i _; rw [sum_filter]; apply sum_le_sum; intro j _; change (if (hostX (l:=Δ) S' i).val ⊆ j.val then if (keep_ (i,j)).val.1=xo then (ups p).mass (keep_ (i,j)).val.2 (f i j) else 0 else 0) ≤ if xo∈j.val then Vg (Gμ i) j else 0
 by_cases q: (hostX (l:=Δ) S' i).val ⊆ j.val
 · rw [if_pos q]; by_cases k: (keep_ (i,j)).val.1=xo
   · rw [if_pos k,if_pos (show xo∈j.val from k ▸ (sitesChosen (o:=o) (i,j)))]; rw [keep_h]; unfold Vg; unfold f; rw [agreesXC Uq]; apply mul_le_mul_of_nonneg_right _ (Uq.value_pos _ _ u _); apply Real.exp_monotone; change (p.supportExponent+1) * _ ≤ (p.supportExponent+1+1+1)*_; exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
   rw [if_neg k]; split; exact mul_nonneg (Real.exp_pos _).le (Uq.value_pos _ _ u _); exact le_rfl
 rw [if_neg q]; split; exact mul_nonneg (Real.exp_pos _).le (Uq.value_pos _ _ u _); exact le_rfl
include hp
lemma pertainsHigh : DuesQ Utrue (ups p) h (writ_E (Placement o Ty Lz)) (wren_K p.order p.power*U_ν):= by
 apply cup_R (ups p) (Placement o Ty Lz) _ hp.numb (zero_le_one.trans D.high)
 apply feat_v ks keep_ (fun i (V:Pane _)=> Lz (Gμ i.1) i.2 (V,Ty)) (fun i=> Tδ ((keep_ i).val.1) (Gμ i.1) i.2) (ups p) U_ν
 · intro i _; apply upsPress; exact Trefoil.mint Uq Ty (Gμ i.1) i.2 (pL.spruce _ _ (by rw [preFar]; exact empty_subset _)) u _ (preFar _) (keep_h i)
 intro x; exact placementRate Uq pL u x
end Focus
end Pitching
end YM.CF.Py.Rate

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
variable (hk:Fair p R x κ γ σ) (hp:Spirit p o Lz Ty)(gx: Harvest p h κ tα Lz Cp)
local notation "Ψt"=> tapped p o Ty Lz
variable (hT:0≤tα)(bt:tα≤100)
local notation "φ"=> ticket_f (radiusB x) γ 1
local notation "λa" u:max=> (ticket_f (radiusB x) γ 1 + burnQ R x κ u)
include Uq hk hp gx hT bt
lemma Spirit.localHigh : DuesQ Utrue (ups p) h (Ψt) (coinW R x κ tα (φ+burnQ R x κ tα)) ∧ Packed p h UP (Cash.owe Ty (slipP p Lz)) (φ+burnQ R x κ tα):=by
 obtain ⟨uP,tP⟩:= hp.livelihood Uq Ty hk gx hT bt; let Q:=Cash.priceRunHigh D.high Ty tP uP
 let H:=pertainsHigh Uq Ty hp.seed gx hp; unfold coinW; conv in wren_K _ _ => rw [← Z.request.boot.order,←Z.request.boot.power]
 rw [show reserveT 2 6 (radiusB x) 1=reserveT p.power p.order p.B 1 from by rw [Z.request.boot.order,Z.request.boot.power,Z.request.boot.B]]; exact ⟨Ione.addT (ups p) H Q.1,Q.2⟩

end Focus
end Pitching
end YM.CF.Py.Rate
