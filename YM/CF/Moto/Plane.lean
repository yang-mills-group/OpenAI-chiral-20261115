import YM.CF.Tune.Shine
import YM.CF.Moto.Lean
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Moto
open Nor
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
variable {d e η tW z g b c AW B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Wray Prism Font
open Eire.Dress Yaw PetalP Feu Feu.Corset Haro
variable {r K0:ℕ}{ι:Type}[Fintype ι][DecidableEq ι]{f c:Type}[Fintype f][LinearOrder f][Fintype c][LinearOrder c]
local notation "κ"=> (Scree.mid P B)
local notation "Kx"=> (Scree.mid N B)
local notation "hT"=> (LeanV f)
local notation "Zx"=> LeanV c
local notation "BF"=> (Eire.Ride S)
local notation "Fm"=> (LeanV (Single κ))
local notation "CM"=> LeanV (Single Kx)
open Hove Oath
local notation "QΦ"=> Rock Kx
open Hove Haro Taxi
local notation "θn"=> (mid N B)
variable (U: InkD (mid N B)) (Φ:Scree.Hub (mid N B)) (o:Site (mid N B))(t:Φ.val.1=node o)(P₀:BudgetPoint)(hx:PressB P₀ Φ U v z) (w:1≤v)
variable (A:ℝ)(ht:DayT P₀.order A)(uA:0≤A)
local notation "KP"=> Φrap (mid N B) o 10
local notation "Hq"=> (KP)
local notation "TP"=> plateZ (node o) P₀ (tooth (Φ.val.1) P₀ U)
abbrev crest_G(P: BudgetPoint)(o:Site (mid N B))(X:InkD (mid N B)) := plateZ (node o) P (Moto.tooth (node o) P X)
def crest_Y(o:Site (mid N B))(X:InkD (mid N B)):= (pay_Y (N:=N) (B:=B) (spring_V (jetsL o (orbitPH (X 1))) o))
local notation "TU"=> crest_G P₀ o U
local notation "TΦ"=> crest_Y o U
local notation "QΨ"=> (jetsL o (orbitPH (U 1)))
variable (GG:Oath.Gala P₀.power P₀.order 100 x 3)(hz:1 ≤ radiusB x)(hv: P₀.threshold=temp x)(hK:20 < (More (mid N B)).val)(hk:3 ≤ (mid N B).val)(pK:1 ≤ P₀.power)
local notation "Vcφ"=> deck_K P₀.order P₀.power 10
abbrev peka_H(k:ℕ):= 1+Hove.κP k+ Hove.pruneQ *Hove.κP k
abbrev tera_ρ (P:BudgetPoint)(x:ℝ):= deck_K P.order P.power 10*(Oath.stakeH P.order * chipZ P.power (peka_H P.power*(2*x)))
include hx w pK t
lemma κprice {d:ℝ}(p:Hove.paid_M o (orbitPH (U 1)) P₀.power*v^2 ≤ d): v^2 * ‖QΨ‖≤ peka_H P₀.power*d:=by
 let Q:= QΨ; let V':=orbitPH (U 1); let J:=paid_M o V' P₀.power
 let A:= peka_H P₀.power; let C:= Hove.κP P₀.power
 have hz:0≤C:=by unfold C Hove.κP ξP; have hp:=mpe true; have hx:=mpe false; positivity
 have hu:0 ≤ pruneQ:=by unfold pruneQ; positivity
 have hc: C≤ A:=by unfold A peka_H; change C≤1+C+pruneQ*C; linarith [mul_nonneg hu hz]
 have hh: pruneQ*C ≤ A:=by unfold A peka_H; linarith only [show 0≤κP P₀.power from hz]
 have h : ‖Q‖ ≤ A*J:=by
    have hp:0≤ J:=paidp_p ..; have h1:0≤ A*J:=mul_nonneg (hz.trans hc) hp
    have hx0:=ζr o V' P₀.power; rw [Prod.norm_def]; apply max_le; refine hx0.trans (mul_le_mul_of_nonneg_right hc hp)
    rw [Prod.norm_def]; refine max_le ((pi_norm_le_iff_of_nonneg h1).mpr fun b=>?_) ((pi_norm_le_iff_of_nonneg h1).mpr fun b=>?_)
    · exact (pruned _).trans ((mul_le_mul_of_nonneg_left (opox o V' P₀.power b pK) hu).trans (le_trans (mul_assoc _ _ _).symm.le (mul_le_mul_of_nonneg_right hh hp)))
    exact (pruned _).trans ((mul_le_mul_of_nonneg_left (opoy o V' P₀.power b pK) hu).trans (le_trans (mul_assoc _ _ _).symm.le (mul_le_mul_of_nonneg_right hh hp)))
 change v^2*‖Q‖≤_; rw [mul_comm]; exact (mul_le_mul_of_nonneg_right h (sq_nonneg _)).trans ((mul_assoc ..).le.trans (mul_le_mul_of_nonneg_left p (hz.trans hc))) -- tune
include GG hv hz
lemma wheel_Y : PressB P₀ KP TΦ v (tera_ρ P₀ z):=by
 let F:= QΨ; let W:=spring_V F o; let C:= Vcφ; let Z:=P₀.power
 have hP:= pose_K W o P₀ 1 _ (beam_l o _ F (leg_K _ _ (worth_Φ Φ U hx))) 100 GG (by omega) 10 (by omega) hz hv rfl v
 obtain ⟨k,g,hr,t'⟩:= hx.worth
 have hu:=pinM o Φ U k g t (ortho_l Φ U k (hr _) ) (zero_le_one.trans w) z t'
 have hv:= κprice U Φ o t P₀ hx w pK hu
 refine Hope.hi_p (F:=pay_Y W) hP ?_; unfold tera_ρ; let J:= Oath.stakeH P₀.order; change C*(J*v^2*chipZ Z ‖F‖) ≤ C*(J*chipZ Z _)
 have hc:0≤ C:= by unfold C deck_K composeCost; positivity
 have ht:0 ≤ J:=by unfold J stakeH flavor γD; have he:= Haro.p0; have h:= wheels_p (n:=P₀.order); positivity
 refine mul_le_mul_of_nonneg_left ?_ hc; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ ht; refine le_trans ?_ (show chipZ Z (v^2*‖F‖)≤ _ from ?_)
 · exact (le_of_eq (by unfold chipZ chal; ring))
 unfold chipZ chal; gcongr
section
include ht uA t hk hK
lemma wallet : let E:=U-(TU+TΦ); PressB P₀ KP TU v (trotΦ P₀ z A) ∧ (∀ U:Pane θn, lifeH TΦ U=0) ∧ (lifeH TU 1=0) ∧ tooth (node o) P₀ TU= tooth (node o) P₀ U ∧ Hove.jetsL o (Haro.orbitPH (TΦ 1))=QΨ:=by
 intro E; let F:=tooth (node o) P₀ U; have hv:∀ i j,‖F i j‖≤z:=by unfold F; rw [←t]; exact dia _ _ _ hx (zero_le_one.trans w)
 have h0: Lattice.halo 2 {node o} ⊆ (KP).val.2:=Corona.halo_mono (by norm_num) (Subset.refl _)
 have hk':Verc F:=by unfold F; rw [←t]; exact ploy _ _ _ hx (zero_le_one.trans w)
 have he:= suit_l P₀ F KP (zero_le_one.trans w) ht uA h0 hv hK hk'; refine ⟨champ P₀ F KP ht uA h0 hv, fun x=>?_,he.1,he.2,?_⟩
 · exact bail_m _ _
 unfold crest_Y; rw [hail_K, fief_Ψ _ _ (true_P ..) hk]
end
end YM.CF.Moto
