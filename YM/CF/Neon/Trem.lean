import YM.CF.Neon.Twang
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Neon
open Py
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
variable {d e η t_aux z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade
-- certify.WAGES off all granted tasks
variable {uG Hh pK qK a γ vS dS kL w:ℝ}{r p i:ℕ}{X: GramM (mid N B)}{Y: GramM (mid P B)}{U:Grasp V.U B d}
open Oath Feu Feu.Corset Haro Nor Siete PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Moto
open Vow Lilt Larch Bake Rue
open Prism Hove Oise
-- primary picture: rank 0 pressure (global scalar extracted separately), 3 PH weight and 4 derivatives, 4 radial. representation.H.
local notation "Yκ"=> mid P B
local notation "Xκ"=> mid N B
local notation "Ωp"=> RegBudget (mid P B)
local notation "θp"=> (Y.p)
local notation "HF"=> Scree.Hub (mid P B)
local notation "Пρ"=> S.patch.L.val
local notation "Pr"=> Roc (mid P B)
open Taxi Hope
variable (o: Site (mid P B))(E1:RegBudget (mid P B))(OG:RegBudget (mid P B))(X0:Dome)(Aζ:Skate)(Q:ℝ)(h:ℝ)
local notation "Δo"=> Cube.node o
open Mew
-- process real gauge Yearn to K normalization. rooted support wave. Cost short C.P broad Vv post.Sector. 
variable (F:Pilot)(Z:Pluck R){H:Muster G S x d T}{W:GivenX V U}{q q':Chi}
local notation "ζμ"=> radiusB x
open Coal
open Tap
-- triangular chart. scales included Φ from native temp gauges, credit.D linear tag.Need separate derivative y & x shape for leading inertia.
variable (u':Op (Single (mid P B)))(P0: Dome)(w_:ℂ)(a_ d' d0:ℝ)
local notation "Tκ"=> (node o)
local notation "EΨ"=> (w_ • P0)
variable (pY:jetsL o u'= w_ • P0)
abbrev δK0 :ℝ:= ∑ b:Bool, ∑ i:Axis, ‖Hove.ditF b i‖
private lemma sum_delta(b:Bool)(i:Axis): ‖ditF b i‖ ≤δK0:= (single_le_sum (fun i (_:i∈ (univ:Finset Axis))=>norm_nonneg _) (mem_univ _)).trans (single_le_sum (fun b (_:b∈(univ:Finset Bool))=> sum_nonneg (fun j _=>norm_nonneg _)) (mem_univ _))
local notation "Υ"=> (‖w_‖*‖P0.1‖)
local notation "ζθ"=> (‖w_‖ *‖P0.2‖+ δK0 *(‖w_‖*‖P0.1‖))
lemma δtop(b:Bool):0≤δK0:= (norm_nonneg _).trans (sum_delta b 0)
include pY
lemma fawn_e : ‖Hove.mornC o u'‖= Υ ∧∀ a:Axis, ‖partX o u' a‖≤ ζθ ∧ ‖partY o u' a‖≤ ζθ:=by
 have hv: mornC o u'= w_ • P0.1:=congrArg Prod.fst pY
 refine ⟨by rw [hv,norm_smul],fun a=>?_⟩
 have hz: ‖(w_ • P0).2‖= ‖w_‖*‖P0.2‖:= norm_smul ..; have ht:domF o u'=lendP (w_ • P0):=(dawn_u ..).trans (congrArg _ pY); let T:= (w_ • P0)
 have hp: partX o u' a=T.2.1 a+(ditF false a)ᴴ*T.1:=congrArg (fun z:Dome=> z.2.1 a) ht; have hr: partY o u' a=T.2.2 a+T.1*ditF true a:=congrArg (fun z:Dome=> z.2.2 a) ht; have hf: ‖T.1‖= Υ:= norm_smul ..
 rw [hp,hr]; have hk:‖(ditF false a)ᴴ‖=‖ditF false a‖:= norm_star _
 constructor
 · exact (norm_add_le ..).trans (add_le_add (((norm_le_pi_norm _ a).trans ((le_max_left ‖T.2.1‖ ‖T.2.2‖))).trans_eq hz) ((norm_mul_le ..).trans (mul_le_mul (hk.trans_le (sum_delta ..)) hf.le (norm_nonneg _) (δtop true))))
 exact (norm_add_le ..).trans (add_le_add (((norm_le_pi_norm _ a).trans ((le_max_right ‖T.2.1‖ ‖T.2.2‖))).trans_eq hz) ((norm_mul_le ..).trans ((mul_le_mul hf.le (sum_delta ..) (norm_nonneg _) ((norm_nonneg _).trans_eq hf)).trans_eq (mul_comm ..)))) -- lambda names tune
variable (o': Site (mid N B))(Qp:Op (Single (mid N B)))(z u:ℂ)
local notation "PΨ"=> jetsL o' Qp
local notation "И"=> (Hove.domF o u')
variable (hxP: ‖Hove.mornC o' Qp-z • Hove.mornC o u'‖≤d)(htP:∀ a:Axis, ‖partX o' Qp a- u • culm (partX o u' a)‖≤d'∧ ‖partY o' Qp a- u • culm (partY o u' a)‖≤d')
include hxP htP
lemma pall_V : ‖(PΨ).1-z • (w_ • P0.1)‖≤ d ∧ ‖(PΨ).2-u • (w_ • P0.2)‖ ≤ pruneQ*d':=by
 let T:=jetsL o u'; have ht:T=EΨ:=pY; have hv':0 ≤ pruneQ:=by unfold pruneQ; positivity
 have hh:0 ≤ pruneQ*d':= mul_nonneg hv' ((norm_nonneg _).trans (htP 0).1)
 have h1 : ‖(PΨ).2-u • T.2‖ ≤ pruneQ*d':=by
    have hk(a b:Tap.Pal)(p:‖a-u • Hove.culm b‖≤ d') : ‖culm a -u • (culm b)‖≤ pruneQ*d':=by
       have hv: culm (a-u •culm b)=culm a-u • (culm (culm b)):=by change coneL (_- _)=_; rw [map_sub,map_smul]; rfl
       rw [cul_p b] at hv; rw [←hv]; exact (pruned _).trans (mul_le_mul_of_nonneg_left p hv')
    rw [Prod.norm_def]; exact max_le ((pi_norm_le_iff_of_nonneg hh).mpr (fun a=> hk _ _ (htP a).1)) ((pi_norm_le_iff_of_nonneg hh).mpr fun a=> hk _ _ (htP a).2)
 exact ⟨by rw [← show T.1 = w_ • P0.1 from congrArg Prod.fst ht]; exact hxP, show ‖(PΨ).2- u • _‖ ≤_ from (show T.2= w_ • P0.2 from congrArg Prod.snd ht) ▸ h1⟩
end YM.CF.Neon
