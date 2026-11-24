import YM.CF.Sere.Uinta
import YM.CF.Hype.Quiet
import YM.CF.Sere.Cogn
import YM.CF.Hype.Rome
import YM.CF.Hype.Flash
import YM.CF.Hype.Mora
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
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
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
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
variable {u Hh pK qK a γ vS dS kL w:ℝ}{r p i:ℕ}{X: GramM (mid N B)}{Y: GramM (mid P B)}{U:Grasp V.U B d}
open Oath Feu Feu.Corset Haro Nor Siete PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Prism Haro Tap Oath
open Larch
-- decays compared with all plow^•
open Ione Lilt Larch Beau
local notation "gL"=>R.L
variable {F F' Gk H_:ℝ→ℝ}
lemma rise_Χ (R:Patch)(p k:ℕ)(d S' Yh:ℝ→ℝ)(A a c0 uV hQ H w:ℝ)(h:1≤H)(t:0<uV)(pd:sizeK R.L 2 d)(ps:Litt R 2 S')(py:Litt R 2 Yh): let Z:=beam_U p k R d S' Yh A a c0 uV hQ H w
          sizeK R.L 2 Z∧∃ E:ℝ→ℝ,Litt R 2 E∧∀ᶠ x:ℝ in atTop,0 ≤ d x → Z x ≤ ray_T p k A a hQ (1/(R.L.val:ℝ)*d x)+E x:=by
 intro Z; let L':ℝ:=1/R.L.val; let M(x):=pace_Z R (A*gritY R.L.val) (d x) (S' x); let B(x):=|way_Q R k p x (d x) c0 uV hQ H|
 let g(x):= reserveT p k (radiusB x) 1*(3*Yh x); have hg:Litt R 2 g:=SupportP.beam_v (Nor.vale_u ..) (py.scale_l _) -- tune prep
 have he:sizeK R.L 2 M:= (pd.scale _).accrue ps.height_r
 let D₀:= (|φnom k p hQ|+1)*(R.L.val:ℝ)⁻¹; have hv0: ∀ᶠ x in atTop, ∀ z:ℝ,0≤z→ |way_Q R k p x z c0 uV hQ H| ≤ D₀*z:= ample_η R k p hQ c0 uV H h t
 have hv: ∀ᶠ x:ℝ in atTop, |B x| ≤ |D₀*d x|:=hv0.mono fun x v=>by
    unfold B; rw [abs_abs]; have he: 0≤D₀:=by unfold D₀; positivity
    rw [abs_mul D₀, abs_of_nonneg he]; let Λ(z):= way_Q R k p x z c0 uV hQ H
    have hh:|Λ (d x)|=|Λ (|d x|)|:=by by_cases p':0≤d x; rw [abs_of_nonneg p']; rw [abs_of_neg (lt_of_not_ge p'),show Λ (-d x)=-Λ (d x) from (by unfold Λ way_Q; ring), abs_neg]; -- parser
    exact hh.trans_le (v |d x| (abs_nonneg _))
 have hV:sizeK R.L 2 B:= (pd.scale _).cost_d hv
 let W:= wren_K k p; refine ⟨sizeK.accrue ((he.accrue (hV.scale _)).scale _) hg.height_r,fun x=>W*S' x+g x,(Litt.scale_l ps W).add_e hg,?_⟩
 have hw:0 ≤ W:=by unfold W wren_K; exact add_nonneg zero_le_one (lucre ..)
 have hc:0 ≤ rise_K k p a:=by unfold rise_K mark_Q composeCost; positivity
 filter_upwards [hv0] with x p' v
 change W*(M x+rise_K k p a* B x)+ g x≤_; exact ((add_le_add_left (mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left (p' _ v) hc) _) hw) _)).trans_eq (by unfold ray_T M pace_Z gritY W D₀ g; field_simp; ring)
end YM.CF.Py
