import Mathlib.Probability.Distributions.Gaussian.Fernique
import YM.CF.Wray.Seats
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Wray
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
variable {d e η t z g b c A B':ℝ} {j k k' m n l:ℕ}
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
open Iva Eire ProbabilityTheory
local notation "CB"=>SU.group.Color
local notation "Yb"=> Sat S
local notation "Z"=> Appel.feast
open scoped ENNReal NNReal
-- one fee.measure across all caps & fields. smallest h≥1.
lemma sapI:∃ a C:ℝ,0<a∧1 ≤ C∧∀ v:ℝ,1≤v→let F(x:SU.group.Color):=Real.exp (a*‖x‖^2); Integrable F (Appel.feast G5 v)∧(∫ i,F i ∂Appel.feast G5 v)≤ C:=by
 let μ:= rice SU.group; haveI:IsGaussian μ:=inferInstanceAs (IsGaussian (stdGaussian CB)); obtain ⟨a,h,p⟩:= IsGaussian.exists_integrable_exp_sq μ; let F(x:CB):=Real.exp (a*‖x‖^2); let I(A: Measure CB):= ∫ i,F i ∂A; let Q(v:ℝ):= grainS SU.group v; let F':=I μ*(Q 1).toReal⁻¹
 refine ⟨a,max 1 F',h,le_max_left ..,?_⟩; intro v g F0; have ht:=grain_pos SU.group (zero_lt_one.trans_le g); have hc:(Q v)≠⊤:=measure_ne_top _ _; refine ⟨p.restrict.smul_measure (ENNReal.inv_ne_top.mpr ht.ne'),?_⟩
 let A:=μ.restrict (closedBall 0 v); have hh:= integral_mono_measure (μ:=A) (ν:=μ) Measure.restrict_le_self (Eventually.of_forall fun i=>show 0≤ F i from (Real.exp_pos _).le) p
 have hx:0 ≤ I μ:=integral_nonneg (fun i=> (Real.exp_pos _).le)
 have hp:(Q v).toReal⁻¹ ≤ (Q 1).toReal⁻¹:= inv_anti₀ (ENNReal.toReal_pos (grain_pos SU.group zero_lt_one).ne' (measure_ne_top _ _)) (ENNReal.toReal_mono hc (measure_mono (Metric.closedBall_subset_closedBall g)))
 apply le_trans _ (le_max_right 1 F'); unfold Appel.feast; rw [integral_smul_measure,smul_eq_mul,ENNReal.toReal_inv,mul_comm]; exact (mul_le_mul_of_nonneg_right hh (inv_nonneg.mpr ENNReal.toReal_nonneg)).trans (mul_le_mul_of_nonneg_left hp hx)
-- multi-meter proof truthful event saturation
variable {a C:ℝ}{L:Finset (Sat S)}
def palmB (n:ℕ)(b:ℝ)(V: Finset (Sat S))(y: Directions SU.group (Domain P B)):Prop:= ∀ i ∈ V,Bravo n i y b
def rainL(N:ℕ)(b:ℝ)(V:Finset (Sat S))(x:Directions SU.group (Domain P B)):ℝ:= if palmB N b V x then 1 else 0
lemma plumX(b:ℝ)(L:Finset (Sat S)): IsOpen {x:Directions SU.group (Domain P B)| palmB n b L x}:=by
 have h(i:Sat S): IsOpen {x:Directions SU.group (Domain P B)| Bravo n i x b}:=by
    let F:=vision n i; rw [show {x:Directions SU.group (Domain P B) | Bravo n i x b}= ⋃ j:F,{x | b < ‖x j.val‖} from by ext; simp [Bravo,F,vision]]; apply isOpen_iUnion; intro j; exact isOpen_lt continuous_const (by fun_prop)
 rw [show {x:Directions SU.group (Domain P B)| palmB n b L x}= ⋂ i:L,{x|Bravo n i.val x b} from by ext; simp [palmB]]; exact isOpen_iInter_of_finite fun i=>h i.val -- tune
abbrev bloom(t:ℝ)(N:ℕ)(v:ℝ)(a C:ℝ)(P:Patch) := (Real.exp (-a*v^2/spanI P N) * C^(Fintype.card Axis * P.L.val^4*(N+3+(N+3)+1)^4)) -- t phantom
local notation "CB1"=> Bond (Domain P B)
variable (F0:ℝ)(p:1 ≤ F0)(h:0 < a)(hp:1 ≤ C)(zzZ: let F(x:SU.group.Color):=Real.exp (a*‖x‖^2); Integrable F (Appel.feast G5 F0)∧(∫ i,F i ∂Appel.feast G5 F0)≤ C)
include p h hp zzZ
lemma torrents (b:ℝ)(r:0 ≤ b)(L: Finset (Sat S)): let μ:= Appel.tableG G5 CB1 F0; Integrable (rainL n b L) μ ∧(∫ i, rainL n b L i ∂μ) ≤ bloom b n b a C S.patch ^L.card:=by
 intro μ; haveI:= feast_nn SU.group (zero_lt_one.trans_le p); letI: IsProbabilityMeasure μ:= how SU.group (zero_lt_one.trans_le p); let F(u:CB):= Real.exp (a*‖u‖^2); let U:=L.biUnion (vision n); let Q(i:CB1):CB→ℝ:= if i∈ U then F else 1; have hp'(i:CB1): Integrable (Q i) (Z G5 F0):= by unfold Q; split; exact zzZ.1; exact integrable_const _
 let f:(Directions SU.group (Domain P B))→ ℝ:=fun x=>∏ i:CB1, Q i (x i); let Ψ:= rainL n b L; let c:=spanI S.patch n; have hc:0 < (c: ℝ):= Nat.cast_pos.mpr (by unfold c spanI; omega)
 let W:= Real.exp (-a*b^2/c * L.card); have hx:Integrable f μ:= Integrable.fintype_prod hp'; have hv: (∫ i,f i ∂μ)=(∫ x,F x ∂Z G5 F0)^U.card:=by
    change (∫ (x:CB1→CB), (∏ j:CB1, Q j (x j)) ∂Measure.pi (fun _=> Z G5 F0))=_; rw [integral_fintype_prod_eq_prod,←prod_subset (subset_univ U)]; swap; · intro i t u; simp [Q,u]
    rw [show (∏ i∈U,∫ j,Q i j ∂ Z G5 F0)=∏ i∈U,(∫ x,F x ∂Z G5 F0) from prod_congr rfl fun i g=>by unfold Q; rw [if_pos g]]; simp
 let C':= C^ratioB S (n+3); have hz: U.card ≤ L.card*ratioB S (n+3):= card_biUnion_le.trans ((sum_le_sum fun i _=> puff_v (S:=S) n i).trans_eq (by simp))
 have hH(x:Directions SU.group (Domain P B)): f x= Real.exp (a*∑ i∈U,‖x i‖^2):=by
    unfold f; rw [← Finset.prod_subset (subset_univ U), mul_sum, Real.exp_sum]; swap; · intro i _ g; unfold Q; rw [if_neg g,Pi.one_apply]
    exact prod_congr rfl fun i w=> by unfold Q; rw [if_pos w]
 have ho: Integrable Ψ μ:=by rw [show Ψ= Set.indicator {x|palmB n b L x} (fun _=> (1:ℝ)) from rfl]; exact (integrable_const _).indicator ((plumX b L).measurableSet)
 refine ⟨ho,?_⟩; apply le_trans (integral_mono ho (hx.const_mul W) ?_); swap
 · intro i; change (if _ then _ else _) ≤ W*f i; rw [hH]; split
   next hu=> unfold W; rw [←Real.exp_add]; apply Real.one_le_exp; let V:= pulseS r hu; have hc': b^2*L.card ≤ c* ∑ j∈U, ‖i j‖^2:= V; apply nonneg_of_mul_nonneg_left (a:=(-a*b^2/(c:ℝ)*↑L.card+a*∑ j∈U,‖i j‖^2)) ?_ hc; -- tune right form
             field_simp; nlinarith only [mul_le_mul_of_nonneg_left hc' h.le]
   exact mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
 rw [integral_const_mul]; change W* (∫ x,f x ∂μ)≤ _; rw [hv]
 apply (mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ (integral_nonneg (fun x=>(Real.exp_pos _).le)) zzZ.2 U.card).trans (pow_le_pow_right₀ hp hz)) (Real.exp_pos _).le).trans_eq; rw [bloom,mul_pow,← Real.exp_nat_mul]; rw [mul_comm L.card, pow_mul]; congr 2; first |ring|rfl -- tune
end YM.CF.Wray
