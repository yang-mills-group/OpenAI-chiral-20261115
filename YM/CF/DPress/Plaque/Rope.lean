import YM.CF.DPress.Plaque.Payment
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Quadratic
import YM.CF.Taxi.Fine
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.DPress.Plaque
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open AnalyticBridge.VerifiedReset
attribute [local instance] Gauge.frobInner
variable {n:Side}{r:ℕ}(P:BudgetPoint){a k:ℕ}
local notation "K"=>SU.group
open Next.Foundations
lemma diff(o:Site n)(U:Config K n): ContDiff ℝ ⊤ (feeW o ∘ increment U):=by
 let Y:= K; let T: Y.Mat →L[ℝ] ℝ:= Complex.reCLM.comp (Matrix.traceLinearMap (Fin Y.repDim) ℝ ℂ).toContinuousLinearMap
 change ContDiff ℝ ⊤ (fun q=> (4:ℝ)⁻¹*(∑ i∈Rings o, (1-T (Y.mat (faceValue (increment U q) i))/(Y.repDim:ℝ))))
 exact contDiff_const.mul (ContDiff.sum (fun i _=> contDiff_const.sub ((T.contDiff.comp (WilsonStartup.mat_face_inc i U)).div_const _))) -- mathlib lemma?
lemma grants(o:Site n): P.Regular (haloW o) (feeW o):=by
 have he(U:Config K n): ContDiffAt ℝ (P.order:ℕ∞) (feeW o ∘ increment U) 0:= (((diff o U).of_le le_top).contDiffAt) -- tune
 exact ⟨sits o,(contFee o).measurable,fun k x=> gaugeW o x k,fun U _=> he _,fun i _ u l m=> left_has u m (he _)⟩
variable (k:ℕ)(T:Side)
abbrev qualify(n:Side)(k:ℕ):Prop:=20*(k+10)< n.val
variable {o:Site n}(u:Site n) (V:AnalyticBridge.VerifiedReset.LinearJet SU.group)
local notation "line'"=> AnalyticBridge.VerifiedReset.line
variable {k}(hn:qualify n k)(v:separation u o≤ k)
abbrev αϲ := ∑ i:PlaqAxes,‖V.positive i‖^2
include hn v
lemma venue (x:Site n)(h:separation u x≤ 2): 10*separation x o < n.val:=by
 have hu:= separation_comm u x; have ht:= separation_triangle x u o; unfold qualify at hn; omega
lemma limit_var : Tendsto (fun t:ℝ=> feeW u (line' (V.field o) t)/t^2) (𝓝[≠] 0) (𝓝 ((∑ i:PlaqAxes,‖V.positive i‖^2)/2)):=by
 let U':= V.field o; let F(i:Face (Per n))(t:ℝ):= (K).price (faceValue (line' U' t) i)/t^2; let L(i:PlaqAxes):= ‖V.positive i‖^2/2
 have hf(i)(p:i∈Rings u):Tendsto (F i) (𝓝[≠] 0) (𝓝 (L i.2)):=by
    have h:= venue u hn v i.1 (WilsonStartup.visit_near i ((mem_filter.mp p).2)); let q:= square i.2.val.1 i.2.val.2; have hp:4≤n.val:=by unfold qualify at hn; omega
    have hh(V:LinearJet K): Exterior.linkSum (V.field o) i.1 q = V.positive i.2:=by rw [AnalyticBridge.VerifiedReset.Square.cochain_square,V.field_step h hp,V.field_step h hp]; simp [LinearJet.positive,LinearJet.curl, sub_eq_add_neg]
    unfold F L; rw [←hh]; exact Work.F03.price_limit (G:=K) (V:=fun t=>faceValue (line' U' t) i) (by simp [WilsonStartup.face_one]) (AnalyticBridge.VerifiedReset.Square.word_deriv i.1 q U')
 have hL: (∑ i∈Rings u,L i.2)=(4:ℝ)*(∑ i:PlaqAxes,‖V.positive i‖^2/2):=by
    rw [ringSum u (fun x=>L x.2),mul_sum]; apply sum_congr rfl; intro i _; have hp: 2≤n.val:=by unfold qualify at hn; omega
    change ∑ x∈Bases u i,L i=_; rw [sum_const,paycheck u i hp,nsmul_eq_mul]; norm_num [L]
 have h:= tendsto_finsetSum (Rings u) hf; rw [hL] at h; simp_rw [feeW, mul_div_assoc,Finset.sum_div]; let H(i:PlaqAxes):= ‖V.positive i‖^2/2; rw [show ∑ i:PlaqAxes,H i= (4:ℝ)⁻¹*(4*(∑ i:PlaqAxes,H i)) by ring]; exact (Tendsto.const_mul (4:ℝ)⁻¹ h)
include P in
lemma hessian : logHessian (feeW u) (V.field o) (V.field o)= ∑ i:PlaqAxes,‖V.positive i‖^2:=by have h:= tendsto_nhds_unique (hessian_limit Thera.yet_one (grants P u) (fee_one u) (V.field o)) (limit_var u V hn v); linarith
end YM.CF.DPress.Plaque
