import YM.CF.DPress.Plaque.Jet
import YM.CF.DPress.Axis.Shape
import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Weigh
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Py.Kay
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
open Oath Feu Feu.Corset Ione Nor Haro Beau Siete PhysicalNext.JointLoad.Heir Vow
open AnalyticBridge.VerifiedReset
open DPress DPress.Fees Finance Rosy
open scoped YM.CF.Mew
open DPress.Plaque Taxi
namespace WagesC
variable {n:Side}{k:ℕ}(P:BudgetPoint){a b h:ℝ}
abbrev Point (n:Side) := Site (More n)
-- Δ recipe gauge site notation for LP2
structure Wings (k:ℕ) (p:BudgetPoint) (a:ℝ) (n:Side) :Prop where
 width : k+6 ≤ p.B
 pos : 0 ≤ a
 pay : DayT p.order a
 hn : Plaque.qualify (More n) k
abbrev hup(v:Point n): Scree.Hub n :=⟨(v,haloW v),siteW_ v⟩
abbrev κov(v o:Point n): Scree.Hub n:= ⟨(v,haloW v∪haloW o),mem_union_left _ (siteW_ v)⟩
abbrev τ₀(v:Point n): Aura n:= pur (hup v)
abbrev υκ(v o:Point n): Aura n:= pur (κov v o)
variable (w:Wings k P a n)
abbrev fund(v:Point n):InkD n:=fun i=>moldV n (feeW v i)
-- shape cheap (B-ball)
include w
lemma wraps(v o:Point n)(p:separation v o≤k) : coverNumber P.B (υκ v o).val ≤1:=by
 apply (Corona.cover_mono _ P.B).trans (AnalyticBridge.CouplingShape.ballPaid _ v); apply union_subset; · exact Corona.halo_mono (by have h:=w.width; omega :2≤P.B) (Subset.refl _)
 intro i v0; obtain ⟨j,h,s⟩:= halo_spec.mp v0; rw [mem_singleton.mp h] at s; have h:=w.width; exact halo_spec.mpr ⟨v, mem_singleton_self _,((separation_triangle v o i).trans (by omega))⟩
lemma covers(v:Point n):coverNumber P.B (haloW v) ≤1:= (Corona.cover_mono (show _ ⊆ (υκ v v).val from subset_union_left) P.B).trans (wraps P w v v (by rw [separation_self]; omega))
-- pressing one per support parity. docs copy Taxi/Talk
omit w
private lemma dustK(X0:Scree.Hub n)(L: Pane n→ℂ)(p:LocalOn X0.val.2 L)(s:GaugeInvariant L)(q:Measurable L)(x:ℝ)(ht:0 ≤x)(u:∀ U,pingS P.threshold X0.val.2 U→ Signs P X0.val.1 (L ∘ increment U) x): PressB P X0 (fun (U:Pane n)=> (hollow (L U) : Cipher n)) h x:=by
 refine ⟨fun i j w=> congrArg _ (p i j w),fun _=> Flour.grainE.smul _,?_,fun i j=>?_,Pi.single ∅ x,fun i=>?_,fun U u' i=>?_,?_⟩ -- tune
 · let K:ℂ→Cipher n:=fun i=> hollow i; exact (Continuous.measurable (f:=K) (Continuous.subtype_mk (continuous_id.smul continuous_const) _)).comp q
 · rw [s]; exact Subtype.ext (Eq.symm ((twist_scalar _ _ _).trans (by rw [map_one]; rfl)))
 · rw [Pi.single_apply]; split_ifs; exact ht; exact le_rfl
 · by_cases j:i=∅; · subst i; rw [Pi.single_eq_same]; apply Prism.mint (u _ u'); exact Eventually.of_forall (fun j=> (hullB _).symm) -- tune .Pane Hess
   rw [Pi.single_eq_of_ne j]; refine Prism.mint (Prism.hail (v:=(0:ℝ)) (show ‖(0:ℂ)‖≤0 by rw [norm_zero])) ?_; exact Eventually.of_forall fun k=>by change (0:ℂ)= ((L _) • (1:FC (LeanV (Single n)))) i ∅; simp [j]
 simp [Pi.single_apply,Scree.tariff,endL,mul_ite] -- simp recursion.
include w
abbrev grade(P:BudgetPoint)(k:ℕ)(a:ℝ):ℝ:= ‖Complex.ofRealCLM‖* Plaque.BillQ P k a
lemma budgetPump(o:Point n)(X:Scree.Hub n)(t:haloW o⊆X.val.2)(v:separation o X.val.1 ≤ k): PressB P X (fund o) h (grade P k a * P.threshold^2):=by
 let e:= feeW o; let F := haloW o; let R:ℝ→L[ℝ]ℂ:= Complex.ofRealCLM; let Y:= (R ∘ e); let A(i):= (fun p:pingS P.threshold X.val.2 i=> fiscal P o i w.pay w.pos p (t (siteW_ o)) v w.hn); let Z:=grade P k a * P.threshold^2; have hK(i)(p:pingS P.threshold X.val.2 i): Signs P X.val.1 (Y ∘ increment i) Z:=by
    have he : ‖Complex.ofRealCLM‖*(BillQ P k a * P.threshold^2)= Z:=by unfold Z grade; ring
    rw [← he]; exact Prism.skills ((Prism.skin (A i p)).linear R le_rfl)
 rw [show fund o=fun i=> (hollow (Y i): Cipher n) from funext fun i=> Taxi.mon_v ..]; exact dustK P X Y (fun U V g=> congrArg Complex.ofReal (Plaque.sits o U V (agrees_mono g (Finset.coe_subset.mpr t)))) (fun i U=> congrArg Complex.ofReal (gaugeW o U i)) (Complex.ofRealCLM.continuous.measurable.comp (contFee o).measurable) Z (hK _ (ping_f P _)).grade hK -- tune .dot
end WagesC
end YM.CF.Py.Kay
