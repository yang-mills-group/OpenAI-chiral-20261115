import YM.CF.Vow.Cause
import YM.CF.Vale.Trilogy
import YM.CF.Vow.View
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Bake
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
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
open Vow Push.AbsoluteSums.Trees
variable{n:Side}{h a b c d:ℝ}{γ δ q e v:ℝ}{P:BudgetPoint}
abbrev lagE (x:Scree.Hub n):Aura n:=⟨x.val.2,x.val.1,x.property⟩
-- one distinguished anchor for now. SPIN not asserted
abbrev fastV(x:Aura n):Seat n:= Classical.choose x.property
lemma fastX(x:Aura n):fastV x∈ x.val:=Classical.choose_spec x.property
abbrev knotD(x:Aura n): Scree.Hub n:=⟨(fastV x,x.val),fastX x⟩
abbrev cloveE (D:Pax n)(A:Ids n):RegBudget n:=fun i=> if knotD (lagE i)=i then (fun V=> D (lagE i) (V,A)) else 0
abbrev Turf (F:Pax n):Prop:=∀ (i:Aura n)(V:Orbit n)(A:Ids n),F i V= F i (V.1,A)
variable (F:Pax n)(p:Turf F)(A:Ids n)
local notation "FQ"=> FeeD P F
open Rue
lemma yelp(X:Aura n): lagE (knotD X)=X:=Subtype.ext rfl
include p
lemma turfK : Turf (FeeD P F):=by
 intro i V T; unfold FeeD spinD lasting zenS; split; swap; · rfl
 apply tsum_congr; intro m; unfold funge; rw [Finset.sum_apply, Finset.sum_apply]; apply sum_congr rfl; intro j _; unfold sta; split; swap; · rfl
 unfold guava; simp only [Pi.smul_apply,Finset.prod_apply]; exact congrArg _ (prod_congr rfl fun i _=> p _ _ _)
lemma lay_e (V:Orbit n) : exponentL P (cloveE F A) V.1=coldE P F V:=by
 unfold exponentL coldE; rw [sum_filter]; symm; rw [← Finset.sum_filter_add_sum_filter_not (univ:Finset (Scree.Hub n)) (fun i=> knotD (lagE i)=i) (fun i=> numbE P.threshold i.val.2 (cloveE F A i) V.1),sum_eq_zero (s:= univ.filter fun i=>¬ knotD (lagE i)=i) (fun i u=>by rw [cloveE,if_neg (mem_filter.mp u).2]; simp [numbE]),add_zero]
 refine Finset.sum_bij (fun i _=> knotD i) (fun i _=>mem_filter.mpr ⟨mem_univ _,by rw [yelp]⟩) (fun i _ j _ v=> ?_) (fun i v=>⟨lagE i, mem_univ _,(mem_filter.mp v).2⟩) (fun i _=> ?_)
 · exact Subtype.ext (congrArg (fun j:Scree.Hub n=>j.val.2) v)
 rw [cloveE,yelp,if_pos rfl]; split_ifs with h; rw [p i V A]; exact (Set.indicator_of_mem (show V.1∈ {U|pingS P.threshold i.val U} from h) (fun V=>F i (V,A))).symm; exact (Set.indicator_of_notMem (show V.1∉{U|pingS P.threshold i.val U} from h) (fun V=>F i (V,A))).symm
variable (f:Aura n→ℝ)(u:Ready Palot.stern P.B f (P.supportExponent+e) γ δ q)(t:1≤h)(g:∀ i:Aura n, Medal P i.val ∅ (F i) h (f i))(he:0<e)
abbrev fareE (P:BudgetPoint)(f:Aura n→ℝ)(x: Scree.Hub n):ℝ:= if knotD (lagE x)=x then fareX P.B P x.val.2 * spanD (lagE x) f 0 else 0
private lemma frontV(i:Scree.Hub n)(k:knotD (lagE i)=i): oV (cloveE (FeeD P F) A i)= FeeD P F (lagE i):=by
 funext V; exact (congrFun (show cloveE (FeeD P F) A i = _ from if_pos k) V.1).trans (turfK F p _ _ _).symm -- tune
include he u t g
lemma sixV : IncX (fun _=>False) (cloveE (FeeD P F) A) P h (reserveT P.power P.order P.B e * (γ*q^0*(1-q)⁻¹)):=by
 let H(i:Aura n):=cloveE (FeeD P F) A (knotD i); have ht':=add_pos P.exponent_pos he; have vp(i):=glenP i t g u ht'.le 0; let ZU:=fareE P f
 refine ⟨⟨ZU,fun i=>?_,fun i=>?_⟩, fun _ v=>v.elim⟩
 · by_cases z:knotD (lagE i)=i
   · dsimp only [ZU,fareE]; rw [if_pos z]; exact (show Medal P i.val.2 ∅ (oV (cloveE (FeeD P F) A i)) h _ from by rw [frontV F p A i z]; exact vp (lagE i)).preservesE A (zero_le_one.trans t) _
   unfold ZU fareE cloveE; rw [if_neg z,if_neg z]; exact Vale.rinse ..
 let R:=reserveT P.power P.order P.B e; have hx(A:Aura n):0 ≤ spanD A f 0:=(vp _).wage (zero_le_one.trans t)
 have hl(x:Aura n): P.mass x.val (ZU (knotD x)) ≤ R*(spanD x f 0 * Trees.currency P.B (P.supportExponent+e) x.val):=by
    unfold ZU fareE; rw [yelp,if_pos rfl]
    let U:= spanD x f 0; rw [show P.mass x.val _= Trees.currency P.B P.supportExponent x.val* spanD x f 0*fareX P.B P x.val from (by unfold BudgetPoint.mass Trees.currency; change _*_=_*_ ; ring_nf)]
    apply le_trans (mul_le_mul_of_nonneg_left (Nor.coinPay P x.val e he) (mul_nonneg (Real.exp_pos _).le (hx x))); unfold R Trees.currency; rw [add_mul, Real.exp_add]; exact le_of_eq (by ring)
 have hU:0≤ R:=by unfold R reserveT coin_n stilK; positivity
 refine le_trans ?_ (mul_le_mul_of_nonneg_left (thinX u ht'.le i 0) hU)
 rw [← Finset.sum_filter_add_sum_filter_not (univ:Finset (Scree.Hub n)) (fun i=> knotD (lagE i)=i) (fun y=> if i=y.val.1 then P.mass y.val.2 (ZU y) else 0),sum_eq_zero (s:= univ.filter fun i=>¬ knotD (lagE i)=i) (fun j u=>by unfold ZU fareE; rw [if_neg (mem_filter.mp u).2]; simp [BudgetPoint.mass]),add_zero]
 let Y:= fun (x:Scree.Hub n)=>if i=x.val.1 then P.mass x.val.2 (ZU x) else 0
 let W:= univ.filter (fun x:Scree.Hub n=>knotD (lagE x)=x)
 have hy:(∑ j:Aura n,Y (knotD j))=∑ i∈W,Y i:=sum_bij (fun i _=>knotD i) (fun i _=>mem_filter.mpr ⟨mem_univ _,by rw [yelp]⟩) (fun i _ j _ v=> (Subtype.ext (congrArg (fun j:Scree.Hub n=>j.val.2) v))) (fun i v=>⟨lagE i,mem_univ _,(mem_filter.mp v).2⟩) (fun _ _=> rfl)
 rw [show (∑ i∈_,_)=_ from hy.symm, mul_sum,sum_filter]; refine sum_le_sum fun x _=>?_ ; unfold Y; split_ifs with v w t'
 · exact hl _
 · exact False.elim (w ((show i= fastV x from v).symm ▸ fastX x))
 · exact mul_nonneg hU (mul_nonneg (hx x) (Real.exp_pos _).le)
 exact le_rfl
end YM.CF.Bake
