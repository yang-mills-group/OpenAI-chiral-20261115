import YM.SU5.Relativistic.Ease
import YM.SU5.Relativistic.BraceLimits
/-!
# Difference laws and continuity of full projected frame
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Set Filter Metric MeasureTheory
open MeshClock Germ Vacancy _root_.YM.SelectionAnalysis Analysis
open scoped Topology Classical BigOperators NNReal ENNReal InnerProductSpace
variable {H:Hilbert} {I W:Type*}{j:Axis}{F:Filter W}{M:Mesh}
section evolution
variable (P:Sunbelt j (marks M) H)(E:OS.Semigroup H j)(S T:I→Slab M)(l:List I)(b:Stamp M)(B:I→ H.Op)
local notation "G"=> Axis→ Stamp M
local notation "U" t:max u:max=>nativeE P E (B t) (S t) (T t) u
local notation "v↑" u:max=> fun i:Axis => ((u i:Stamp M):ℝ)
local notation "Zs" l:max b:max x:max=> bracing E.E T (fun i=> (U i (x i))) b l

lemma ordered_cost : ∃ K:ℝ,∀ x:I→Axis→Stamp M, ‖Zs l b x‖≤ K:=by
 induction l generalizing b with
 | nil=> exact ⟨‖(1:H.Op)‖,fun u=>le_rfl⟩
 | cons i l ih=>
    obtain ⟨K,u⟩:= ih (T i).upper
    let C : H.Op:= E.E (heatGap b (T i).lower)
    refine ⟨‖B i‖*K, fun x=>?_⟩
    rw [bracing]
    exact (norm_comp_cost ..).trans (mul_le_mul ((norm_comp_cost ..).trans ((mul_le_of_le_one_left (norm_nonneg _) (E.shrinks _)).trans (native_cost P E _ _ _ _))) (u x) (norm_nonneg _) (norm_nonneg _))

lemma passage_cost (u:I→Axis→ℝ)(x y:W→I→Axis→Stamp M) (p:∀i∈l, safely j (S i) (T i) (u i))
    (k: Tendsto (fun w i a=> ((x w i a:Stamp M):ℝ)) F (𝓝 u)) (t: Tendsto (fun w i a=> ((y w i a:Stamp M):ℝ)) F (𝓝 u)) (h:∀ i∈l, ∀ᶠ s in F,∀ a:Axis,a≠j→x s i a=y s i a):
    Tendsto (fun w=> Zs l b (x w) - Zs l b (y w)) F (𝓝 0):=by
  induction l generalizing b with
  | nil=>change Tendsto (fun w:W=> (1:H.Op)-1) F _; rw [sub_self]; exact tendsto_const_nhds
  | cons i l ih=>
     let C:H.Op:=E.E (heatGap b (T i).lower); let X (w:W):= U i (x w i); let Y₀(w:W):= U i (y w i)
     have hx:= contributes P E (S i) (T i) (B i) (u i) (fun w=> x w i) (fun w=>y w i) (p i List.mem_cons_self) (tendsto_pi_nhds.mp k i) (tendsto_pi_nhds.mp t i) (h i List.mem_cons_self)
     have ht:= ih (T i).upper (fun a t=>p a (List.Mem.tail _ t)) fun a w=>h a (List.Mem.tail _ w)
     obtain ⟨K,aK⟩:=ordered_cost P E S T l (T i).upper B
     apply stuff_mul (u:=fun i=>C*X i) (v:=fun i=> C*Y₀ i) (s:=fun w=> Zs l ((T i).upper) (x w)) (t:=fun w=>Zs l ((T i).upper) (y w)) ⟨_,Eventually.of_forall fun w=>((norm_comp_cost ..).trans ((mul_le_of_le_one_left (norm_nonneg _) (E.shrinks _)).trans (native_cost P E _ _ _ (y w i))))⟩ ⟨K,Eventually.of_forall fun w=> aK _⟩ ?_ ht
     change Tendsto (fun i:W=>C*X i - C*Y₀ i) F _
     have hp:Tendsto (fun w=> C*(X w-Y₀ w)) F (𝓝 0):=by simpa only [mul_zero] using (show Tendsto (fun w=>C*(X w-Y₀ w)) _ (𝓝 (C*0)) from tendsto_const_nhds.mul hx)
     simp_rw [←mul_sub]; exact hp

lemma envelop_small (e:∀ i,∀ (z : marks M) (t:ℝ≥0), ((P.track.crew i).play z).comp (E.E t)=(E.E t).comp ((P.track.crew i).play z)) (u: Axis→ℝ)(i:I): ‖envelope P E e (B i) (S i) (T i) u‖ ≤ ‖B i‖:=by
 obtain ⟨g,p⟩:= Settler.advances M u
 apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
 intro x; exact le_of_tendsto (collecting_point j _ _ _ _ P E e _ p x|>.norm) (Eventually.of_forall fun n=> (ContinuousLinearMap.le_opNorm ..).trans (mul_le_mul_of_nonneg_right (not_far j _ _ _ u P E e _ p n) (norm_nonneg _)))
lemma strong_cont [TopologicalSpace W] (X:W→ H.Op)(Y:W→H) (c:∃ B:ℝ,∀ w, ‖X w‖≤ B) (p:∀ x:H,Continuous fun i => X i x)(h:Continuous Y): Continuous (fun i=> X i (Y i)):=by
  obtain ⟨B,e⟩:= c; refine continuous_iff_continuousAt.mpr fun x=> ?_
  apply tendsto_of_tendsto_of_dist ((p (Y x)).tendsto x); apply squeeze_zero' (Eventually.of_forall fun _=> dist_nonneg)
  swap
  · exact (show Tendsto (fun i=>B*dist (Y i) (Y x)) (𝓝 x) (𝓝 0) from by simpa only [mul_zero] using (tendsto_iff_dist_tendsto_zero.mp (h.tendsto x)).const_mul B)
  exact Eventually.of_forall fun i=>by rw [dist_comm,dist_eq_norm,←map_sub]; exact ((X i).le_opNorm _).trans ((mul_le_mul_of_nonneg_right (e _) (norm_nonneg _)).trans_eq (by rw [←dist_eq_norm]))

lemma braceCont (e:∀ i,∀ (z : marks M) (t:ℝ≥0), ((P.track.crew i).play z).comp (E.E t)=(E.E t).comp ((P.track.crew i).play z)) (x:P.track.Realm P.list):
    Continuous (fun z:I→Axis→ℝ=> bracing (glass P (daylight M) E e).E T (fun i=>envelope P E e (B i) (S i) (T i) (z i)) b l x):=by
 induction l generalizing b with
 | nil=> exact continuous_const
 | cons i l ih=>
     let G':= glass P (daylight M) E e; let A (z:I→Axis→ℝ):= envelope P E e (B i) (S i) (T i) (z i)
     have hv(Ga):=ih Ga
     change Continuous (fun z=> G'.E (heatGap b (T i).lower) (A z (bracing G'.E T (fun i=>envelope P E e (B i) (S i) (T i) (z i)) ((T i).upper) l x)))
     apply Continuous.comp (f:=fun z=> A z _) (G'.E (heatGap b (T i).lower)).continuous -- tune
     exact strong_cont (H:=P.track.Realm P.list) A _ ⟨_,fun i'=>envelop_small P E S T B e (i' i) i⟩ (fun v=> (envelope_cont P E e _ _ _ v).comp (continuous_apply _)) (hv ((T i).upper))
end evolution
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.passage_cost
