import YM.SU5.Selected.Time.Alps
import Mathlib.Analysis.Complex.PhragmenLindelof
set_option autoImplicit false
set_option maxHeartbeats 480000
set_option quotPrecheck false
noncomputable section
namespace YM.Spectral.Alps
open OS OS.Semigroup Function Set Filter MeasureTheory Measure Spectral Complex Analysis Boundary Probe
open scoped Topology NNReal ENNReal InnerProductSpace ComplexOrder BigOperators
variable {H:Hilbert}{a:Axis}(S:OS.Semigroup H a)
local notation "U"=> S.edge
local notation "E"=> S.E
variable (x y:H)
def balcony (z:ℂ):H.Op:= (S.edge z.re)*(S.E z.im.toNNReal)
-- no asserts on lower half plane. convenient made globally bounded continuity.
lemma balcony_zero : balcony S 0=1:= by unfold balcony; rw [show (0:ℂ).re=0 from rfl,show (0:ℂ).im.toNNReal=0 by simp]; rw [show U (0:ℝ)=1 from S.birth,show E 0=1 from S.eZero]; exact one_mul _
local notation "k"=> balcony S
@[simp] lemma balcony_high (t:ℝ≥0): k (↑(t:ℝ)*I)=E t:= by unfold balcony; simp only [show (↑(t:ℝ)*I:ℂ).re=0 by simp,show (↑(t:ℝ)*I:ℂ).im.toNNReal=t by simp]; rw [show U (0:ℝ)=1 from S.birth,one_mul]
@[simp] lemma balcony_floor(t:ℝ): k (t:ℂ)= S.edge t:= by unfold balcony; simp [show E 0=1 from S.eZero]
lemma balcony_pay(p:ℂ): ‖k p‖ ≤ 1:=by apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro x; change ‖S.edge _ _‖ ≤_; rw [S.life,one_mul]; apply ((S.E _).le_opNorm _).trans; exact mul_le_of_le_one_left (norm_nonneg _) (S.shrinks _)
lemma basis_cost (z:ℂ) (u:ℂ)(hz:0≤z.im)(hu:0≤u.im): k (z+u)=k z*k u:=by
 have he:= S.eitherE z.im.toNNReal u.re; let T:ℝ≥0:=z.im.toNNReal; unfold balcony; simp only [Complex.add_re,Complex.add_im]; rw [← S.send,Real.toNNReal_add hz hu,S.time] -- order
 change (U _ * U _) * (E _ * E _)=_; rw [←mul_assoc,mul_assoc _ (U _),(show U u.re * E T=E T* U u.re from he.symm)]; simp only [mul_assoc]; rfl
lemma balcony_cont : Continuous (fun z=> k z x):=by
 let H' : Continuous (fun (z:ℂ)=> S.E (z.im.toNNReal) x):= ((S.continuousE x).comp (continuous_real_toNNReal.comp continuous_im)); unfold balcony; simp only [ContinuousLinearMap.mul_apply]; exact S.cont_edge (fun (z:ℂ)=> S.E z.im.toNNReal x) re H' continuous_re
lemma balcony_holo_ge {z:ℂ}(h:0<z.im) : k z=S.F (-I*z):=by
 have hh(x:H):= S.lift_ray x h 0; ext1 x; exact (show k z x=S.F (-I*z) x from by have g:=hh x; simpa [ray,S.unit.origin, balcony] using g)
lemma balcony_holo : AnalyticOnNhd ℂ (balcony S) {z|0<z.im}:=by
 intro z t; have he: -I*z∈inside:=by change 0< (-I*z).re; simpa using (show 0<z.im from t); -- tune
 refine ((S.localHeat _ he).comp (show AnalyticAt ℂ (fun z:ℂ=> -I*z) z from analyticAt_const.mul analyticAt_id)).congr ?_; filter_upwards [Paley.open_loft.mem_nhds t] with z hz; exact (balcony_holo_ge S hz).symm
lemma balcony_law{z:ℂ}(h:0≤z.im): inner ℂ x (k z x)=∫ u:ℝ,Complex.exp ((u:ℂ)*z*I)∂(spectralP S).diagonal x:= spectral S x z h
-- identity principle quantitative secant. Need to mean variation read along heat criterion implies nontrivial Mink orbit (time defines one-point centered differences along seam). flags.
open PhragmenLindelof Bornology Asymptotics
open scoped Filter
lemma sheer(P:H.Op)(z:ℂ) : ‖inner ℂ x (k z y)‖ ≤ ‖x‖*‖y‖ := by
 refine (norm_inner_le_norm (𝕜:=ℂ) ..).trans ?_; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); exact ((k z).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (balcony_pay ..))
lemma lips (d t:ℝ≥0)(v:ℝ)(c: ℝ)(hp:v< ‖inner ℂ x ((E d - E t) y)‖) :∃ i:ℝ, v/2 < ‖inner ℂ x ((U i-U c) y)‖ := by
 let f(z:ℂ):=inner ℂ x (k (z*I) y)-inner ℂ x (U c y)
 let C:= ‖x‖*‖y‖+ ‖inner ℂ x (U c y)‖; have hB(i): ‖f i‖≤C:= (norm_sub_le (inner ℂ x (k (i*I) y)) (inner ℂ x (U c y))).trans (by have he:= sheer S x y (0 : H.Op) (i*I); unfold C; linarith only [he])
 by_contra! h; have hC(z:ℂ)(p:0 ≤ z.re): ‖f z‖≤ v/2:= by
    let t(z:ℂ):= z* I; have ht: Continuous f:= ( (continuous_const.inner ((balcony_cont S y).comp (continuous_id.mul_const _)) ).sub continuous_const) -- tune
    refine PhragmenLindelof.right_half_plane_of_bounded_on_real ⟨?_,ht.continuousOn⟩ ?_ ?_ ?_ p
    · intro i u; have hg:(i*I)∈ Paley.loft:=by change 0<(i*I).im; simpa using (show (0:ℝ) < Complex.re i from u)
      let T:H.Op →L[ℂ] ℂ:= (innerSL ℂ x).comp (ContinuousLinearMap.apply ℂ H.space y); have e:DifferentiableAt ℂ t i:= (differentiable_id.mul_const _).differentiableAt; have uP:= DifferentiableAt.comp (g:=(balcony S)) i ((balcony_holo S (t i) hg).differentiableAt) e; have he:DifferentiableAt ℂ (fun z=> T (balcony S (t z))) i:= DifferentiableAt.comp (g:=fun x=>T x) (f:=(balcony S ∘ t)) i T.differentiableAt uP; exact (he.sub_const (inner ℂ x (U c y))).differentiableWithinAt
    · refine ⟨1,by norm_num,0,?_⟩; simp only [zero_mul,Real.exp_zero]; exact isBigO_iff.mpr ⟨C, Eventually.of_forall (fun z:ℂ=> by simpa using hB z) ⟩ -- IsBigOWith structure?
    · exact isBoundedUnder_of_eventually_le (a:=C) (Eventually.of_forall (fun z=> hB _))
    intro i; unfold f; change ‖_‖≤_; rw [mul_assoc, Complex.I_mul_I,mul_neg_one,← Complex.ofReal_neg, balcony_floor]; simpa [ContinuousLinearMap.sub_apply,inner_sub_right] using h (-i)
 have ht:=hC (t:ℝ) (show 0≤_ from t.property); have hd:=hC (d:ℝ) (show 0≤_ from d.property);
 have hv: inner ℂ x ((E d-E t) y) = f (↑(d:ℝ))-f (↑(t:ℝ)):=by unfold f; rw [balcony_high,balcony_high,sub_sub_sub_cancel_right,ContinuousLinearMap.sub_apply, inner_sub_right] -- `inner ℂ Op.apply` syntax may E special
 exact hp.not_ge (hv ▸ (norm_sub_le ..).trans ( (add_le_add hd ht).trans_eq (add_halves _))) -- maybe orientation eq

local notation "π₁"=> S.orth
local notation "P"=> aboveH S
lemma strictB_eq (p:ℂ): inner ℂ x (k p y)= inner ℂ (P x) (k p (P y)) + inner ℂ x (π₁ y):=by
 let r:= k p; have h(v:H): r (π₁ v)=π₁ v:=by unfold r balcony; rw [ContinuousLinearMap.mul_apply, centered]; exact mink_invar S _ _ (Submodule.starProjection_apply_mem ..)
 have he : Commute (P) r:= (((branch_arc S _).symm).mul_right (branch_power S _)) -- angle
 let B:=(P); have hb(v:H): P (P v)= P v:= (spectralP S).idempotent measurableSet_Ioi v
 have hz(v:H): P v=v-π₁ v:= DFunLike.congr_fun (spotlight S) v; have hk : (P).adjoint=P := (spectralP S).real measurableSet_Ioi
 have hl(v:H):r (P v)=P (r v):=DFunLike.congr_fun he.symm v -- Symm Commute syntax
 calc
    _ = inner ℂ x (r (P y))+inner ℂ x (π₁ y):=by rw [hz,map_sub,h y,inner_sub_right,sub_add_cancel]
    _ = _ := by
        change inner ℂ x (r (P y))+_=inner ℂ (P x) (r (P y))+_; congr 1; calc
            _ = inner ℂ x (P (r (P y))):=by rw [←hl,hb]
            _ = _ := by rw [←ContinuousLinearMap.adjoint_inner_left,hk]
-- Δ in Branch both. real Mink continuation of projected.
lemma split_cost (p q:ℂ) : inner ℂ x ((k p-k q) y)= inner ℂ (P x) ((k p-k q) (P y)):=by
 simp_rw [ContinuousLinearMap.sub_apply, inner_sub_right]; rw [strictB_eq S x y p,strictB_eq S x y q]; abel
lemma reach (p q:ℝ≥0)(v:ℝ)(c:ℝ)(w:v< ‖inner ℂ x ((E p - E q) y)‖) : ∃ t:ℝ, v/2< ‖inner ℂ x ((U t-U c) y)‖ ∧ v/2 < ‖inner ℂ (P x) ((U t-U c) (P y))‖:=by obtain ⟨i,t⟩:= lips S x y p q v c w; exact ⟨i,t, (show inner ℂ x ((U i-U c) y)=_ from (by simpa only [balcony_floor] using (split_cost S x y (i:ℂ) (c:ℂ)))) ▸ t⟩
lemma fail_cost (p q:ℝ≥0)(w: inner ℂ x ((E p - E q) y) ≠ 0) : x∉ S.ground ∧ y∉S.ground:=by
 let z:=(↑(p:ℝ):ℂ)*I; let t:=(↑(q:ℝ):ℂ)*I; have hv:inner ℂ x ((E p - E q) y)=inner ℂ (P x) ((E p - E q) (P y)):= by simpa only [z,t,balcony_high] using (split_cost S x y z t) -- may need simp [z,t]
 rw [lively, lively]; refine ⟨fun i=> w (hv.trans ?_), fun i=> w (hv.trans ?_) ⟩; rw [i,inner_zero_left]; rw [i,map_zero,inner_zero_right]
lemma strict_w (x:H)(w:x∉ S.ground)(t:ℝ≥0): E t x ∉ S.ground := by
 rw [lively]; intro i; apply w; rw [lively]; refine OS.Semigroup.heat_faithful S t _ ( (DFunLike.congr_fun (branch_power S t).symm x).trans i) -- tune
end YM.Spectral.Alps
open YM.Spectral.Alps
#print axioms balcony_holo
#print axioms lips
#print axioms strictB_eq
#print axioms reach
#print axioms fail_cost
#print axioms strict_w
