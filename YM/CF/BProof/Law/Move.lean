import YM.CF.BProof.Law.Product
import YM.Work.F05.PiDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.LinearAlgebra.Determinant

set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Law.MP
open Function MeasureTheory Filter Set
open scoped BigOperators Topology Classical ENNReal
-- extend operations
variable {A B F I J:Type}[Fintype I][Fintype J] [MeasurableSpace A][MeasurableSpace B]
variable {μ:Measure A}{ν:Measure B}{f:A→ B}{S:Set B}
lemma cut (h:MeasurePreserving f μ ν)(s:MeasurableSet S) : MeasurePreserving f (μ.restrict (f ⁻¹' S)) (ν.restrict S):= by rw [← h.map_eq, Measure.restrict_map h.measurable s]; exact ⟨h.measurable,rfl⟩ -- rw tune
lemma fund (h:MeasurePreserving f μ ν) (g:B→ ℝ≥0∞)(hg:Measurable g) : MeasurePreserving f (μ.withDensity (g ∘ f)) (ν.withDensity g) := by
 refine ⟨h.measurable,Measure.ext fun S H=>?_⟩; have hh:=cut h H; rw [Measure.map_apply h.measurable H, withDensity_apply _ H, withDensity_apply _ (h.measurable H), ← hh.map_eq]; exact (lintegral_map hg hh.measurable).symm -- tune
lemma finite (h:MeasurePreserving f μ ν) [IsFiniteMeasure ν] : IsFiniteMeasure μ := ⟨by convert lt_top_iff_ne_top.mpr (measure_ne_top ν univ) using 1; exact (by simpa using h.measure_preimage (nullMeasurableSet_univ (μ:=ν)))⟩ -- tune
lemma scheme (μ:I→J→ Measure A)[∀ i j,SigmaFinite (μ i j)] : MeasurePreserving (MeasurableEquiv.curry I J A) (Measure.pi fun i:I×J=> μ i.1 i.2) (Measure.pi fun i=> Measure.pi (μ i)):= by
 let e:=MeasurableEquiv.curry I J A; suffices h:MeasurePreserving e.symm _ _ by exact h.symm
 refine ⟨e.symm.measurable, Eq.symm (Measure.pi_eq ?_)⟩; intro T ht; let V(i:I):=Set.univ.pi fun j=> T (i,j)
 have hp : e.symm ⁻¹' (Set.univ.pi T)=Set.univ.pi V := by
   ext y; exact ⟨fun h i _ j _ => h (i,j) (Set.mem_univ _), fun h i _=> h i.1 (Set.mem_univ _) i.2 (Set.mem_univ _)⟩
 rw [Measure.map_apply e.symm.measurable (MeasurableSet.univ_pi ht), hp, Fintype.prod_prod_type,Measure.pi_pi]; exact Finset.prod_congr rfl fun i _ => Measure.pi_pi ..
lemma volume_curry : MeasurePreserving (MeasurableEquiv.curry I J ℝ) := scheme (fun (_:I) (_:J)=> (volume:Measure ℝ))

open Matrix
lemma linear [DecidableEq I](f:(I→ℝ)→ₗ[ℝ] (I→ℝ))(h:0<LinearMap.det f) : MeasurePreserving f (ENNReal.ofReal (LinearMap.det f) • volume) volume := by
 refine ⟨f.continuous_of_finiteDimensional.measurable,?_⟩; rw [Measure.map_smul,Real.map_linearMap_volume_pi_eq_smul_volume_pi h.ne',abs_of_pos (inv_pos.mpr h),smul_smul, ← ENNReal.ofReal_mul h.le,mul_inv_cancel₀ h.ne',ENNReal.ofReal_one,one_smul]
lemma lin_stamp [DecidableEq I](T:Matrix I I ℝ)(ht:0<T.det) : MeasurePreserving T.mulVecLin (ENNReal.ofReal T.det • volume) volume := by
 have hx:LinearMap.det T.mulVecLin=T.det:=by change LinearMap.det (Matrix.toLin' T)=_; rw [LinearMap.det_toLin']; -- tune
 rw [←hx]; exact linear _ (hx ▸ ht)

-- columns. Y0 from iid patch at significant S; replace others.
section
variable (μ ν:I→ Measure A)(β:I→Measure B)[∀ i, IsProbabilityMeasure (μ i)][∀ i, SigmaFinite (ν i)][∀ i,SigmaFinite (β i)]
lemma rearrange [DecidableEq I](S:Finset I)(d:I→ B → A)(h:∀ i,Measurable (d i))(k:∀ i,i∈ S→ IsProbabilityMeasure (β i))(u:∀ i,i∈S→ μ i=ν i)(v:∀ i,i∉ S→ MeasurePreserving (d i) (β i) (ν i)):
    MeasurePreserving (fun x : (I→ A) × (I→ B)=> Law.patch S x.1 (fun i=>d i (x.2 i))) ((Measure.pi μ).prod (Measure.pi β)) (Measure.pi ν):=by
 let q(x : (I→A) × (I→ B)):= patch S x.1 (fun i=>d i (x.2 i)); have hx:Measurable q:=(patch_m (B:=A) S).comp (f:=fun x : (I→ A) × (I→ B)=>(x.1,fun i=>d i (x.2 i))) (measurable_fst.prodMk (measurable_pi_lambda _ fun i=> (h i).comp ((measurable_pi_apply i).comp measurable_snd)))
 refine ⟨hx, Eq.symm (Measure.pi_eq ?_)⟩; intro T p; let V(i:I):= if i∈ S then T i else Set.univ; let W(i:I):=if i∈ S then Set.univ else d i ⁻¹' T i
 have hp:q ⁻¹' (Set.univ.pi T)=(Set.univ.pi V)×ˢ(Set.univ.pi W):=by
   ext y; change (∀ i:I,i∈univ → q y i∈ T i) ↔ (∀ i:I,i∈univ → y.1 i∈ V i) ∧ (∀ i:I,i∈univ → y.2 i∈ W i); simp only [mem_univ,true_implies]
   constructor
   · intro a; constructor
     · intro i; specialize a i; by_cases hi:i∈S <;> simp [hi,V] <;> simpa only [hi,q,Law.patch,↓reduceIte] using a
     intro i; specialize a i; by_cases hi:i∈ S<;>simp [hi,W] <;> simpa only [hi,q,Law.patch,↓reduceIte] using a
   rintro ⟨a,b⟩ i; specialize a i; specialize b i; by_cases hi:i∈S; simpa [hi,q,Law.patch,V] using a; simpa [hi,q,Law.patch,W] using b
 change Measure.map q _ _ = _; rw [Measure.map_apply hx (MeasurableSet.univ_pi p), hp,Measure.prod_prod,Measure.pi_pi,Measure.pi_pi,←Finset.prod_mul_distrib]; apply Finset.prod_congr rfl; intro i _; by_cases hi:i∈ S
 · haveI:= k i hi; rw [show V i=T i from if_pos hi,show W i= univ from if_pos hi,measure_univ,mul_one,u i hi]
 rw [show V i= univ from if_neg hi, show W i=d i ⁻¹' T i from if_neg hi, measure_univ,one_mul]; exact (v i hi).measure_preimage (p i).nullMeasurableSet
end
lemma densify {μ:I→ Measure A}[∀ i,SigmaFinite (μ i)] {g:I→ A→ ℝ}(h:∀ i,Measurable (g i))(u:∀ i x,0≤g i x) [NormedAddCommGroup F][NormedSpace ℝ F](f:(I→ A)→ F):
    (∫ x,f x ∂Measure.pi fun i=>(μ i).withDensity (fun a=> ENNReal.ofReal (g i a))) = ∫ x,(∏ i,g i (x i)) • f x ∂Measure.pi μ:=by
 let Q(i:I)(x:A):= ENNReal.ofReal (g i x); let B(x : I→A):= ∏ i, Q i (x i); have he(i):Measurable (Q i):=(h i).ennreal_ofReal; have hx:Measurable B:= Finset.measurable_prod _ (fun i _=> (he i).comp (measurable_pi_apply _))
 haveI:∀ i,SigmaFinite ((μ i).withDensity (Q i)):= fun i=> SigmaFinite.withDensity_ofReal _; change (∫ x,f x ∂ Measure.pi fun i=>_)=_; rw [← Work.F05.piDensity μ Q he,integral_withDensity_eq_integral_toReal_smul hx _]
 · apply integral_congr_ae; apply Eventually.of_forall; intro x; dsimp only [B,Q]; rw [← ENNReal.ofReal_prod_of_nonneg (f:=fun i=>g i (x i)) (fun i _=> u i (x i)), ENNReal.toReal_ofReal (Finset.prod_nonneg fun i _=> u i (x i))] -- tune Q
 exact Eventually.of_forall fun x=> ENNReal.prod_lt_top (f:=fun i=>Q i (x i)) fun i _=> ENNReal.ofReal_lt_top
end YM.CF.BProof.Law.MP
