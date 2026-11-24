import YM.Work.F05.PiDensity
import YM.CF.BProof.Law.Product
import YM.CF.BProof.Chord

/-! Density of Mark noise against Haar, still a probability law; no zero extension used
for conditioning. Provide integral identities for complex/cylindrical observables. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Law
open Function Set RG MeasureTheory Filter Finset
open scoped BigOperators Topology Classical ENNReal Matrix.Norms.Frobenius
variable {I E : Type}[Fintype I][DecidableEq I]
variable [NormedAddCommGroup E][NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable (G: Gauge) (r:ℝ)(hr:0<r)(h:r≤1)
-- supported law
def cloud := G.probHaar.withDensity (fun v : G.El=> ENNReal.ofReal (density G r 1 v))
lemma den_c : Measurable (density G r 1):=(density_c ..).comp (g:=(Function.uncurry (density G r))) (f:=fun v:G.El=>(1,v)) (by fun_prop)
include hr h
lemma cloud_unit : IsProbabilityMeasure (cloud G r):=by
 have H:= density_unit G (1:G.El) hr h; let f:=density G r 1
 let P:=G.probHaar; have hh:Measurable f:=den_c G r; have hx:Integrable f P:=Integrable.of_bound hh.aestronglyMeasurable ((4/r)^matDim G) (Eventually.of_forall fun i=> (Real.norm_of_nonneg (density_pay G 1 i hr h).1).trans_le (density_pay G 1 i hr h).2) -- tune
 refine ⟨?_⟩; unfold cloud; rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,← ofReal_integral_eq_lintegral_ofReal hx (Eventually.of_forall (fun i=> (density_pay G 1 i hr h).1)), H, ENNReal.ofReal_one]
lemma cloud_ae : ∀ᵐ x∂cloud G r,G.chord x≤r :=by
 apply (ae_withDensity_iff ((den_c G r).ennreal_ofReal)).mpr; apply Eventually.of_forall; intro i h; by_contra! p; apply h; simp only [density_apply,cd_one,if_neg p.not_ge,ENNReal.ofReal_zero] -- tune neg implication
lemma multicloud : ∀ᵐ x∂ Measure.pi (fun _:I=> cloud G r),∀ i,G.chord (x i)≤r:=by
 haveI:=cloud_unit G r hr h
 apply ae_all_iff.mpr; intro i; exact (Measure.quasiMeasurePreserving_eval (μ:=fun _:I=>cloud G r) i).tendsto_ae (cloud_ae G r hr h)
lemma cloud_w (F:(I→G.El)→E):
    (∫ x,F x ∂Measure.pi (fun _:I=>cloud G r))=∫ x,(∏ i,density G r 1 (x i)) • F x ∂Measure.pi (fun _:I=>G.probHaar):=by
 let μ:=Measure.pi fun _:I=>G.probHaar
 let B(x:I→ G.El):=∏ i,density G r 1 (x i)
 let Q(q: G.El):= ENNReal.ofReal (density G r 1 q); let L(x:I→ G.El):=∏ i,Q (x i)
 have hp: Measurable Q:=(den_c G r).ennreal_ofReal; have hL: Measurable L:= Finset.measurable_prod _ (fun i _=> hp.comp (measurable_pi_apply _))
 have ha(x:I→G.El): L x=ENNReal.ofReal (B x):=by unfold L Q B; rw [ENNReal.ofReal_prod_of_nonneg]; exact fun i _=> (density_pay G 1 (x i) hr h).1
 have hh(x:I→ G.El): 0≤B x:= prod_nonneg fun i _=> (density_pay G 1 _ hr h).1
 haveI:= cloud_unit G r hr h; have H:(μ.withDensity L)=Measure.pi (fun _:I=>cloud G r):= @Work.F05.piDensity I _ (fun _=> G.El) _ (fun _=>G.probHaar) _ (fun _=>Q) (fun _=>hp) (fun i=> (show SigmaFinite (cloud G r) from inferInstance))
 rw [← H,integral_withDensity_eq_integral_toReal_smul hL (Eventually.of_forall (fun i=> by rw [ha]; exact ENNReal.ofReal_lt_top))]; simp_rw [ha,ENNReal.toReal_ofReal (hh _)]; rfl

/-- Inserting all-cloud densities, even when nose only needs S coordinates. -/
lemma cloud_w_part [CompleteSpace E](S: Finset I)(F:(I→G.El)→E)(hp:Envelope F)(hk:∀ x y, Set.EqOn x y (↑S) → F x=F y):
    (∫ x,F x ∂Measure.pi (fun _:I=>cloud G r))=∫ x,(∏ i∈S,density G r 1 (x i)) • F x ∂Measure.pi (fun _:I=>G.probHaar):=by
 let P:=Measure.pi fun _:I=> G.probHaar; let d(U:I→ G.El)(i:I):=density G r 1 (U i); let W(T:Finset I)(x:I→G.El):=∏ i∈T,d x i
 have hx (T:Finset I) : Envelope (W T) := by
    refine ⟨Finset.measurable_prod _ (fun i _=> (den_c G r).comp (measurable_pi_apply _)),((4/r)^matDim G)^T.card,?_⟩; intro i; rw [Real.norm_of_nonneg (prod_nonneg (fun k _=> (density_pay G _ _ hr h).1))]; apply le_trans (b:=∏ _∈ T,((4/r)^matDim G)) (prod_le_prod (fun k _=> (density_pay G _ _ hr h).1) (fun k _=> (density_pay G _ _ hr h).2)); rw [prod_const]
 have e (T) : Envelope (fun i=> W T i • F i) := by
    obtain ⟨C,hC⟩:=(hx T).cost; obtain ⟨D,hD⟩:=hp.cost; exact ⟨(hx T).meas.smul hp.meas, C*D,fun i=> (norm_smul ..).trans_le (mul_le_mul (hC i) (hD i) (norm_nonneg _) ((norm_nonneg _).trans (hC i)))⟩
 have hh(u v:I→ G.El): F (patch S u v)=F u:=hk _ _ (patch_on ..)
 have h'(u v:I→ G.El): W (Finset.univ) (patch S u v)=W S u*W Sᶜ v:= by
    have hv: W Finset.univ (patch S u v)=W S (patch S u v)*W Sᶜ (patch S u v):=(prod_mul_prod_compl S _).symm
    rw [hv,show W S (patch S u v)=W S u from prod_congr rfl fun i hi=> congrArg (density G r 1) (patch_on S u v hi), show W Sᶜ (patch S u v)= W Sᶜ v from prod_congr rfl fun i hi=> congrArg (density G r 1) (patch_off S u v hi)]
 rw [cloud_w G r hr h]; change (∫ x,W Finset.univ x • F x ∂P)=∫ x,W S x • F x ∂P; rw [show P=Measure.pi fun _:I=> G.probHaar from rfl,Law.refresh S _ (e Finset.univ)]; simp_rw [h',hh]
 have hq : ∫ v,W Sᶜ v ∂P=1:=by
    let g(i:I)(x:G.El): ℝ:=if i∈S then 1 else density G r 1 x; have hq(i:I): ∫ x,g i x ∂ G.probHaar=1:=by unfold g; split_ifs; simp; exact density_unit G 1 hr h
    have hf(v): W Sᶜ v=∏ i,g i (v i):=by
      rw [← prod_mul_prod_compl S,Finset.prod_eq_one (f:=fun i=>g i (v i)) (fun i hi=>if_pos hi),one_mul]; exact prod_congr rfl fun i hi=> (if_neg (mem_compl.mp hi)).symm
    simp_rw [hf]; rw [show P=Measure.pi _ from rfl,integral_fintype_prod_eq_prod]; simp_rw [hq]; simp
 change (∫ u, ∫ v, (W S u*W Sᶜ v) • F u ∂P ∂P)=_
 simp_rw [mul_comm (W S _),mul_smul,integral_smul_const,hq,one_smul]
 rfl
end YM.CF.BProof.Law
