import GaugeFieldConstruction.Levana
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vale.Veins
open Function Filter Lattice Laurent Bloch Wilson Precision RG Next.Free Work.F08 Craft Pressure Stationary Tree Reef Hom AnalyticBridge.LocalGaussianLaws
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.Frobenius
open Exterior Next.Free.Stretch Finset Matrix
open Crest.Shore CF.Jill CF.Fir MeasureTheory Lat Ember
local notation "I"=>Complex.I
abbrev plumed (z:Cover): Gaia:= exileE.symm (stem z)
def stage (z:Cover): Set Gaia:= (fun x:Gaia=> x-plumed z)⁻¹' boundsEarth -- stage conflicts
lemma doorM(z:Cover) : MeasurableSet (stage z):= earth_meas.preimage (by fun_prop)
local notation "π"=>Real.pi
lemma counts_Z (x:Gaia)(z:Cover): x∈stage z ↔ ∀ i:Axis, -π< x i-2*π*(z i)∧ x i-2*π*(z i) ≤ π:= Iff.rfl
lemma meet_Z : Pairwise (Function.onFun Disjoint stage):=by
 intro i j p; apply Set.disjoint_left.mpr; intro x hx hy; apply p; funext a; by_contra v; obtain l|r:=lt_or_gt_of_ne v <;> have hp:= (counts_Z x i).mp hx a <;> have he:= (counts_Z x j).mp hy a
 · have hx:(i a:ℝ)+1 ≤ j a := by exact_mod_cast show i a+1≤j a from l; -- tune
   nlinarith [Real.pi_pos,hp.2,he.1]
 have hx:(j a:ℝ)+1≤ i a:=by exact_mod_cast show j a +1≤ i a from r; -- tune
 nlinarith [Real.pi_pos,hp.1,he.2]
lemma fillΖ : (⋃ z:Cover, stage z)=Set.univ:=by
 ext x; constructor; · intro _; trivial
 intro _; let v(i:Axis):ℤ:=⌈(x i-π)/(2*π)⌉
 refine Set.mem_iUnion.mpr ⟨v,(counts_Z ..).mpr fun i=>?_⟩; have he: (x i-π)/(2*π)≤ v i:= Int.le_ceil _; have hx: ↑(v i)-1 < (x i-π)/(2*π):=(sub_lt_iff_lt_add).mpr (Int.ceil_lt_add_one _)
 rw [lt_div_iff₀ (by positivity)] at hx; rw [div_le_iff₀ (by positivity)] at he; constructor <;> linarith
lemma knobs_C : (volume:Measure Gaia)=Measure.sum (fun z=> volume.restrict (stage z)):=by rw [← Measure.restrict_iUnion meet_Z doorM,fillΖ,Measure.restrict_univ]
variable {f:Bin→ℂ}
abbrev μ0 := volume.restrict boundsEarth
abbrev stageFn (z:Cover) := MeasurableEquiv.addRight (plumed z)
lemma spinQ (z:Cover): MeasurePreserving (stageFn z) μ0 (volume.restrict (stage z)):= by
 have he:MeasurePreserving (stageFn z) volume volume:= measurePreserving_add_right ..
 have hx: boundsEarth=(stageFn z)⁻¹' stage z:= by ext x; change _ ↔ x+plumed z-plumed z∈boundsEarth; rw [add_sub_cancel_right]
 unfold μ0; rw [hx]; apply he.restrict_preimage; exact doorM _
lemma echoRev (h:∀ z:Cover, Integrable (fun p:Gaia=>f (exileE p + CF.Jill.stem z)) μ0) (g: Summable (fun z:Cover=> ∫ p:Gaia, ‖f (exileE p + CF.Jill.stem z)‖ ∂μ0)): Integrable (f∘ exileE) volume ∧ (∫ p:Gaia,shelved f (exileE p) ∂μ0)= ∫ p:Gaia,f (exileE p) :=by
 have he: (fun z=> ∫ p:Gaia, ‖f (exileE p + CF.Jill.stem z)‖ ∂μ0) =(fun z=>∫ p:Gaia in stage z, ‖f (exileE p)‖):=funext fun z=> (spinQ z).integral_comp (stageFn z).measurableEmbedding (fun p=> ‖f (exileE p)‖)
 have hZ: Integrable (f ∘ exileE) volume:= by
    rw [knobs_C]; apply integrable_sum_measure (fun z=> ((spinQ z).integrable_comp_emb (g:=f ∘ exileE) (stageFn z).measurableEmbedding).mp (h z)) (he ▸ g) -- tune
 refine ⟨hZ,?_⟩; have ht:= (hasSum_integral_of_summable_integral_norm h g).tsum_eq; rw [show (∫ p:Gaia,shelved f (exileE p) ∂μ0)= _ from ht.symm]; conv_rhs=> rw [knobs_C]
 rw [integral_sum_measure (show Integrable (fun p:Gaia=> f (exileE p)) (Measure.sum (fun z=> volume.restrict (stage z))) from by rw [←knobs_C]; exact hZ)] -- tune
 exact tsum_congr fun z=> (spinQ z).integral_comp (stageFn z).measurableEmbedding (f ∘ exileE)
-- DCT supplies
lemma waxQ (s:Cover)(i j:Cover × PlaqAxes)(r:TypeFace 1): Measurable fun p:Gaia=> WritW i j r (exileE p+ CF.Jill.stem s):= by
 have hp(z:Cover × PlaqAxes): Continuous fun x=> Pontiff z x r:=by
    unfold Pontiff; let h:= (resume z r).comp (show Continuous tmap from by unfold tmap; fun_prop); refine (Continuous.mul ((Continuous.pow ?_ 4).mul ?_) h); · unfold Crest.Shore.weave; fun_prop
    unfold glowτ; fun_prop
 unfold WritW; apply Measurable.mul
 · apply Measurable.inv; unfold Crest.Shore.radius; fun_prop
 apply Measurable.mul; · apply (hp _).measurable.comp (f:=fun p=> exileE p+ CF.Jill.stem s) (by fun_prop)
 exact (show Continuous (fun x:Bin=> star (Pontiff i x r)) from (hp i).star).measurable.comp (f:=fun p=> exileE p+stem s) (by fun_prop) -- tune
lemma Seaport (i j:Cover × PlaqAxes)(r:TypeFace 1): Integrable (WritW i j r∘ exileE) volume ∧ gridQ i j r= (cartWeight:ℂ) * ∫ p:Gaia,WritW i j r (exileE p):=by
 obtain ⟨C,g,u⟩:=tipW; have hp (z:Cover) : ∀ᵐ p:Gaia ∂μ0, ‖WritW i j r (exileE p+stem z)‖ ≤ C*income z:=by
    filter_upwards [ae_restrict_mem earth_meas,ae_restrict_of_ae (show ∀ᵐ x:Gaia,x≠0 from by rw [ae_iff]; rw [show {x: Gaia|¬ x≠0}={0} from by ext; simp,measure_singleton])] with p t h
    let M:ℕ→Side:= fun i=> ⟨2*i+1,by omega⟩; have hv:Tendsto M atTop atTop:= tendsto_atTop.mpr fun b=> (eventually_ge_atTop b.val).mono fun x (u:b.val≤x)=> (show b.val≤2*x+1 from by omega)
    have hx(a:ℕ) : Odd (M a).val:=⟨a,rfl⟩
    have hk:Bound Real.pi (exileE p):= (pi_norm_le_iff_of_nonneg Real.pi_pos.le).mpr fun i=>abs_le.mpr ⟨(t i).1.le,(t i).2⟩
    apply le_of_tendsto (sweepsE (F:=fun _=>tmap (exileE p)) hv (Eventually.of_forall hx) tendsto_const_nhds i j r hk (fun u=> h (exileE.injective u)) z).norm
    filter_upwards [hv.eventually (raising z)] with i0 k; unfold chelate; rw [if_pos k]; exact (u (M i0) (hx i0) _ (b_base hk) _ _ _ _).trans_eq (congrArg (C*·) (by rw [←income_lift,k]))
 haveI: IsFiniteMeasure μ0:=⟨by rw [show μ0 _=volume boundsEarth by simp [μ0]]; exact lt_of_le_of_ne le_top earth_oaks⟩
 let f:=WritW i j r
 have he(z:Cover):Integrable (fun p:Gaia=> f (exileE p +stem z)) μ0:=(integrable_const (C*income z)).mono' ((waxQ z _ _ _).aestronglyMeasurable) (hp z)
 obtain ⟨H,W⟩:= echoRev he (by
    refine Summable.of_nonneg_of_le (fun i=> integral_nonneg (fun _=> norm_nonneg _)) (g:=fun i=>_) (f:=fun i=> μ0.real Set.univ*(C*Crest.Shore.income i)) (fun i=> le_trans (integral_mono_ae (he i).norm (integrable_const (C*Crest.Shore.income i)) (hp i)) (by rw [integral_const,smul_eq_mul])) ((wallet.mul_left C).mul_left _)) -- tune
 exact ⟨H,congrArg ((↑cartWeight:ℂ)*·) W⟩
end YM.CF.Vale.Veins
end
