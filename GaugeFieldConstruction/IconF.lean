import GaugeFieldConstruction.Esther
import GaugeFieldConstruction.Trump
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock.Flux
open Function Filter Metric NormedSpace Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill Kea Flare Rush Tulip Cube SU Dial Thera
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker Classical
attribute [local instance] opCStarAlgebra
open YM.GaugeFieldConstruction CF.Crest CF.Crest.Shore MeasureTheory CF.Vale.Veins
open YM.Stationary (Gaia exileE earth_meas earth_bounded earth_oaks boundsEarth cartWeight geode_sum)
local notation "I"=> Complex.I
abbrev gyroP (x:Cover)(i j:Cauchy.Spin)(p:Bin):ℂ:= mode (tmap p) x * tenderD i j (tough p)
abbrev RomT (x:Cover)(i j:Cauchy.Spin):= (cartWeight:ℂ)* ∫ p:Gaia in boundsEarth, gyroP x i j (exileE p)
variable {N:Side}
private def tentC(f:Site N→ℂ) (p: Gaia):ℂ:= Complex.I * ↑(plants (Complex.im∘ f) p)+ ↑(plants (Complex.re∘f) p)
lemma fancyC (h: Even N.val)(f:Site N→ℂ): Integrable (tentC f) μ0:=by
 unfold tentC; exact (((fortunate (Complex.im∘f) h).ofReal).const_mul _).add ((fortunate (Complex.re∘f) h).ofReal)
lemma earnC (h: Even N.val)(f:Site N→ℂ): (cartWeight:ℂ)*(∫ p:Gaia,tentC f p ∂μ0)=(stageVolume N)⁻¹*∑ i:Site N,f i:= by
 have hm:= fullF (Complex.im∘f) h; have hr:= fullF (Complex.re∘f) h
 unfold tentC; rw [integral_add (((fortunate (Complex.im∘f) h).ofReal).const_mul _) (fortunate (Complex.re∘f) h).ofReal,integral_const_mul,integral_complex_ofReal,integral_complex_ofReal]
 have he:f=(fun i=> I * ↑(f i).im+ ↑(f i).re):=funext fun i=> by apply Complex.ext <;> simp
 rw [show ∑ i:Site N, f i= ∑ i:Site N,(I * ↑(f i).im + ↑(f i).re) from congrArg _ he]; rw [sum_add_distrib, ←mul_sum, ← Complex.ofReal_sum,← Complex.ofReal_sum]; simp only [μ0]; calc
 _ = I * ↑(cartWeight*∫ p:Gaia in boundsEarth,plants (Complex.im∘ f) p)+ ↑(cartWeight*∫ p:Gaia in boundsEarth,plants (Complex.re∘f) p):=by push_cast; ring
 _ = _:=by rw [←hr,←hm]; unfold stageVolume; push_cast; simp only [Function.comp_apply]; ring
lemma at_da (p:Gaia)(z:Site N)(h:p∈cellH z)(f:Site N→ℂ): tentC f p=f z :=by unfold tentC; rw [flora _ _ h, flora _ _ h]; apply Complex.ext <;> simp
lemma iii (p:ℝ)(u:p<(4:ℝ)):IntegrableOn (fun z:Gaia=> ‖z‖^(-p)) boundsEarth MeasureTheory.volume:=by
 let R:=2*Real.pi +1
 have hv: Module.finrank ℝ Gaia=4:= by simp
 have he: AEStronglyMeasurable (fun z:Gaia=> ‖z‖^(-p)) MeasureTheory.volume:=(show Measurable _ from by fun_prop).aestronglyMeasurable
 apply (integrableOn_ball_of_norm_le_rpow (μ:=MeasureTheory.volume) (show 1 ≤ Module.finrank ℝ Gaia by omega) (α:=p) (by simpa only [hv,Nat.cast_ofNat] using u) (r:=R) (C:=1) ?_ he).mono_set (fun x h=> closedBall_subset_ball (lt_add_one _) (earth_bounded _ h))
 exact Eventually.of_forall (fun _=>by rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),one_mul])
lemma pitφ (C:ℝ):IntegrableOn (fun p:Gaia=> C / ‖p‖) boundsEarth MeasureTheory.volume:=by
 simp_rw [div_eq_mul_inv, ←Real.rpow_neg_one]; exact (iii 1 (by norm_num)).const_mul _
lemma remitP (p:Gaia)(z:Site N)(h:p∈cellH z): ‖p‖ ≤ 4* amplitude z:=by
 have hu:‖bark z‖≤ 2*amplitude z:=by
    let g:= amplitude z; have hx: ‖bark z‖^2 ≤ (∑ i:Axis,g^2):=by rw [← geode_sum]; refine sum_le_sum (fun i _=>?_); rw [← sq_abs]; apply pow_le_pow_left₀ (abs_nonneg _) _; exact norm_le_pi_norm (pm z) i
    simp only [sum_const,card_univ, show Fintype.card Axis=4 from Fintype.card_fin 4,nsmul_eq_mul,Nat.cast_ofNat,zero_add] at hx -- tune
    have h:0≤g:=(amplitude_pos _).le; change _ ≤ 2*g; nlinarith [norm_nonneg (bark z)]
 have hh:=proximity z h; have ht:= norm_sub_norm_le p (bark z); rw [norm_sub_rev] at ht; linarith [amplitude_pin z]
lemma Busses : ∃ C:ℝ,0<C∧∀ (N:Side),Even N.val →∀ (s:Site N) (M:Jill.Male) (x y:Cover)(i j:Cauchy.Spin), ‖tellerP x y i j N M s‖≤ C/amplitude s :=by
 obtain ⟨C,p,F⟩:= floor_C (j:=4) (by decide); refine ⟨Real.pi+C,by positivity,fun N e s M x y i j=>?_⟩
 unfold tellerP frankφ; rw [norm_mul, mode_real _ _ (mel_h _).1,one_mul, ← looksB (k:=(s,Classical.arbitrary Slot)) e] -- tune
 apply le_trans (norm_entry ..); apply (norm_add_le ..).trans; have ht : ‖shoe N 4 M (s,Classical.arbitrary Slot)‖ ≤ 1:= by first| exact (shoe_P ..).norm_le| exact (shoe_P e _ 4 M).norm_le _
 refine (add_le_add ht (F e _ M)).trans ?_; let d:= amplitude s; change 1+C/d≤_; rw [add_div]; exact add_le_add (by rw [one_le_div (amplitude_pos _)]; exact amplitude_top e _) le_rfl
variable {N T:ℕ→Side} (g:Tendsto N atTop atTop) (w:∀ i,Even (N i).val){M:ℕ→Jill.Male}(v:Tendsto (fun i=>(M i).val) atTop atTop) (x y:Cover)(i j: Cauchy.Spin)
include g w v
lemma dourC : Tendsto (fun k:ℕ=> (stageVolume (N k))⁻¹*∑ p:Site (N k),tellerP x y i j (N k) (M k) p) atTop (𝓝 (RomT (y-x) i j)):=by
 simp_rw [← earnC (w _) (f:=fun p=>_)] -- tune simp
 obtain ⟨C,u,d⟩:=Busses; let D:= C*4
 let H(k):= tellerP x y i j (N k) (M k)
 have he(k):= fancyC (w k) (H k)
 have ht :∀ i:ℕ,∀ᵐ p:Gaia ∂μ0, p∈boundsEarth ∧ ∃ k:Site (N i),p∈cellH k:= fun i=> arboretum (w i) earth_meas (Set.Subset.refl _)
 have hz:∀ᵐ p:Gaia ∂μ0,p≠0 := ae_restrict_of_ae (by rw [ae_iff]; rw [show {a:Gaia|¬ a≠0}={0} from by ext; simp, measure_singleton]);
 apply Tendsto.const_mul
 apply tendsto_integral_of_dominated_convergence (fun p:Gaia=>D/‖p‖) (fun i=>(he i).aestronglyMeasurable) (pitφ D)
 · intro k; filter_upwards [ht k,hz] with p t a; obtain ⟨q,h⟩:=t.2; rw [at_da p q h]
   have hh:=remitP p q h
   refine (d _ (w k) q _ _ _ _ _).trans ((div_le_div_iff₀ (amplitude_pos _) (norm_pos_iff.mpr a)).mpr ?_); unfold D; nlinarith only [mul_le_mul_of_nonneg_left hh u.le]
 filter_upwards [ae_all_iff.mpr ht,hz] with p u z; choose Y e using (fun i=>(u i).2)
 let X:= exileE p; have hk:= Papyrus.Franc.Loaves.mill Y (driftφ g Y e)
 have H:Jill.Bound Real.pi X:= (pi_norm_le_iff_of_nonneg Real.pi_pos.le).mpr fun i=> abs_le.mpr ⟨((u 0).1 i).1.le,((u 0).1 i).2⟩ -- tune
 have hv:Tendsto (fun k:ℕ=> mixL 4 (M k).val (mel (Y k))) atTop (𝓝 (tough X)):=tendsto_pi_nhds.mpr (fun a=> gulch v hk (Eventually.of_forall (fun i=>(M i).property)) H (fun t=> z (exileE.injective t)) a (Eventually.of_forall fun i=> mel_h _))
 have he:Continuous (fun p:Momentum=>mode p (y-x)):=by unfold mode; fun_prop
 have hh: Continuous (tenderD i j):=by unfold tenderD; fun_prop
 refine ((((he.tendsto _).comp hk).mul ((hh.tendsto _).comp hv))).congr fun k=> Eq.symm (at_da p (Y k) (e k) _)
#print axioms dourC
end YM.CF.Fock.Flux
end
