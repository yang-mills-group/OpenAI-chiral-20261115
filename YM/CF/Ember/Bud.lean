import YM.CF.Ember.Mica
set_option autoImplicit false
noncomputable section
namespace YM.CF.Ember
open Function Filter Lat Lattice Metric MeasureTheory Finset Stationary
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal
variable {N : Side}
lemma cellCore (k:Site N): volume (cellH k)=(ENNReal.ofReal (2*pinch N))^4:=by
 let u:=EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp Axis
 rw [cellH, u.measure_preimage (fir_meas _ |>.nullMeasurableSet)]
 have he(a:Per N): volume (hue a)= ENNReal.ofReal (2*pinch N):=by rw [hue,Real.volume_Ioc]; congr 1; ring
 rw [show fir k = Set.univ.pi fun i=> hue (k i) by ext x; simp [fir,Set.mem_pi], volume_pi_pi]; simp_rw [he]; simp
lemma globeH : volume boundsEarth=(ENNReal.ofReal (2*Real.pi))^4:=by
 let u:=EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp Axis
 rw [boundsEarth,u.measure_preimage (cradle_meas.nullMeasurableSet)]
 rw [show cradle=Set.univ.pi (fun i=> Set.Ioc (-Real.pi) Real.pi) by ext x; simp [cradle,Set.mem_pi],volume_pi_pi]; simp [Real.volume_Ioc,two_mul]
lemma canopy (h:Even N.val): (⋃ k:Site N,cellH k)=ᵐ[volume] boundsEarth:=by
 let S:=⋃ k:Site N,cellH k
 have he:S⊆boundsEarth:= Set.iUnion_subset fun k=> forest k h
 have hg:S≤ᵐ[volume]boundsEarth:= Eventually.of_forall fun _=>fun p=> he p
 have hx:volume S=volume boundsEarth:=by
   rw [show S=_ from rfl,measure_iUnion clears cell_meas,tsum_fintype]; simp_rw [cellCore]; rw [sum_const,card_univ,site_card,nsmul_eq_mul,globeH,payH (N:=N), show 2*((N.val:ℝ)*pinch N)=(N.val:ℝ)*(2*pinch N) by ring, ENNReal.ofReal_mul (Nat.cast_nonneg _),mul_pow]; simp
 refine ae_eq_set.mpr ⟨ae_le_set.mp hg,?_⟩
 change volume (boundsEarth \ S)=0
 rw [measure_sdiff he (MeasurableSet.iUnion cell_meas|>.nullMeasurableSet) (hx.symm ▸ earth_oaks),hx,tsub_self]
open Classical in
def plants (f:Site N→ℝ)(p:Gaia):ℝ:= if h:∃ k:Site N,p∈cellH k then f h.choose else 0
lemma flora (f:Site N→ℝ){p: Gaia}(k:Site N)(h:p∈cellH k):plants f p=f k:=by
 let hx:∃ k,p∈cellH (N:=N) k:=⟨k,h⟩
 rw [plants,dif_pos hx]; congr; exact funext fun i=> overlaps (hx.choose_spec i) (h i)
lemma fortune (f:Site N→ℝ)(k: Site N):IntegrableOn (plants f) (cellH k) volume:=by
 refine IntegrableOn.congr_fun (integrableOn_const (C:=f k) ?_) (fun x h=> (flora f k h).symm) (cell_meas _); rw [cellCore]; finiteness
lemma fortunate (f:Site N→ℝ)(h:Even N.val): IntegrableOn (plants f) boundsEarth volume :=by
 refine IntegrableOn.mono_set_ae ?_ (canopy h).symm.le
 exact integrableOn_finite_iUnion.mpr (fortune f)
lemma fullF (f:Site N→ℝ)(h:Even N.val) : (∑ k,f k)/(N.val:ℝ)^4=cartWeight*(∫ p in boundsEarth,plants f p):=by
 rw [setIntegral_congr_set (canopy h).symm,integral_iUnion_fintype cell_meas clears (fortune f)]
 have hp:=pinch_pos N
 have he(k) : (∫ p in cellH k,plants f p)=(2*pinch N)^4*f k:=by rw [setIntegral_congr_fun (g:=fun _=>f k) (cell_meas _) (fun i hi=>flora f k hi),setIntegral_const,Measure.real,cellCore,ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity),smul_eq_mul]
 simp_rw [he,←mul_sum]; unfold cartWeight; rw [payH (N:=N)]; have H:=nPos N; field_simp
lemma arboretum (h:Even N.val){S:Set Gaia}(hs:MeasurableSet S)(hq:S⊆boundsEarth): ∀ᵐ p ∂volume.restrict S, p∈S ∧ ∃ k:Site N,p∈cellH k:=by
 filter_upwards [ae_restrict_mem hs,ae_restrict_of_ae (canopy h)] with p hp he; exact ⟨hp,Set.mem_iUnion.mp (Eq.mpr he (hq hp))⟩
end YM.CF.Ember
