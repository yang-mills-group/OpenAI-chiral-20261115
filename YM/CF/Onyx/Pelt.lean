import YM.CF.Onyx.Tent
set_option autoImplicit false
noncomputable section
namespace YM.CF.Onyx
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill Flare
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open MeasureTheory
open YM.Stationary (Gaia cartWeight)
variable {N:Side}{x:Gaia}{k:Site N}{R:ℝ}
def pie (R:ℝ)(k:Site N):= (fun p:Gaia=> R⁻¹ • p) ⁻¹' cellH k
def apr (A:Site N→Peb)(R:ℝ)(x:Gaia):= ∑ i:Site N,(pie R i).indicator (fun _=> A i) x
lemma pies (R:ℝ)(k:Site N):MeasurableSet (pie R k):= (cell_meas _).preimage (by fun_prop)
lemma shout (h:x∈ pie R k)(F:Site N→Peb): apr F R x=F k:=by
 rw [apr,sum_eq_single k]; · rw [Set.indicator_of_mem h]
 · intro i l v; rw [Set.indicator_of_notMem (show x∉pie R i from fun g=>Set.disjoint_left.mp (Ember.clears v) g h|>False.elim)] -- tune
 simp
lemma void_f (h:∀ k:Site N,x∉pie R k)(F:Site N→Peb): apr F R x=0:=sum_eq_zero fun i _=>Set.indicator_of_notMem (h _) _
lemma pea (h:0<R)(i:Site N): volume (pie R i)= ENNReal.ofReal ((R*2*pinch N)^4):=by
 unfold pie; rw [← Measure.map_apply (by fun_prop : Measurable fun x:Gaia=>R⁻¹ • x) (cell_meas i),Measure.map_addHaar_smul volume (show R⁻¹≠0 by positivity),Measure.smul_apply,cellCore]
 simp only [smul_eq_mul]; simp only [show Module.finrank ℝ Gaia=4 by simp [Stationary.Gaia,Axis], inv_pow, inv_inv, abs_of_nonneg (pow_nonneg h.le _)]
 have hp:=pinch_pos N; rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
lemma polar_m (F:Site N→Peb)(p:0<R): (∫ x:Gaia,apr F R x)= (R*2*pinch N)^4 • (∑ i,F i):=by
 unfold apr; rw [integral_finsetSum, Finset.smul_sum]; apply sum_congr rfl; intro i _; rw [integral_indicator (pies _ _),setIntegral_const,Measure.real,pea p i,ENNReal.toReal_ofReal (by have he:=pinch_pos N; positivity)]
 intro i _; apply (integrable_indicator_iff (pies _ _)).2 (integrableOn_const ?_); rw [pea p i]; finiteness
lemma Yard.cells{S:ℕ→Side}{R:ℕ→ℝ}(h:Yard S R) : ∀ᵐ x:Gaia, ∀ᶠ i in atTop,∃ k:Site (S i), x∈ pie (R i) k :=by
 have ht(i): ∀ᵐ x:Gaia, (R i)⁻¹ • x∈ Stationary.boundsEarth →∃ k:Site (S i),x∈pie (R i) k:=by
    filter_upwards [Measure.quasiMeasurePreserving_smul (volume (α:=Gaia)) (inv_ne_zero (h.pos i).ne')|>.ae (canopy (h.even i))] with x e; intro p; change ∃ k:Site (S i), (R i)⁻¹ • x ∈ cellH k; exact Set.mem_iUnion.mp (Eq.mpr e p)
 filter_upwards [ae_all_iff.mpr ht] with x hx; filter_upwards [h.high.eventually (eventually_ge_atTop ‖x‖)] with i e; apply hx i ∘ Stationary.orbs; rw [norm_smul,Real.norm_of_nonneg (by have he:=h.pos i; positivity : 0 ≤ (R i)⁻¹)]; change ‖x‖≤R i at e; exact (mul_le_mul_of_nonneg_left e (inv_nonneg.mpr (h.pos i).le)).trans_eq (inv_mul_cancel₀ (h.pos i).ne') -- tune
lemma peerF(p q:Gaia):inner ℝ p q=∑ i,p i*q i:=by rw [PiLp.inner_apply]; apply sum_congr rfl; intro; intro; simp only [RCLike.inner_apply]; ring_nf; rfl -- tune
lemma cartR(s:Offset N)(z:Cover)(h:0<R)(k:Site N): charK s k z=burn (riseX R z) (R • moor (glen s k)):=by
 rw [burn,peerF,Complex.ofReal_sum]; unfold charK mode; congr 2; apply sum_congr rfl; intro i _; change (↑(glen s k i):ℂ)*_=↑(((z i:ℝ)/R)*(R*glen s k i)); push_cast; have he:(R:ℂ)≠0:=(by exact_mod_cast h.ne'); field_simp
-- scaled fields
def sled(s:Offset N)(F:Site N→Peb)(z:Cover)(R:ℝ)(k:Site N):Peb:= R⁻¹ •(charK s k z • F k)
lemma boon(s:Offset N)(A:Site N→Peb)(p:0<R)(z:Cover): bore s R z A=cartWeight • (∫ x,apr (sled s A z R) R x):=by
 rw [polar_m _ p]; unfold sled; rw [← Finset.smul_sum,smul_smul,smul_smul]; unfold bore; congr 1; unfold pinch Stationary.cartWeight; have hp:=nPos N; field_simp
lemma sot(A:Site N→Peb)(R:ℝ): AEStronglyMeasurable (apr A R) volume:=by let F(i:Site N):=(pie R i).indicator (fun _=>A i); rw [show apr A R=∑ i,F i by ext1 i; exact (Finset.sum_apply _ _ _).symm]; exact Finset.aestronglyMeasurable_sum (Finset.univ:Finset (Site N)) (fun i _=>(show AEStronglyMeasurable (fun _:Gaia => A i) volume from aestronglyMeasurable_const).indicator (pies R i))
end YM.CF.Onyx
