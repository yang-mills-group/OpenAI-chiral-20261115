import YM.SU5.Reconstruction.UVPrice.Backline
/-!
# For spectra decompose. Automatic real-energy projection identification. Also Clasp with registrations even without light-positivity
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Roy
open Function Set Filter MeasureTheory Spectral Analysis Metric InnerProductSpace
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace
open YM.Multiplier Chirp CrossedFrame OS Semigroup Boundary Probe CF.Buffered.Afterglow.Tower MeshClock Germ SelectionAnalysis ConePrice Real Picket
variable {H : Hilbert} {a b : Axis} (S : OS.Semigroup H a)
local notation "D₁" => {i:Axis//i≠a}
local notation "P" => S.ℚmeasure
local notation "μ" x:max=> (P).diagonal x
-- multiplier E in the PVM (opa)
noncomputable def favor (a : Axis) (t:ℝ≥0) (p:E4):ℝ := exp (-(t:ℝ)*max 0 (p a))
@[fun_prop] lemma favorC (t:ℝ≥0): Continuous (favor a t):= by unfold favor; fun_prop
lemma favorL (t:ℝ≥0)(p:E4): 0 < favor a t p ∧ favor a t p≤1:=⟨exp_pos _, Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos_of_nonneg t.property) (le_max_left ..))⟩
lemma costT (t:ℝ≥0): Registers S.ℚmeasure (fun p=> (favor a t p:ℂ)) (S.E t) := by
 refine ⟨⟨by fun_prop,1, zero_le_one,fun x=> by simpa [Complex.norm_real,Real.norm_of_nonneg (favorL _ _).1.le] using (favorL t x (a:=a)).2⟩,?_⟩
 intro x
 let he:=ConePrice.damped S x t 0
 rw [S.uZero,ContinuousLinearMap.id_apply] at he
 refine he.trans ?_
 apply integral_congr_ae; filter_upwards [shelf_ae S x] with y hy
 unfold favor; rw [Complex.ofReal_exp,max_eq_right (shelf_ePays S _ hy)]
 -- push simp eval
 simp only [Submodule.coe_zero, plane,inner_zero_right,Complex.ofReal_zero,zero_mul,Complex.exp_zero,one_mul,Complex.ofReal_neg,Complex.ofReal_mul,mul_assoc,Complex.I_mul_I]
 congr 1; ring
lemma costU (s:Cross a): Registers S.ℚmeasure (fun p=> plane p s.val) (S.U s):=by rw [← ConePrice.translation]; exact story S s.val
-- projection to shelf at 0.
def toe (a:Axis):Set E4:= {p:E4| p a=0}
noncomputable def cue: H.Op:= S.ℚmeasure.region (toe a)
lemma toe_meas: MeasurableSet (toe a):=(isClosed_eq (show Continuous fun p:E4=>p a by fun_prop) continuous_const).measurableSet
lemma toe_pays: Registers S.ℚmeasure ((toe a).indicator 1) (cue S):= Registers.box _ toe_meas
-- through emerging all real
lemma truth (x:H) : Tendsto (fun t=> S.E t x) atTop (𝓝 (cue S x)):= by
 refine Registers.tends atTop _ _ (toe_pays S) (costT S) x 1 (Eventually.of_forall fun t=> Eventually.of_forall fun y=>?_) ?_
 · rw [Complex.norm_real, Real.norm_of_nonneg (favorL _ _).1.le]; exact (favorL _ _).2
 filter_upwards [shelf_ae S x] with y v
 by_cases h:y a=0
 · rw [indicator_of_mem (show y∈ toe a from h)]
   simp [favor,h]
 rw [indicator_of_notMem (show y∉ toe a from h)]
 let F(t:ℝ):= -t * (y a); have ht:= lt_of_le_of_ne (shelf_ePays S _ v) (Ne.symm h)
 have he: Tendsto (fun t:ℝ≥0=> F t) atTop atBot:= ((tendsto_neg_atTop_atBot (G:=ℝ)).atBot_mul_const ht).comp (NNReal.tendsto_coe_atTop.mpr tendsto_id)
 unfold favor; rw [max_eq_right ht.le]; simpa only [Function.comp_def,Complex.ofReal_zero] using (Complex.continuous_ofReal.continuousAt (x:=0)).tendsto.comp (Real.tendsto_exp_atBot.comp he)
lemma cue_ground: cue S=S.orth:= by ext1 x; exact tendsto_nhds_unique (truth S x) (S.emerges x)
lemma cue_project: IsStarProjection (cue S):= ⟨show ((P).region (toe a)).comp ((P).region (toe a))=_ from by rw [(P).joins toe_meas toe_meas, Set.inter_self]; rfl, (P).real toe_meas⟩
lemma zero_μ (x:H): ∀ᵐ p ∂ (P).diagonal (cue S x), p∈Beneath S 0:= by
 have he : ∀ᵐ p ∂ (P).diagonal (cue S x),p∈toe a:= by rw [cue,ConePrice.restrictP S toe_meas]; exact ae_restrict_mem toe_meas
 filter_upwards [shelf_ae S (cue S x),he] with y v h; exact ⟨v, (show y a=0 from h).le⟩
end YM.Roy
