import Mathlib

/-!
# L1 prices for local determining op-densities. Not assuming existence of any point fields in
spacetime. Implementation towards estimate on the reconstruction in input link arrays.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 12000
set_option maxHeartbeats 450000
noncomputable section
namespace YM.PaymentCamera
open Function Filter Metric NormedSpace MeasureTheory Set
open scoped Topology ENNReal NNReal InnerProductSpace Classical
variable (X:Type*)(E:Type*) [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- all input costs at a fixed gauge Stencil use literal bounded functions -/ 
def players : Submodule ℂ (X→ℂ) where
 carrier := {f| Measurable f ∧ ∃ C:ℝ,∀ x, ‖f x‖ ≤ C}
 zero_mem' := ⟨(show Measurable (fun _:X=> (0:ℂ)) from measurable_const),0,fun _=> norm_zero.le⟩
 add_mem' := fun {x y} ⟨p,C,h⟩ ⟨q,D,t⟩=> ⟨p.add q,C+D,fun u=>(norm_add_le (x u) (y u)).trans (add_le_add (h _) (t _))⟩
 smul_mem' := fun a x ⟨p,C,h⟩=> ⟨p.const_mul a,‖a‖*C,fun u=> (norm_mul (a:ℂ) (x u)|>.le).trans (mul_le_mul_of_nonneg_left (h _) (norm_nonneg _))⟩
abbrev Test := ↥(players X)
variable {X E}
lemma Test.meas (x:Test X) : Measurable x.val:= x.property.1
lemma Test.bounds (x:Test X) : ∃ C:ℝ,∀ i,‖x.val i‖≤C:= x.property.2
variable (μ:Measure X)[IsFiniteMeasure μ]
lemma Test.cost (x:Test X) (p:ℝ≥0∞) : MemLp x.val p μ:=by
 obtain ⟨C,h⟩:=x.bounds; exact (memLp_const C).mono' x.meas.aestronglyMeasurable (Eventually.of_forall h)
lemma Test.finances (x:Test X): Integrable x.val μ:= memLp_one_iff_integrable.mp (x.cost μ 1)
omit [IsFiniteMeasure μ] in
noncomputable def sample {A:Set X}(h: MeasurableSet A)(z:ℂ): Test X := ⟨A.indicator (fun _=> z), measurable_const.indicator h, ‖z‖,fun x=>by by_cases e:x∈A <;> simp [*,norm_nonneg]⟩
noncomputable def seat (p:ℝ≥0∞) : Test X →ₗ[ℂ] Lp ℂ p μ where
 toFun x:= (x.cost μ p).toLp _
 map_add' _ _:= MemLp.toLp_add ..
 map_smul' _ _:= MemLp.toLp_const_smul ..
lemma sample_seat (p:ℝ≥0∞){A:Set X}(h:MeasurableSet A)(z:ℂ): seat μ p (sample h z) = indicatorConstLp p h (measure_ne_top μ A) z := rfl
lemma seats_supply (p:ℝ≥0∞)[Fact (1 ≤ p)](hp:p≠ ⊤) : DenseRange (seat μ p):=by
 let L:= (seat μ p).range.topologicalClosure; change ∀ i, i∈ (closure (Set.range (seat μ p)))
 refine Lp.induction (μ:=μ) hp (fun i=> i∈ L) ?_ ?_ ?_
 · intro c A h v; rw [Lp.simpleFunc.coe_indicatorConst]; exact subset_closure (⟨sample h c,sample_seat μ p h c⟩ : _ ∈ (seat μ p).range)
 · intro _ _ _ _ _ a b; exact L.add_mem a b
 exact (LinearMap.range (seat μ p)).isClosed_topologicalClosure
noncomputable def bill (x:Test X):ℝ:= ‖seat μ 1 x‖
lemma bill_nonneg (x:Test X): 0≤bill μ x:=norm_nonneg _
lemma bill_eq (x:Test X): bill μ x= ∫ i, ‖x.val i‖∂μ:= L1.norm_of_fun_eq_integral_norm (x.finances μ)
@[simp] lemma bill_scale (x:Test X)(z:ℂ): bill μ (z • x)=‖z‖*bill μ x:=by simp only [bill,map_smul,norm_smul]
@[simp] lemma bill_zero: bill μ 0=0:=by simp only [bill,map_zero,norm_zero]
@[simp] lemma bill_zone{A:Set X}(h:MeasurableSet A): bill μ (sample h 1)= μ.real A:=by
 rw [bill,sample_seat,norm_indicatorConstLp one_ne_zero]; simp; simp
noncomputable def squareCap:ℝ := ((μ Set.univ)^((1:ℝ)-2⁻¹)).toReal
lemma cap_square (x:Test X):bill μ x≤ squareCap μ* ‖seat μ 2 x‖:=by
 change ‖(x.cost μ 1).toLp _‖ ≤ squareCap μ * ‖(x.cost μ 2).toLp _‖
 rw [Lp.norm_toLp,Lp.norm_toLp,squareCap,mul_comm, ←ENNReal.toReal_mul]; apply ENNReal.toReal_mono
 · exact ENNReal.mul_ne_top (x.cost μ 2).2.ne (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top μ _))
 convert eLpNorm_le_eLpNorm_mul_rpow_measure_univ (show (1:ℝ≥0∞) ≤ 2 by norm_num) (x.meas.aestronglyMeasurable (μ:=μ)) using 1 <;> norm_num

end YM.PaymentCamera
#print axioms YM.PaymentCamera.cap_square
#print axioms YM.PaymentCamera.seats_supply
