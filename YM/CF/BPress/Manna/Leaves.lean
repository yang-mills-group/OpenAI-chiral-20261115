import YM.CF.BPress.Huon.Cream
/-! single block cost incl normalization change & uniform counting. -/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Manna
open Function Finset NormedSpace MeasureTheory Measure Filter Metric Lattice Wilson Branch LocalH Cube Lat SU Skye Port Locale Sugar Wealth Weave House Scree Precision Pressure Next.SectorChange RG Push.SectorMeasure Crew RG.PathData Grid Honey Recipe Peel
open scoped Topology BigOperators Classical YM.CF.BPress.Vesper Matrix Matrix.Norms.Frobenius InnerProductSpace ENNReal
attribute [local instance] Gauge.frobInner
variable {N: Side}{B:BandWidth}{A:Bands (More N) B} {R:Hangar (More N)}{H:Crew A}
open Huon Rates Env
/-- entire block measure cost (including $p_o^{-1}$). count independent. $K$. -/
def areaB (R:Hangar (More N)) := (2:ℝ)*10^(R.L.val^3)
def spent (u:Realm B N R):Prop:= ∃ i:Patio R,(u.1 i).1
def curious (u:Realm B N R):Prop:= ∃ j:Fin 5,j≠0∧ u.1=House.background R j
lemma leaves : MeasurableSet {u:Realm B N R|spent u}:= measurable_fst ((Set.to_countable _).measurableSet (s:={u:Bank R|∃ i,(u i).1}))
lemma care : MeasurableSet {u:Realm B N R|curious u}:=measurable_fst ((Set.to_countable {x:Bank R|∃ j:Fin 5,j≠0∧ x=House.background R j}).measurableSet)
variable {y:ℝ} (z:Fast y) (r:1/2≤ paysP (B:=B) R y)
include r z
lemma pay_f : 0 < paysP (B:=B) R y:= (half_pos zero_lt_one).trans_le r
lemma exposure (S:Set (Realm B N R))(h:MeasurableSet S): (hotM (B:=B) R y).real S ≤ 2*((Training R B y).real S):=by
 let p:=paysP (B:=B) R y; let T:= Training R B y; have hx :0<p:= pay_f z r; unfold hotM hit Measure.real; rw [Measure.smul_apply, smul_eq_mul,Measure.restrict_apply h,ENNReal.toReal_mul,ENNReal.toReal_ofReal (inv_pos.mpr hx).le]; apply mul_le_mul (le_trans (inv_anti₀ (half_pos zero_lt_one) r) (by norm_num)) (measureReal_mono (μ:=T) Set.inter_subset_left (measure_ne_top T S)) (by positivity) zero_le_two -- tune ν
omit r z
lemma AreaPos (R:Hangar (More N)):1≤ areaB R:=by unfold areaB; exact one_le_mul_of_one_le_of_one_le (one_le_two) (one_le_pow₀ (by norm_num))
private lemma bankC : (House.count (Bank R)).real Set.univ=(10:ℝ)^(R.L.val^3):=by unfold Measure.real; rw [Measure.count_apply_finite _ Set.finite_univ]; simp [Bank,Emblem,Patio] -- tune simp
include r z
lemma cap_area : (hotM (B:=B) R y).real Set.univ≤areaB R:=by
 haveI:= summerP (B:=B) R z; refine (exposure z r _ MeasurableSet.univ).trans_eq (?_ ); rw [Training, show (Set.univ:Set (Realm B N R))=Set.univ×ˢ Set.univ from by simp, measureReal_prod_prod]; rw [bankC,probReal_univ,mul_one]; rfl
lemma slim : (hotM (B:=B) R y).real {x|curious x} ≤8:=by
 let W (j : Fin 5):= ({House.background R j}:Set (Bank R)) ×ˢ (Set.univ : Set (Attire (B:=B) R)); have he:{x:Realm B N R|curious x}⊆⋃ j: {i:Fin 5//i≠0}, W j.1:=by -- psigma? Prop use subtype
    rintro x ⟨j,v,h⟩; exact Set.mem_iUnion.mpr ⟨⟨j,v⟩,h,Set.mem_univ _⟩
 let ν:=hotM (B:=B) R y; let M:=Training R B y; haveI:= summerP (B:=B) R z; have ht (j): ν.real (W j) ≤ 2:=by
    apply (exposure z r _ ((measurableSet_singleton _).prod MeasurableSet.univ)).trans_eq; rw [measureReal_prod_prod,probReal_univ,mul_one]; simp [Measure.real,House.count] -- tune
 apply (measureReal_mono he).trans; apply (measureReal_iUnion_fintype_le _).trans; refine (sum_le_sum (fun i _=> ht i.val)).trans_eq ?_; rw [sum_const,nsmul_eq_mul]; norm_num [Fintype.card_subtype_compl] -- tune
lemma caption : (hotM R y).real {x: Realm B N R | ¬cooled R y x.2} ≤ areaB R* HumCost B.D R.L.val y:=by
 let K:={x:Attire (B:=B) R|cooled R y x}; change (hotM R y).real (Prod.snd ⁻¹' Kᶜ) ≤ _; let V:=sunny (B:=B) R y; haveI: IsProbabilityMeasure V:=summerP R z; apply (exposure z r _ (measurable_snd (cooled_flag _ _).compl)).trans; rw [show Prod.snd ⁻¹' Kᶜ=(Set.univ×ˢ Kᶜ:Set (Realm B N R)) from by ext; simp]; unfold Training areaB; rw [measureReal_prod_prod, measureReal_compl (μ:=V) (cooled_flag ..), probReal_univ (μ:=V), ← payday,bankC, mul_assoc]; gcongr; exact salary R y z -- tune
end YM.CF.BPress.Manna
