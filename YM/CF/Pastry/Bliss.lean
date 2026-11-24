import YM.CF.Pastry.Pie

/-! Scalar part and effective cloud, transport as-is. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Pastry
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Function Fock Finset NormedSpace Petal Branch
attribute [local instance] opCStarAlgebra
variable {n m : Type*} [LinearOrder n] [Fintype n] [LinearOrder m] [Fintype m]
lemma zero_poke : (1:Dough n)≠0 := fun h=> one_ne_zero (show (1:FC n)=0 from congrArg Subtype.val h)
lemma rise_ne (x:Dough n) : exp x≠0 := by
  letI : NormedAlgebra ℚ (Dough n):= NormedAlgebra.restrictScalars ℚ ℝ (Dough n)
  intro h; have H:=isUnit_exp x; rw [h] at H; obtain ⟨y,v⟩:=H; have he:=y.inv_val; rw [v,mul_zero] at he; exact zero_poke he.symm
lemma hullB (z:ℂ) : pane (hollow (n:=n) z)=z := by change (z • (1:FC n)) ∅ ∅=z; simp
lemma hull_sum (A B : Dough n) : pane (A+B)=pane A+pane B := rfl
lemma pane_f {I : Type*} (A: Finset I) (f : I→Dough n) : pane (∑ i∈A,f i)=∑ i∈A,pane (f i) := map_sum (panHom n) .. -- tune
lemma cookH (z:ℂ) (v : Poly n m) : v.cook (hollow z)=z • 1 := by change v.eval (z • (1:FC n))= _; rw [map_smul,v.eval_one]
lemma paneExp (x:Dough n) : pane (exp x)=Complex.exp (pane x) := by
  letI : NormedAlgebra ℚ (Dough n):= NormedAlgebra.restrictScalars ℚ ℝ (Dough n)
  rw [Complex.exp_eq_exp_ℂ]; exact map_exp (panHom n) ((panHom n).toLinearMap.continuous_of_finiteDimensional) _
lemma expReal (v : Poly n m) (z:ℂ) (x:Dough n) : v.cook (exp (hollow z + x))=Complex.exp z • exp (v.cook x) := by
  letI : NormedAlgebra ℚ (Dough n):= NormedAlgebra.restrictScalars ℚ ℝ (Dough n)
  letI : NormedAlgebra ℚ (FC m):= NormedAlgebra.restrictScalars ℚ ℂ (FC m)
  let f : ℂ→+* FC m:= algebraMap ℂ _
  have he t : f t=t • 1 := Algebra.algebraMap_eq_smul_one _
  have hp : Continuous f := by apply continuous_iff_continuousAt.mpr; intro x; have H : (f:ℂ→FC m)=fun x=>x • 1 := funext he; rw [H]; exact continuousAt_id.smul continuousAt_const
  rw [exp_add,map_mul,v.rising,v.rising,cookH,←he,←map_exp f hp,he,Algebra.smul_mul_assoc,one_mul,Complex.exp_eq_exp_ℂ]
lemma actReal (A : FC n) (c : ℝ) (z : Wave n) : acts (c•A) z=c • acts A z := by
  have he : c•A=(c:ℂ) • A := by ext i j; simp [Complex.real_smul]
  rw [he,act_smul]; exact Complex.coe_smul _ _ -- tune
lemma cloudClose (i : Finset n) (v:Dough n) (g : v∈stretch i) : cloudless v∈ stretch i := (stretch i).sub_mem g ((stretch_ok _).mpr (Flour.grainE.smul _))
lemma convCloud : Continuous (cloudless (n:=n)) := by
  have he : Continuous (hollow (n:=n)) := Continuous.subtype_mk (continuous_id.smul continuous_const) _
  let F := fun x:Dough n=>hollow (n:=n) (pane x)
  have hp : Continuous F:= he.comp ((mast_cont (n:=n)).comp continuous_subtype_val)
  exact continuous_id.sub hp
open MeasureTheory
lemma hinge {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} (F : Dough n →L[ℝ] ℂ) {φ : Y→ Dough n} (h : Integrable φ μ) : ∫ x,F (φ x) ∂μ=F (∫ x,φ x ∂μ) := by
  exact ContinuousLinearMap.integral_comp_comm (𝕜:=ℝ) (E:=↥(Dough n)) (Fₗ:=ℂ) F h
lemma eyeReal (a : FC n) (c : ℝ) (u x : Wave n) : inner ℂ u (acts a (c • x)) = c • inner ℂ u (acts a x) := by
  rw [←Complex.coe_smul, map_smul, inner_smul_right,Complex.real_smul]
end YM.CF.Pastry
