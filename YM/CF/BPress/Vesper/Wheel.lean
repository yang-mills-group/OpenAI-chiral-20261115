import YM.CF.BPress.Vesper.Forges
import YM.CF.BPress.Law
/- VolumeB-phase Fourier projections, normalized on circle as complex unit group. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Vesper
open Function Filter NormedSpace MeasureTheory Finset Lattice Branch Push.AbsoluteSums Palmer Fock Pastry Pine Pf
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
open Cube Lat SU Spin Spin.Paint Chalk Lily Skye Scree Branch Tenant DoughBag Tulip Dial --
variable {I:Type}[Fintype I][DecidableEq I]
scoped instance : MeasurableSpace Circle:= borel _
scoped instance : BorelSpace Circle:= ⟨rfl⟩
abbrev Wheel(I:Type):= I→Circle
namespace Wheel
open Measure
abbrev circleLaw := haarMeasure (G:=Circle) ⊤ -- Top?)
instance : IsProbabilityMeasure circleLaw:= ⟨haarMeasure_self⟩
abbrev coin (I:Type)[Fintype I]:= Law.chain circleLaw I
def ζ (T:Finset I)(Z:Wheel I):ℂ:= ∏ i∈T, (Z i:ℂ)
lemma ζ_price (T:Finset I)(Z:Wheel I): ‖ζ T Z‖=1:=by simp [ζ,norm_prod]
lemma ζ_full (T:Finset I)(Z:Wheel I): ζ T Z≠0:=norm_ne_zero_iff.mp ((ζ_price T Z).symm ▸ one_ne_zero) -- tune
lemma ζ_C(T:Finset I):Continuous (ζ T):= continuous_finsetProd _ (fun i _=> Continuous.comp (show Continuous (fun x:Circle=>(x:ℂ)) from continuous_subtype_val) (continuous_apply i)) -- tune
lemma ζ_mul (T:Finset I)(x y:Wheel I): ζ T (x*y)=ζ T x*ζ T y:=by simp only [ζ,Pi.mul_apply,Circle.coe_mul,prod_mul_distrib]
variable (X:Wheel I)
private def Rχ(i:I):Wheel I:= fun j=> if i=j then -1 else 1
private lemma ζ_off(T:Finset I){i:I}(h:i∉T): ζ T (Rχ i)=1:=by apply prod_eq_one; intro j v; simp only [Rχ,Ne.symm (ne_of_mem_of_not_mem v h), ite_false, Circle.coe_one]
private lemma ζ_on (T: Finset I){i:I}(p:i∈T): ζ T (Rχ i)= -1:=by nth_rw 1 [←insert_erase p]; rw [ζ,prod_insert (notMem_erase i T), show (∏ j∈T.erase i, (Rχ i j:ℂ))=1 from ζ_off (T.erase i) (notMem_erase i T)]; simp [Rχ]
def κF (T S:Finset I)(u:Wheel I):ℂ:= (ζ S u)⁻¹ * ζ T u
lemma κ_c(T S:Finset I): Continuous (κF T S):=((ζ_C S).inv₀ (ζ_full S)).mul (ζ_C T) -- tune
private lemma turn {g:Wheel I}(t:Wheel I→ℂ)(p:Continuous t)(v:∀x:Wheel I,t (g*x)= - t x):∫ x,t x ∂coin I=0:=by
 have hm :MeasurePreserving (fun x:Wheel I=>g*x) (coin I) (coin I):= measurePreserving_pi _ _ (f:=fun i (x:Circle)=> g i*x) (fun i=>measurePreserving_mul_left _ _); have ht := Law.restore _ _ _ hm t (p.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace t)); simp_rw [v] at ht; rw [integral_neg] at ht; exact add_self_eq_zero.mp (eq_neg_iff_add_eq_zero.mp ht)
lemma ortho (T S:Finset I): ∫ x:Wheel I,κF T S x∂coin I= if T=S then 1 else 0:=by
 split; next h=> subst T; simp [κF,ζ_full]
 next h=> by_cases p:T ⊆ S
          · obtain ⟨i,q,v⟩:= not_subset.mp (fun v=>h (Subset.antisymm p v)); apply turn (g:=Rχ i) _ (κ_c T S); intro x; unfold κF; rw [ζ_mul,ζ_mul,ζ_on S q,ζ_off T v]; simp
          obtain ⟨i,v,q⟩:= not_subset.mp p; apply turn (g:=Rχ i) _ (κ_c T S); intro x; unfold κF; rw [ζ_mul,ζ_mul,ζ_on T v,ζ_off S q]; simp
-- price transport with scalars
lemma order_f {J:Type*}(p:Finset J)(T:J→Finset I)(S:Finset I)(f:J→ℂ): ∫ x,(ζ S x)⁻¹ * (∑ i∈p, ζ (T i) x*f i)∂coin I=∑ i∈p,if T i=S then f i else 0:=by
 simp_rw [mul_sum,←mul_assoc (ζ S _)⁻¹]; rw [integral_finsetSum]; swap; · intro i _; exact ((κ_c (T i) S).mul (continuous_const (y:=f i))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
 apply sum_congr rfl; intro i v; rw [integral_mul_const]; change (∫ x:Wheel I, κF (T i) S x∂coin I)*_= _; rw [ortho]; split <;> simp
end Wheel
end YM.CF.BPress.Vesper
