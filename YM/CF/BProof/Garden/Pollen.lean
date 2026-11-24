import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.Pi
import YM.CF.BProof.Garden.Cache
/-! Auxiliary normalized phases Y, Z for the same complex integrand. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Garden
open Function Filter Fock NormedSpace Finset MeasureTheory Lattice Lat Spin Tulip
open scoped Topology Matrix MatrixOrder InnerProductSpace Kronecker BigOperators Matrix.Norms.L2Operator ENNReal ComplexConjugate
attribute [local instance] opCStarAlgebra
variable {I:Type*}[Fintype I][DecidableEq I]
abbrev YPhase:= AddCircle (1:ℝ)
abbrev Pollen (I:Type*) := I → YPhase
def glow := (fourier 1:C(YPhase,ℂ))
@[simp] lemma glow_p(i:YPhase): ‖glow i‖=1:=by rw [glow,fourier_one]; simp
abbrev gold(I:Type*)[Fintype I]:Measure (Pollen I):=Measure.pi (fun _=> AddCircle.haarAddCircle)
instance : IsProbabilityMeasure (gold I):=by unfold gold; infer_instance
def style (S:Finset I)(f:Pollen I):ℂ:= ∏ i∈S,glow (f i)
@[simp] lemma style_zero(f:Pollen I): style ∅ f=1:=prod_empty
lemma style_one (S:Finset I)(f:Pollen I): ‖style S f‖=1:=by simp [style,norm_prod]
@[fun_prop] lemma style_cont(S:Finset I) : Continuous (style S):= by unfold style; fun_prop
lemma tokens(S:Finset I)(f:Pollen I): style S f= ∏ i:I, fourier (if i∈S then 1 else 0) (f i):=by rw [← prod_subset (subset_univ S) (by intro x _ hx; rw [if_neg hx,fourier_zero])]; exact prod_congr rfl fun i hi=> by rw [if_pos hi]; rfl
lemma poppy(S T:Finset I): (∫ f, star (style S f)*style T f ∂gold I)=if S=T then 1 else 0:=by
 let k(U:Finset I)(i:I):ℤ:=if i∈U then 1 else 0; let L(i:I)(p:YPhase):ℂ:= fourier (-k S i) p * fourier (k T i) p; have he(f:Pollen I):star (style S f)*style T f=∏ i:I,L i (f i):=by rw [tokens,tokens,star_prod, ←prod_mul_distrib]; unfold L; apply prod_congr rfl; intro i _; rw [fourier_neg]; rfl
 have hp(i:I):(∫ p,L i p ∂AddCircle.haarAddCircle)=if k S i=k T i then 1 else 0:= by
   change fourierCoeff (T:=1) (fourier (k T i)) (k S i)=_; rw [fourierCoeff_fourier]; by_cases e:k S i=k T i<;>simp [e,Pi.single_apply]
 simp_rw [he]; unfold gold; rw [integral_fintype_prod_eq_prod L]; simp_rw [hp]; by_cases h:S=T; simp [h]; rw [if_neg h]; have ht:∃ i:I,k S i≠ k T i:=by by_contra! v; apply h; ext i; have he:=v i; by_cases p:i∈S <;> by_cases g:i∈T<;>simp [p,g,k] at * -- tune
 obtain ⟨i,x⟩:=ht; exact prod_eq_zero (mem_univ i) (if_neg x)
lemma monet (f:Pollen I){S T:Finset I}(h:Disjoint S T) : style (S∪ T) f =style S f *style T f:=prod_union h
variable {N:Side}
def optional (ε:ℂ)(y:Pollen (Site N))(J:Plant N):Plant N:=1+(fun i=>ε*glow (y i)) • J
lemma fluffy (ε:ℂ)(y:Pollen (Site N))(P:Plant N)(S:Support N): (optional ε y P).prod S=∑ i∈S.powerset,(ε^i.card*style i y) • P.prod i:=by
 induction S using Finset.induction_on with
 | empty=> simp
 | insert x S h ih=>
   let f(i:Support N) :=(ε^i.card*style i y) • P.prod i; have he(i:Support N)(g:i⊆S) : f (insert x i)=(ε*glow (y x)) • (P.leaf x * f i):=by
      have ht:x∉i:=fun w=> h (g w); unfold f; rw [card_insert_of_notMem ht,P.prod_insert ht,Algebra.mul_smul_comm,smul_smul,style,prod_insert ht]; congr 1; rw [pow_succ']; unfold style; ring
   rw [Plant.prod_insert _ h,ih, show (optional ε y P).leaf x=1+(ε*glow (y x)) • P.leaf x from rfl, add_mul,one_mul, Finset.sum_powerset_insert h]; -- tune
   simp only [mul_sum,Algebra.smul_mul_assoc]; congr 1; exact sum_congr rfl fun i hi=>(he i (mem_powerset.mp hi)).symm
lemma ion(Y:Wave (Single N))(ε:ℂ)(y:Pollen (Site N))(P:Plant N)(S:Support N)(R:Wave (Single N)) : inner ℂ Y (acts ((optional ε y P).prod S) R)=∑ i∈S.powerset,style i y * (ε^i.card * inner ℂ Y (acts (P.prod i) R)):=by simp only [fluffy,act_sum,inner_sum,act_smul,inner_smul_right]; exact sum_congr rfl fun _ _=>by ring
lemma cIntegrable {D E:Type*}[TopologicalSpace D][CompactSpace D][MeasurableSpace D][OpensMeasurableSpace D][NormedAddCommGroup E]{μ:Measure D}[IsFiniteMeasure μ]{f:D→E}(h:Continuous f): Integrable f μ:= h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
lemma issue (ε:ℂ)(e:ε≠0)(P:Plant N)(S: Support N)(Y R: Wave (Single N)): (∫ f, ((ε⁻¹)^S.card*star (style S f))*inner ℂ Y (acts ((optional ε f P).prod S) R) ∂gold (Site N))=inner ℂ Y (acts (P.prod S) R):=by
 simp_rw [ion,mul_sum]; let W:=fun (i:Support N)(f:Pollen (Site N))=>((ε⁻¹)^S.card*star (style S f))*(style i f * (ε^i.card * inner ℂ Y (acts (P.prod i) R))); have hp(i:Support N):(∫ f,W i f ∂gold (Site N))= (if S=i then 1 else 0)*((ε⁻¹)^ S.card* (ε^i.card * inner ℂ Y (acts (P.prod i) R))):=by
   let v:= ε^i.card * inner ℂ Y (acts (P.prod i) R); rw [show W i=(fun f=>star (style S f)*style i f*(ε⁻¹^S.card*v)) from (funext fun w=> (by unfold W v; ring)),integral_mul_const,poppy]
 change (∫ f, ∑ i∈S.powerset,W i f ∂gold (Site N))=_; rw [integral_finsetSum]; simp_rw [hp,ite_mul,one_mul,zero_mul]; rw [sum_ite_eq, if_pos (mem_powerset_self _),←mul_assoc, ←mul_pow,inv_mul_cancel₀ e,one_pow,one_mul]; intro i _; apply cIntegrable; unfold W; fun_prop
end YM.CF.BProof.Garden
