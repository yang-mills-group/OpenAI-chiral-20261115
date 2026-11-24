import Mathlib.MeasureTheory.Integral.Pi
/-!
# Cost in total variation of normalized product law

In both counting and a priori link integrations. Bound by sum of differences
for the sparsely changing coordinates without an exponential in number of
factors. Here only need fixed compact coordinate measure and bounded continuous
densities (the inputs when fixed upper fields).
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function NormedSpace Finset MeasureTheory
open scoped Topology Classical BigOperators

section products
variable {I K X:Type*}[Fintype I][DecidableEq I](f g:I→K→ℝ)

def pairJump(k:I)(F:I→K→ℝ)(G:I→K→ℝ)(i:I)(x:K):ℝ:=if i=k then ‖F k x-G k x‖ else F i x
lemma divisible (hf:∀ i x,0≤ f i x)(k:I)(p:∀ i:I,i≠k→f i=g i)(x:I→K):
 ‖(∏ i:I,f i (x i))-(∏ i:I,g i (x i))‖=∏ i,pairJump k f g i (x i):=by
 let V:Finset I:= univ.erase k
 let s:= ∏ i∈V,f i (x i)
 have hx: (∏ i:I,f i (x i))= f k (x k)*s:= (mul_prod_erase univ _ (mem_univ k)).symm
 have he: (∏ i:I,g i (x i))= g k (x k)*s:=by
    rw [←mul_prod_erase univ (fun i=>g i (x i)) (mem_univ k)]; apply congrArg; exact prod_congr rfl fun i e=>by rw [p i (Finset.ne_of_mem_erase e)]
 have hg:(∏ i:I,pairJump k f g i (x i))= pairJump k f g k (x k)*s:=by
    rw [←mul_prod_erase univ (fun i=>pairJump k f g i (x i)) (mem_univ k)]; apply congrArg; exact prod_congr rfl fun i e=>by rw [pairJump,if_neg (Finset.ne_of_mem_erase e)]
 rw [hx,he,hg,←sub_mul,norm_mul,pairJump,if_pos rfl,Real.norm_of_nonneg (show 0≤s from Finset.prod_nonneg (fun i _=>hf i (x i)))]
variable [Fintype K]
lemma jump_sum (hf:∀ i x,0≤f i x)(a:∀i,∑ x,f i x=1)(k:I)(p:∀i,i≠k→f i=g i):
 (∑ x:I→K, ‖(∏ i,f i (x i))-(∏ i,g i (x i))‖)=∑ x,‖f k x-g k x‖:=by
 simp_rw [divisible f g hf k p]; rw [← Fintype.prod_sum]
 rw [← mul_prod_erase univ (fun i=>∑ x,pairJump k f g i x) (mem_univ k)]
 have h:(∏ i∈univ.erase k,∑ x,pairJump k f g i x)=1:= prod_eq_one (fun i e=>by simp [pairJump,Finset.ne_of_mem_erase e,a i])
 rw [h]; simp only [mul_one,pairJump,if_true]

lemma discursive (hf:∀i x,0≤f i x)(hg:∀i x,0≤g i x)(a:∀i,∑ x,f i x=1)(v:∀i,∑ x,g i x=1)(T:Finset I)(p:∀i,i∉T→ f i=g i):
 (∑ x:I→K, ‖(∏ i,f i (x i))-(∏ i,g i (x i))‖)≤∑ i∈T,∑ x,‖f i x-g i x‖:= by
 induction T using Finset.induction_on generalizing g with
 | empty=> simp [show f=g from funext (fun i=>p i (by simp))]
 | insert i t h ih=>
    let H(j:I):= if j=i then g j else f j
    -- compare f→H then H→g; induction needs f variable instead of g. instead replace g at i with f there, induction f to that.
    let R(j:I):= if j=i then f j else g j
    have hx(j x):0≤R j x:=by unfold R; split; exact hf _ _; exact hg _ _
    have ha(j):∑ x,R j x=1:=by unfold R; split; exact a j; exact v j
    have e:∀ j, j∉t→ f j=R j:=by intro j w; unfold R; split; rfl; next h=> exact p _ (by simpa using And.intro h w)
    let V(y:I→K→ℝ)(x:I→K):= ∏ i:I,y i (x i)
    have he(j)(h':j∈t):R j=g j:=if_neg (by intro e; exact h (e ▸ h'))
    have ht:∀ j,j≠i→R j=g j:=fun j v=> if_neg v
    have pp:(∑ j∈t,∑ x:K,‖f j x-R j x‖)=∑ j∈t,∑ x:K, ‖f j x-g j x‖:= sum_congr rfl fun i g=>by rw [he i g]
    have h₂:R i=f i:=if_pos rfl
    calc
     _ ≤ ∑ x:I→K,(‖V f x-V R x‖ + ‖V R x-V g x‖):= Finset.sum_le_sum fun i _=>norm_sub_le_norm_sub_add_norm_sub (V f i) (V R i) _
     _ = (∑ x,‖V f x-V R x‖)+(∑ x,‖V R x-V g x‖):= sum_add_distrib
     _≤(∑ j∈t,∑ x:K,‖f j x-R j x‖)+(∑ x:K,‖R i x-g i x‖):= add_le_add (ih R hx ha e) (jump_sum R g hx ha i ht|>.le)
     _= _:=by rw [pp,h₂,sum_insert h,add_comm]

end products
section continuous
variable {I K:Type*}[Fintype I][DecidableEq I][MeasurableSpace K](μ:Measure K)[IsProbabilityMeasure μ]
variable [TopologicalSpace K][CompactSpace K][T2Space K][BorelSpace K][SecondCountableTopology K](f g:I→K→ℝ)(hf:∀i x,0≤ f i x)(hg:∀i x,0≤g i x)(c:∀i,Continuous (f i))(d:∀i,Continuous (g i))(a:∀i, ∫ x,f i x∂μ=1)(v:∀i, ∫ x,g i x∂μ=1)
local notation "Vμ" => Measure.pi (fun (_:I)=>μ)
include a hf
lemma jump_int (k:I)(p:∀i,i≠k→f i=g i):
 (∫ x:I→K, ‖(∏ i,f i (x i))-(∏ i,g i (x i))‖∂Vμ)=∫ x,‖f k x-g k x‖∂μ:=by
 simp_rw [divisible f g hf k p]; rw [integral_fintype_prod_eq_prod]
 rw [← mul_prod_erase univ (fun i=>∫ x,pairJump k f g i x∂μ) (mem_univ k)]
 have h:(∏ i∈univ.erase k,∫ x,pairJump k f g i x∂μ)=1:= prod_eq_one (fun i e=>by simp [pairJump,Finset.ne_of_mem_erase e,a i])
 rw [h]; simp only [mul_one,pairJump,if_true]
include hg c d v
lemma sparse_int (s:Finset I)(p:∀i,i∉s→ f i=g i):
 (∫ x:I→K, ‖(∏ i,f i (x i))-(∏ i,g i (x i))‖∂Vμ)≤∑ i∈s,∫ x,‖f i x-g i x‖∂μ:= by
 induction s using Finset.induction_on generalizing g with
 | empty=> simp [show f=g from funext (fun i=>p i (by simp))]
 | insert i t h ih=>
    let R(j:I):= if j=i then f j else g j
    have hx(j x):0≤R j x:=by unfold R; split; exact hf _ _; exact hg _ _
    have ha(j):∫ x:K,R j x∂μ=1:=by unfold R; split; exact a j; exact v j
    have hc(j):Continuous (R j):=by unfold R; split; exact c j; exact d j
    have e:∀ j, j∉t→ f j=R j:=by intro j w; unfold R; split; rfl; next h=> exact p _ (by simpa using And.intro h w)
    let V(y:I→K→ℝ)(x:I→K):= ∏ i:I,y i (x i)
    have he(j)(h':j∈t):R j=g j:=if_neg (by intro e; exact h (e ▸ h'))
    have ht:∀ j,j≠i→R j=g j:=fun j v=> if_neg v
    have pp:(∑ j∈t,∫ x:K,‖f j x-R j x‖∂μ)=∑ j∈t,∫ x:K, ‖f j x-g j x‖∂μ:= sum_congr rfl fun i g=>by rw [he i g]
    have h₂:R i=f i:=if_pos rfl
    have v(F:I→K→ℝ)(hf:∀i,Continuous (F i)): Continuous (V F):= continuous_finsetProd _ (fun i _=> (hf i).comp (continuous_apply i)) -- name
    have q{F G:I→K→ℝ}(p:∀i,Continuous (F i))(g:∀i,Continuous (G i)):Integrable (fun x:I→K=> ‖V F x-V G x‖) Vμ:= ((v F p).sub (v G g)|>.norm).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    calc
     _ ≤ ∫ x:I→K,(‖V f x-V R x‖ + ‖V R x-V g x‖)∂Vμ:= integral_mono (q c d) ((q c hc).add (q hc d)) fun i=>norm_sub_le_norm_sub_add_norm_sub (V f i) (V R i) _
     _ = (∫ x,‖V f x-V R x‖∂Vμ)+(∫ x,‖V R x-V g x‖∂Vμ):= integral_add (q c hc) (q hc d)
     _ ≤(∑ j∈t,∫ x:K,‖f j x-R j x‖∂μ)+(∫ x:K,‖R i x-g i x‖∂μ):= add_le_add (ih R hx hc ha e) (jump_int μ R g hx ha i ht|>.le)
     _= _:=by rw [pp,h₂,sum_insert h,add_comm]
end continuous
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.sparse_int
