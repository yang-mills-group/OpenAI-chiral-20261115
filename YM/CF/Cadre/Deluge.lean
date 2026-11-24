import YM.CF.Pastry.Bliss
import YM.CF.Cadre.Grain
import YM.CF.Sault.Gilt
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Cadre
open Function Filter Topology Lattice Finset Palot
open scoped Classical
variable {A:Type*}[Fintype A][DecidableEq A]
local notation "ΣA"=> Palot.leaf A
local notation "ΣG"=> hook A
variable (Y:Palot.leaf A)(D O:Finset A)(F:hook A)
-- P supports meeting kernel leaf Y
open Fock Pastry Sault PowerSeries
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
attribute [local instance] opCStarAlgebra
variable {I:Type*}[LinearOrder I][Fintype I](W: leaf A→ Finset I)(K: leaf A→ FC I)(R: Palot.leaf A→ PowerSeries (Dough I))
local notation "ℊ"=>PowerSeries (Dough I)
variable (C:Palot.leaf A→ Palot.leaf A→ Finset (Palot.leaf A)→ PowerSeries (Dough I))(e:∀ X:leaf A,derivative (Dough I) (R X)=∑ Y:leaf A,∑ F∈ drum X Y (O∩X.val), C X Y F)
variable (η:∀ X Y:leaf A,∀ G∈drum X Y (O∩X.val),∀ i:ℕ,(coeff i (C X Y G)).val=Sault.rind (K Y * (coeff i (∏ t∈G,R t)).val))
variable (ω:∀ X:leaf A,Fock.Sector (W X) false (K X)) (t:∀ X Y:leaf A,Disjoint X.val Y.val→ Disjoint (W X) (W Y))(hU:∀ X i, Flour (W X) (coeff i (R X)).val)
-- Ω snapshot.Converge clean Φ, Ψ.P.Press shift. avoid nonnormal derivatives.
section
variable {B:Type*}[NormedCommRing B][CompleteSpace B]
abbrev Aqua (P:PowerSeries B):Prop:= Summable fun i:ℕ=> ‖coeff i P‖
abbrev hitU (P:PowerSeries B):= ∑' i:ℕ,coeff i P
namespace Aqua
variable {P Q:PowerSeries B}
lemma sip(p:Aqua P)(h:Aqua Q):Aqua (P+Q)∧hitU (P+Q)=hitU P+hitU Q:=by
 refine ⟨Summable.of_nonneg_of_le (fun _=>norm_nonneg _) (fun i=> (by rw [map_add]; exact norm_add_le ..)) (p.add h),?_⟩; simp only [hitU,map_add, p.of_norm.tsum_add h.of_norm]
lemma soar(p:Aqua P)(h:Aqua Q): Aqua (P*Q) ∧hitU (P*Q)=hitU P*hitU Q:=by
 unfold Aqua hitU; simp_rw [coeff_mul]; refine ⟨Summable.of_nonneg_of_le (fun _=>norm_nonneg _) ?_ (summable_norm_sum_mul_antidiagonal_of_summable_norm p h),?_⟩; intro i; exact le_rfl; exact (tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm p h).symm
lemma ψ_p {Y:Type*}(F:Finset Y)(Q:Y→PowerSeries B)(p:∀ i∈F,Aqua (Q i)):Aqua (∑ i∈F,Q i) ∧ hitU (∑ i∈F,Q i)=∑ i∈F,hitU (Q i):=by
 induction F using Finset.induction_on with
 |empty=> simp [Aqua,hitU]
 |insert i F g ih=> rw [sum_insert g,sum_insert g]; obtain ⟨q,l⟩:=ih fun i y=>p i (mem_insert_of_mem y); obtain ⟨u,k⟩:=(p i (mem_insert_self ..)).sip q; rw [←l]; exact ⟨u,k⟩
lemma ψ_m {Y:Type*}(F:Finset Y)(Q:Y→PowerSeries B)(p:∀ i∈F,Aqua (Q i)):Aqua (∏ i∈F,Q i) ∧ hitU (∏ i∈F,Q i)=∏ i∈F,hitU (Q i):=by
 induction F using Finset.induction_on with
 |empty=> simp only [prod_empty]; unfold hitU Aqua; simp_rw [coeff_one]; constructor; exact summable_of_ne_finset_zero (s:={0}) (fun i h=> (by rw [if_neg (show i≠0 by simpa using h),norm_zero])); rw [tsum_eq_single 0]; simp; intro b u; simp [u]
 |insert i F g ih=> rw [prod_insert g,prod_insert g]; obtain ⟨q,l⟩:=ih fun i y=>p i (mem_insert_of_mem y); obtain ⟨u,k⟩:=(p i (mem_insert_self ..)).soar q; rw [←l]; exact ⟨u,k⟩
end Aqua
end
abbrev levT(T:ℊ):Wave I:=acts (hitU T).val (vacuum _)
def ere(A:FC I)(x:Wave I):= acts A x
def pea : Dough I→L[ℝ]Wave I:=LinearMap.toContinuousLinearMap (LinearMap.mk (AddHom.mk (fun x:Dough I=>acts x.val (vacuum I)) (fun x y=> act_add ..)) (fun c x=>Pastry.actReal (x.val) c (vacuum I))) -- tune erasure extra
lemma radT {m:Type*}[LinearOrder m][Fintype m](f:Wave I→L[ℂ]Wave m)(Q:FC m)(T:ℊ)(v:Aqua T)(q:∀ i,f (pose (derivative (Dough I) T) i)=acts Q (f (pose T i)))(i:ℕ): (↑i+1:ℂ) • f (pose T (i+1))=acts Q (f (pose T i)):=by
    let V:=coeff (i+1) T; have hl:(↑i+1:↥(Dough I))* V= (i+1:ℕ) • V:=by rw [nsmul_eq_mul]; push_cast; rfl
    change _=acts Q (f (pose T i)); rw [←q]; change _=f (acts (coeff i (derivative (Dough I) T)).val _); rw [coeff_derivative,mul_comm,hl]; change (↑i+1:ℂ) • f (acts V.val (vacuum I))= f (acts ((Dough I).val ((i+1:ℕ) • V)) (vacuum I)); rw [map_nsmul,←Nat.cast_smul_eq_nsmul ℂ,act_smul,map_smul]; push_cast; rfl
lemma hart {m:Type*}[LinearOrder m][Fintype m](Q:FC m)(S:ℕ→ Wave m)(he:∀ i:ℕ,(↑i+1:ℂ) • S (i+1)=acts Q (S i))(i:ℕ): S i=acts ((i.factorial:ℂ)⁻¹ • Q^i) (S 0):=by
 let L(i:ℕ):=(i.factorial:ℂ)⁻¹ • Q^i; suffices ∀ i,S i=acts (L i) (S 0) from this _; intro i
 induction i with
 |zero=>simp [L]
 |succ i ih=>
    apply smul_right_injective _ (show (↑i+1:ℂ)≠0 by exact_mod_cast Nat.succ_ne_zero i) -- tune
    change (↑i+1:ℂ) • S (i+1)= _ ; dsimp only; rw [he,ih,←act_mul]; simp only [L,Nat.factorial_succ,Algebra.mul_smul_comm,act_smul]; rw [← pow_succ',smul_smul]; push_cast; congr 1; field_simp
lemma loft {m:Type*}[LinearOrder m][Fintype m](f:Wave I→L[ℂ]Wave m)(Q:FC m)(T:ℊ)(v:Aqua T)(q:∀ i,f (pose (derivative (Dough I) T) i)=acts Q (f (pose T i))) : f (levT T)= acts (NormedSpace.exp Q) (f (pose T 0)):=by
 let L(i:ℕ):=(i.factorial:ℂ)⁻¹ • Q^i; let S(i:ℕ):=f (pose T i); have ht(i:ℕ):S i=acts (L i) (S 0):=hart Q S (radT f Q T v q) i
 let Z:= (f.restrictScalars ℝ).comp pea; have hu(t:ℊ): f (levT t)=Z (hitU t):=rfl; have hl(Z:FC m):acts Z (S 0)=ere Z (S 0):=rfl
 let Y:FC m→ₗ[ℂ] Wave m:= ⟨⟨fun A=> acts A (S 0), fun A B=> act_add ..⟩,fun z A=> act_smul ..⟩; let D:=Y.toContinuousLinearMap
 rw [hu, hitU,Z.map_tsum v.of_norm]; change ∑' i,S i= D (NormedSpace.exp Q); rw [congrFun (NormedSpace.exp_eq_tsum ℂ) Q]; rw [D.map_tsum]; swap; · exact (NormedSpace.norm_expSeries_summable' (𝕂:=ℂ) Q).of_norm
 exact tsum_congr fun i=>ht i
end YM.CF.Cadre
