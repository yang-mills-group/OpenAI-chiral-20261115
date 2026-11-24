import YM.CF.Urn.Glass
set_option autoImplicit false
noncomputable section
namespace YM.CF.Urn
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Proa
variable {I Y G D:Type*}[Fintype I][Fintype Y][DecidableEq I][DecidableEq Y][TopologicalSpace D]
variable {X:Stage Y I D G}{L:License D}{s t u: Tag X}{F T:Raw D I}{m:ℕ}{a b x z:ℝ}
def whip(X:Stage Y I D G)(x:ℝ)(m:ℕ)(i j:I):=(1+x*X.F.span (X.home i) (X.home j))^m
lemma womb (h:0≤x)(i j k:I):whip X x m i k ≤ whip X x m i j*whip X x m j k:=by
 unfold whip; let v(i j:I):ℝ:=X.F.span (X.home i) (X.home j); have hv(i j:I): 0 ≤ v i j:= Nat.cast_nonneg _; change (1+x*v i k)^m≤_; rw [←mul_pow]; change _≤ ((1+x*v i j)*(1+x*v j k))^_; apply pow_le_pow_left₀ (by positivity)
 have he : v i k ≤ v i j+v j k:=by unfold v; exact_mod_cast X.F.tri (X.home i) (X.home j) (X.home k)
 nlinarith [mul_le_mul_of_nonneg_left he h,mul_nonneg (mul_nonneg (sq_nonneg x) (hv i j)) (hv j k)]
lemma Wh(T U:Seal Y→Toll I)(w:∀ S i j,0≤ T S i j)(q:∀ S i j,0≤ U S i j)(k: incline X m x (fun _=>a) z T)(l:incline X m x (fun _=>b) z U)(v:0 ≤ x)(t:0 ≤ z)(hp:0 ≤ b)(i:I): ∑ j:I,whip X x m i j * ∑ l: Seal Y × Seal Y,rent z (l.1∪l.2)*Branch.charge (T l.1) (U l.2) i j ≤ (2:ℝ)*(a*b):=by
 let R(i j:I):=whip X x m i j; let D(i j k:I)(P Q:Seal Y):= R i j*(Branch.rent z P*T P i j)*(R j k*(Branch.rent z Q*U Q j k))
 have he (j k:I): ∑ x:Seal Y,∑ y:Seal Y,D i j k x y=R i j*saleM z T i j*(R j k*saleM z U j k):=by simp only [D,saleM,Branch.rent,mul_sum,sum_mul]; rw [sum_comm]
 have hh(i j):0 ≤R i j:=by unfold R whip; positivity
 have hz (j:I): whip X x m i j * ∑ l: Seal Y×Seal Y,rent z (l.1∪l.2)*Branch.charge (T l.1) (U l.2) i j ≤ (2:ℝ)* ∑ k:I,R i k*saleM z T i k*(R k j* saleM z U k j):=by
    rw [Fintype.sum_prod_type]; simp_rw [Branch.charge,mul_sum, ←he, mul_sum]; rw [sum_comm (s:= (univ:Finset I))]; simp_rw [sum_comm (f:=fun (k:I) (b:Seal Y)=> (2:ℝ)*D i k j _ b)]
    apply sum_le_sum; intro P _; apply sum_le_sum; intro S _; apply sum_le_sum; intro V _
    have hr:= womb (X:=X) (m:=m) v i V j; have hx:= w P i V; have hq:= q S V j
    apply le_trans (mul_le_mul hr (mul_le_mul_of_nonneg_right (rent_join P S t) (mul_nonneg (by norm_num) (mul_nonneg hx hq))) (mul_nonneg (rent_pos ..).le (mul_nonneg (by norm_num) (mul_nonneg hx hq))) (mul_nonneg (hh i V) (hh V j))); apply le_of_eq; unfold D R; ring
 apply (sum_le_sum (fun j _=>hz j)).trans; rw [←mul_sum]; apply mul_le_mul_of_nonneg_left _ (by norm_num); rw [sum_comm]; simp_rw [←mul_sum]; apply le_trans (sum_le_sum (fun j _=>mul_le_mul_of_nonneg_left (l j) (mul_nonneg (hh i j) (sale_nn w z i j)))); rw [←sum_mul]; exact mul_le_mul_of_nonneg_right (k _) hp
lemma duo (h:Street L s t m x z (fun _=>a) F)(l:Street L t u m x z (fun _=>b) T)(v:0≤x)(t':0≤ z)(hp:0≤b):Street L s u m x z (fun _=>2*(a*b)) (fun y=> F y*T y):=by
 obtain ⟨A,W,p,r,f⟩:=h; obtain ⟨P,U,g,q,h⟩:=l
 refine mergeW (fun i: Seal Y×Seal Y=> i.1∪i.2) (fun i y=> A i.1 y * P i.2 y) (fun i=> Branch.charge (W i.1) (U i.2)) (fun i=> Suite.jointK (p _) (g _)) (fun d=>?_) (Wh W U (fun i=> (p i).nonn) (fun i=> (g i).nonn) r q v t' hp)
 rw [Fintype.sum_prod_type,f,h]; simp only [sum_mul,mul_sum]; rw [sum_comm]
lemma thinner (h:Street L s t m x z (fun _=>a) F)(v:0≤b)(ht: b ≤ x): Street L s t m b z (fun _=>a) F:=by obtain ⟨A,W,p,l,f⟩:=h; refine ⟨A,W,p,fun i=> (sum_le_sum ?_).trans (l i),f⟩; intro j _; gcongr; exact sale_nn (fun i=> (p i).nonn) z i j
end YM.CF.Urn
