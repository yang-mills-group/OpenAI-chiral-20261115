import YM.CF.Cadre.Motte
import YM.CF.Cadre.Dash
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
open PowerSeries
abbrev PS:= PowerSeries ℝ
abbrev cent(F:PS):Prop:=∀ i:ℕ,0 ≤ coeff i F
abbrev mintL (i:ℕ)(x:ℝ)(F:PS):=∑ j∈ range (i+1),x^j*coeff j F
variable {i j:ℕ}{P Q R:PS}{x:ℝ}(p: cent P)(q:cent Q)(hx:0 ≤ x)
namespace cent
lemma plus (p:cent P)(q:cent Q):cent (P+Q):= fun _=>by rw [map_add]; exact add_nonneg (p _) (q _)
lemma sip(p:cent P)(q:cent Q):cent (P*Q):=fun _=>by rw [coeff_mul]; exact sum_nonneg fun i _=>mul_nonneg (p i.1) (q i.2)
lemma unit : cent 1:=fun i=> by rw [coeff_one]; split<;>norm_num
lemma scaleL {x:ℝ}(p:cent P)(h:0 ≤ x):cent (x • P):=fun _=> by rw [coeff_smul]; exact mul_nonneg h (p _)
lemma negℜ(p:cent P)(x:ℝ)(t:0 ≤ x)(i:ℕ): 0 ≤ mintL i x P:=sum_nonneg fun i _=>mul_nonneg (pow_nonneg t _) (p _)
lemma multi {ι: Type*}(S:Finset ι)(f:ι→PS)(p:∀ i∈S,cent (f i)):cent (∏ i∈S,f i):=by
 induction S using Finset.induction_on with
 |empty=>rw [prod_empty]; exact unit
 |insert i S g ih=> rw [prod_insert g]; exact sip (p _ (mem_insert_self ..)) (ih fun j q=> p j (mem_insert_of_mem q))
lemma kind (p:cent P)(h:i ≤ j) (u:0 ≤ x):mintL i x P ≤ mintL j x P:=sum_le_sum_of_subset_of_nonneg (by intro d w; rw [mem_range] at w ⊢; omega) (fun i _ _=>mul_nonneg (pow_nonneg u _) (p _))
lemma lead (F:PS)(i:ℕ)(x:ℝ) : HasDerivAt (fun x=> mintL (i+1) x F) (mintL i x (derivative ℝ F)) x:=by
 let R(j:ℕ)(z:ℝ):=z^j*coeff j F; let L(j:ℕ):ℝ:=j*x^(j-1)*coeff j F; have he(j):HasDerivAt (R j) (L j) x:=by have h:HasDerivAt (R j) ((j*x^(j-1)*1)*coeff j F) x:=(((hasDerivAt_id' x).pow j).mul_const (coeff j F)); simpa only [L,mul_one] using h
 change HasDerivAt (fun x=> ∑ j∈ range (i+2),R j x) _ _
 have ht: (∑ j∈ range (i+2),L j)=mintL i x (derivative ℝ F):=by rw [sum_range_succ',show L 0=0 from (by simp [L]), add_zero]; refine sum_congr rfl fun j _=>?_ ; unfold L; rw [coeff_derivative]; push_cast; ring
 rw [← ht]; exact HasDerivAt.fun_sum fun i _=>he i -- check
lemma tend (i:ℕ)(p:cent P)(q:cent Q)(g:0 ≤ x):mintL i x (P*Q) ≤ mintL i x P*mintL i x Q:=by
 let T:=range (i+1); let V(j:ℕ×ℕ):=(x^j.1*coeff j.1 P)*(x^j.2*coeff j.2 Q); let k(j:ℕ):=antidiagonal j
 unfold mintL; rw [sum_mul_sum]; have hp(j:ℕ):x^j*coeff j (P*Q)=∑ t∈k j,V t:= by rw [coeff_mul,mul_sum]; refine sum_congr rfl fun d h=>?_ ; unfold V; have hx:= mem_antidiagonal.mp h; rw [←hx,pow_add]; ring
 simp_rw [hp]; rw [← sum_biUnion]; swap; · intro i j k l u; exact disjoint_left.mpr fun y h v=> u ((mem_antidiagonal.mp h).symm.trans (mem_antidiagonal.mp v))
 rw [← sum_product']; refine sum_le_sum_of_subset_of_nonneg ?_ (fun i h _=>?_) -- tune decides
 · intro n h; obtain ⟨j,v,h⟩:= mem_biUnion.mp h; have hx:=mem_antidiagonal.mp h; rw [mem_range] at v; rw [mem_product]; simp only [mem_range]; omega
 exact mul_nonneg (mul_nonneg (pow_nonneg g _) (p _)) (mul_nonneg (pow_nonneg g _) (q _))
lemma finite {ι:Type*} (S:Finset ι)(P:ι→PS)(p:∀ i∈S,cent (P i))(hx:0 ≤ x)(i:ℕ):mintL i x (∏ j∈S,P j) ≤∏ j∈S,mintL i x (P j):=by
 induction S using Finset.induction_on with
 |empty=> rw [prod_empty,prod_empty]; unfold mintL; simp_rw [coeff_one, mul_boole]; simp
 |insert j S g ih=> rw [prod_insert g,prod_insert g]; have hp(k)(q:k∈ S):=p k (mem_insert_of_mem q); have he:=p j (mem_insert_self ..); exact (tend _ he (multi S P hp) hx).trans (mul_le_mul_of_nonneg_left (ih hp) (negℜ he x hx _))
end cent
-- homogeneous terms nonempty ≥ consumed parent.
abbrev fizz (X Y:ΣA)(T: Finset A)(V:ΣA→ Finset A→PS)(z:ℝ): PS:= z • ∑ G∈drum X Y T ∩ farW A,∏ j∈G,V j (T∩ j.val) -- import Cadre.Coral? Motte imports Clear
variable {K: Palot.leaf A→ Finset A→ PS}(k:∀ X:Palot.leaf A,∀ D ⊆ X.val,cent (K X D))
include hx k
include hx k
lemma reprice(X:ΣA)(z:ℝ)(v:0 ≤ z):mintL i x (fizz X Y O K z) ≤ z * blast X Y (farW A) (fun i' D=>mintL i x (K i' D)) O:=by
 unfold mintL fizz; simp_rw [coeff_smul,map_sum,smul_eq_mul, mul_left_comm _ z]; -- tune
 rw [← mul_sum]; apply mul_le_mul_of_nonneg_left; swap; exact v
 simp_rw [mul_sum]; rw [sum_comm]; exact sum_le_sum fun G _=> cent.finite G _ (fun j _=> k _ _ inter_subset_right) hx i -- tune
omit hx k
lemma car_k(V:PS)(i:ℕ):mintL i 0 V=coeff 0 V:=by unfold mintL; rw [sum_eq_single 0]; simp; intro j _ hj; rw [zero_pow hj,zero_mul]; simp
end YM.CF.Cadre
