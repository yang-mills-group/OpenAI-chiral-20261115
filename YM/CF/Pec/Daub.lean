import YM.CF.Pec.Cairo
set_option autoImplicit false
noncomputable section
namespace YM.CF.Pec
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n:Side}{Z:Type}[NormedAddCommGroup Z][InnerProductSpace ℝ Z]
def central(i:Axis)(f:Site n→Z)(x:Site n):= (1/2:ℝ) • (f (x+step i)- f (x-step i))
lemma skewCenter(i j:Axis)(f:Site n→Z): central i (central j f)=central j (central i f):=by funext x; unfold central; rw [smul_sub _ (f _) (f _), smul_sub _ (f _) (f _), smul_sub _ (f _) (f _), smul_sub _ (f _) (f _)]; apply congrArg; rw [add_right_comm x, show x+step i-step j=x-step j+step i by abel, show x+ step j-step i=x-step i+step j by abel, sub_right_comm x]; abel
lemma senseE (f g:Site n→Z)(i: Axis): ∑ x, inner ℝ (central i f x) (g x)= -(∑ x,inner ℝ (f x) (central i g x)):=by
 unfold central; simp_rw [real_inner_smul_left, real_inner_smul_right, inner_sub_left, inner_sub_right, ←mul_sum, sum_sub_distrib]
 rw [show (∑ x:Site n,inner ℝ (f (x+step i)) (g x))=∑ x:Site n,inner ℝ (f x) (g (x-step i)) from ?_, show (∑ x:Site n, inner ℝ (f (x-step i)) (g x))=∑ x:Site n,inner ℝ (f x) (g (x+step i)) from ?_]; ring
 · conv_rhs=> rw [← Equiv.sum_comp (Equiv.addRight (-step i: Site n))]
   apply sum_congr rfl; intro x _; change _=inner ℝ (f (x+ -step i)) (g (x+ -step i+step i)); simp [sub_eq_add_neg]
 conv_rhs => rw [← Equiv.sum_comp (Equiv.addRight (step i:Site n))]
 apply sum_congr rfl; intro x _; change _=inner ℝ (f (x+step i)) (g (x+step i-step i)); rw [add_sub_cancel_right]
def centaur(A:Axis→Site n→Z)(x:Site n):Hue Z:=fun i j=> central i (A j) x-central j (A i) x
lemma centaur_anti(A:Axis→Site n→Z)(x:Site n)(i j): centaur A x i j= -centaur A x j i:=by unfold centaur; abel
lemma roots_r(P:Case)(F:Hue Z)(h:∀ i j,F i j= -F j i): (hum P F F).re= priceC P*∑ p:PlaqAxes, ‖F p.val.1 p.val.2‖^2:=by
 rw [stretch P F F h h]; simp_rw [Complex.re_sum, Complex.smul_re,smul_eq_mul]; rw [Finset.mul_sum]; refine sum_congr rfl ?_; intro x _; rw [sum_eq_single x]; swap; intro i _ hi; rw [vanishC P x i (Ne.symm hi),mul_zero]; swap; simp
 rw [tallyC,real_inner_self_eq_norm_sq,mul_comm]
lemma twinE (A:Axis→Axis→ℝ)(f:∀ i j,A i j=A j i)(p:∀ i,A i i=0): 2* (∑ i:PlaqAxes,A i.val.1 i.val.2)= ∑ i:Axis, ∑ j:Axis,A i j:=by
 let s:= fun x:Axis×Axis=>A x.1 x.2
 let F(i j):= if i<j then A i j else 0
 have he(i j): A i j= F i j+ F j i:=by
    rcases lt_trichotomy i j with h|h|h; · rw [show F i j=_ from if_pos h, show F j i=0 from if_neg (not_lt_of_ge h.le),add_zero]
    · subst j; simp [F,p]
    rw [show F i j=0 from if_neg (not_lt_of_ge h.le),show F j i=_ from if_pos h,zero_add,f]
 have ht: (∑ i:Axis,∑ j:Axis,F i j)=∑ i:PlaqAxes,s i.val:=by
    rw [← Fintype.sum_prod_type']; -- tune
    let G:=univ.filter fun x:Axis×Axis=>x.1<x.2
    have hz : G=univ.image (fun x:PlaqAxes=>x.val):=by
       ext i; refine ⟨fun e=>mem_image.mpr ⟨⟨i,(mem_filter.mp e).2⟩,mem_univ _,rfl⟩,fun h=>?_⟩; obtain ⟨x,_,rfl⟩:=mem_image.mp h; exact mem_filter.mpr ⟨mem_univ _,x.property⟩
    rw [← Finset.sum_filter]; change ∑ i∈G,s i= _; rw [hz, sum_image (fun a _ b _=>Subtype.ext)] -- tune
 conv_rhs => arg 2; intro i; arg 2; intro j; rw [he]
 simp_rw [sum_add_distrib]; rw [sum_comm (f:=fun i j:Axis=>F j i),ht,two_mul]
lemma plume(P:Case)(A:Axis→Site n→Z): ∑ x:Site n,(hum P (centaur A x) (centaur A x)).im=0:=by
 let T(x):=centaur A x; let D(i j):=central i (A j); let X(i j k l):= (crystalC P i j k l).im; let U(x i j k l):= inner ℝ (T x i j) (T x k l) * X i j k l; let V(x i j k l):= inner ℝ (D i j x) (T x k l) * X i j k l; let W(x i j k l):=inner ℝ (D i j x) (D k l x) * X i j k l
 have hx(i j k l):X i j k l= - X j i k l∧ X i j k l= - X i j l k:=⟨congrArg Complex.im (ascL P i j k l).1,congrArg Complex.im (ascL P i j k l).2⟩
 have he(x i j k l):U x i j k l=V x i j k l + V x j i k l:=by unfold U V; change inner ℝ (_-_) _*_=_+ _; rw [inner_sub_left,sub_mul, (hx j i k l).1]; ring -- tune
 have hv(x i j k l):V x i j k l=W x i j k l+ W x i j l k:=by unfold V W; change inner ℝ _ (_ - _) *_= _+_; rw [inner_sub_right,sub_mul,(hx i j l k).2]; ring
 have hs(x): (hum P (T x) (T x)).im=∑ i:Axis,∑ j:Axis,∑ k:Axis,∑ l:Axis,W x i j k l:=by
    rw [stretch P (T x) (T x) (centaur_anti A x) (centaur_anti A x)]
    simp_rw [Complex.im_sum, Complex.smul_im,smul_eq_mul]; -- shape
    have hook(f v:Axis→ Axis→ℝ)(h:∀ i j,v i j=f i j+f j i)(p:∀ i,v i i=0):∑ i:PlaqAxes,v i.val.1 i.val.2=∑ i:Axis,∑ j:Axis,f i j:=by
       have he:= twinE v (fun i j=> (h i j).trans ((add_comm ..).trans (h j i).symm)) p; conv_rhs at he=> arg 2; intro i; arg 2; intro j; rw [h]
       simp_rw [sum_add_distrib] at he; rw [sum_comm (f:=fun i j:Axis=>f j i)] at he; linarith
    let P'(i j):=∑ k:PlaqAxes,V x i j k.val.1 k.val.2
    let q(i j):=∑ k:PlaqAxes,U x i j k.val.1 k.val.2
    change (∑ k:PlaqAxes,q k.val.1 k.val.2)= _; rw [hook P' q]; swap
    · intro i j; unfold q P'; simp_rw [he]; exact Finset.sum_add_distrib
    swap; · intro i; unfold q; apply sum_eq_zero; intro k _; unfold U; simp [T,centaur]
    refine sum_congr rfl fun i _=> ?_; refine sum_congr rfl fun j _=>?_; exact hook (W x i j) (V x i j) (hv x i j) (fun k=>by simp [V,T,centaur]) -- syntaxes
 have ht(i j k l): (∑ x,W x i j k l)= -(∑ x,W x k j i l):=by
    have he:X i j k l= -X k j i l:=swap_im ..
    unfold W D; simp only [←sum_mul]; rw [senseE,senseE] -- both? tune
    rw [he, skewCenter]; ring
 let F(i j k l):=∑ x,W x i j k l
 have heq : ∑ x:Site n,∑ i:Axis,∑ j:Axis,∑ k:Axis, ∑ l:Axis,W x i j k l= ∑ j:Axis,∑ l:Axis,∑ i:Axis,∑ k:Axis, F i j k l:=by
    rw [Finset.sum_comm (s:=(univ:Finset (Site n)))]; conv_rhs=>
        arg 2; intro j; rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm];
    refine sum_congr rfl fun i _=>?_ ; rw [Finset.sum_comm (s:=(univ:Finset (Site n)))]; refine sum_congr rfl fun j _=> ?_; rw [Finset.sum_comm (s:=(univ:Finset (Site n)))]; conv_rhs => rw [Finset.sum_comm]
    refine sum_congr rfl fun k _=> ?_; rw [Finset.sum_comm (s:=(univ:Finset (Site n)))]
 change (∑ x: Site n,(hum P (T x) (T x)).im)=_; simp_rw [hs]; rw [heq]; apply sum_eq_zero; intro i _; apply sum_eq_zero; intro j _
 have hg : ∑ k:Axis,∑ l:Axis,F k i l j = -(∑ k:Axis,∑ l:Axis, F k i l j) :=by
    conv_rhs=> rw [Finset.sum_comm]
    simp only [←Finset.sum_neg_distrib]; refine sum_congr rfl fun k _=> ?_; exact sum_congr rfl fun i' _=> ht _ _ _ _
 linarith
end YM.CF.Pec
