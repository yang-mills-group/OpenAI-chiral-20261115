import Organdy.Mistral
set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Organdy
open Finset
variable {I V:Type}[Fintype I][DecidableEq I][AddCommGroup V][Module ℝ V]


abbrev Ink (I:Type):=I→I→ℂ
namespace Ink
def gilt (A: Ink I)(y:I→ℝ):ℂ:= ∑ i,∑ j,A i j*((y i:ℂ)*(y j:ℂ))
def qty (A: Ink I):ℝ:=∑ i,∑ j,‖A i j‖
abbrev Sym (A:Ink I) := ∀ i j,A i j=A j i
abbrev Within (A:Ink I)(S:Finset I) := ∀i j,A i j≠0→i∈S∧j∈S

lemma qty_nonneg (A:Ink I):0≤A.qty:=by unfold qty; positivity

lemma same {A: Ink I}{y z:I→ℝ}{M:Finset I}(h:A.Within M)(v:∀i∈M,y i=z i):
  A.gilt y=A.gilt z:=by
   unfold gilt
   apply sum_congr rfl;intro i _;apply sum_congr rfl;intro j _
   by_cases u:A i j=0
   · simp [u]
   rw [v i (h i j u).1,v j (h i j u).2]

abbrev Paint (i:Type) :=EuclideanSpace ℝ i
variable {c:ℝ}(Q:V→ₗ[ℝ]V→ₗ[ℝ]ℂ)(R:V→ₗ[ℝ]Paint I)(pc:0≤c)
 (s:∀ x y,Q x y=Q y x)
 (h:∀ x, ‖Q x x‖≤c*‖R x‖^2)
include h s
lemma polar (x y:V):
 4*‖Q x y‖≤c*‖R (x+y)‖^2+c*‖R (x-y)‖^2:=by
 have e:(4:ℂ)*Q x y=Q (x+y) (x+y)-Q (x-y) (x-y):=by
    simp only [map_add,map_sub,LinearMap.add_apply,LinearMap.sub_apply,s x y]
    ring
 rw [←show ‖(4:ℂ)‖=4 by norm_num, ←norm_mul,e]
 exact (norm_sub_le ..).trans (add_le_add (h _) (h _))

lemma polar_zero (x y:V)(p:R x=0) : Q x y=0:=by
 by_contra q
 let z:= ‖Q x y‖
 have b:0<z:= norm_pos_iff.mpr q
 let k:=2*|c| *‖R y‖^2
 have e:0<1+k:=by positivity
 let a:=(1+k)/z
 have u:=polar _ _ s h (a•x) y
 rw [map_add,map_sub,map_smul R,p,smul_zero,zero_add,zero_sub,norm_neg,map_smul Q, LinearMap.smul_apply,norm_smul,Real.norm_eq_abs,
   abs_of_pos (div_pos e b)] at u
 change 4*(a*z) ≤ _ at u
 rw [show a*z=1+k from div_mul_cancel₀ _ b.ne'] at u
 unfold k at u e
 linarith [mul_le_mul_of_nonneg_right (le_abs_self c) (sq_nonneg ‖R y‖)]
lemma polar_eq (x y:V)(p:R x=R y): Q x x=Q y y:=by
 have e(u:V):Q x u=Q y u:=
   sub_eq_zero.mp ((show Q x u-Q y u=Q (x-y) u by simp).trans
      (polar_zero _ _ s h _ _ (show R (x-y)=0 by rw [map_sub,p,sub_self])))
 rw [e,s y x,e]

include pc
lemma polar_small (x y:V)(p:‖R x‖≤1)(q:‖R y‖≤1): ‖Q x y‖ ≤ 2*c:=by
  have a:‖R (x+y)‖^2 ≤ 2^2:=by
     rw [map_add];exact pow_le_pow_left₀ (norm_nonneg _) ((norm_add_le ..).trans (by linarith)) 2
  have b:‖R (x-y)‖^2 ≤ 2^2:=by
     rw [map_sub];exact pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le ..).trans (by linarith)) 2
  linarith [polar _ _ s h x y, mul_le_mul_of_nonneg_left a pc, mul_le_mul_of_nonneg_left b pc]

lemma pigment : ∃A: Ink I, Sym A ∧ (∀i j, ‖A i j‖≤2*c) ∧
   ∀x,Q x x=A.gilt (R x):=by
 let F:=EuclideanSpace.basisFun I ℝ
 let K:=LinearMap.range R
 let P:Paint I→ₗ[ℝ]Paint I:=K.subtype.comp (K.orthogonalProjectionOnto.toLinearMap)
 have hp(x:V):P (R x)=R x:=by
   let y:K:=⟨R x,x,rfl⟩
   change (K.orthogonalProjectionOnto (y:Paint I)).val=y.val
   simp
 have e(i):∃v:V, R v=P (F i):=(K.orthogonalProjectionOnto (F i)).property
 choose y e using e
 have u(i): ‖R (y i)‖ ≤ 1:= (e i).symm ▸ (K.norm_orthogonalProjectionOnto_apply_le _).trans_eq (F.orthonormal.1 i)
 refine ⟨fun i j=>Q (y i) (y j), fun i j=>s ..,fun i j=>polar_small Q R pc s h _ _ (u i) (u j),fun x=>?_⟩
 have g:∑ i,(R x i) • F i= R x := F.sum_repr _
 have f:R x=R (∑ i,R x i • y i):=by

   have b:P (R x)=R x:=hp _
   nth_rw 1 [←g] at b
   rw [map_sum] at b ⊢
   simp_rw [map_smul] at b ⊢
   simp_rw [e]; exact b.symm
 rw [polar_eq Q R s h _ _ f]
 unfold gilt
 simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply, Complex.real_smul, Finset.mul_sum]
 rw [sum_comm]
 apply sum_congr rfl;intro i _;apply sum_congr rfl;intro j _
 ring

lemma sepia (M:Finset I)
 (u:∀x i,i∉ M→ R x i=0) :
 ∃ A:Ink I,Sym A ∧ Within A M ∧ qty A ≤ (M.card:ℝ)^2*(2*c) ∧
  ∀ x,Q x x=A.gilt (R x):=by
 obtain ⟨A,t,p,y⟩:=pigment Q R pc s h
 let B:Ink I:=fun i j=> if i∈ M then if j∈M then A i j else 0 else 0
 refine ⟨B,?_,?_,?_,?_⟩
 · intro i j;by_cases e:i∈M
   · by_cases a:j∈M <;> simp [B,e,a,t i j]
   · simp [B,e]
 · intro i j w
   by_contra! q
   by_cases a:i∈M
   · exact w (by simp [B,q a])
   exact w (by simp [B,a])
 · unfold B qty
   simp only [apply_ite (‖·‖),norm_zero]

   have e(x:I):
     (∑ j, if x ∈ M then if j∈M then ‖A x j‖ else 0 else 0)
    = if x ∈ M then ∑ j, (if j∈M then ‖A x j‖ else 0) else 0:=by by_cases v:x∈M <;>simp [v]
   simp_rw [e]
   rw [sum_ite_mem];simp only [sum_ite_mem,univ_inter]
   refine (sum_le_sum (fun i (_:i∈M)=>sum_le_sum (fun j (_:j∈M)=>p i j))).trans_eq ?_
   simp [nsmul_eq_mul,pow_two,mul_assoc]
 intro x
 rw [y]
 unfold gilt B
 apply sum_congr rfl;intro i _
 apply sum_congr rfl;intro j _
 by_cases e:i∈M
 · by_cases a:j∈M
   · rw [if_pos e,if_pos a]
   simp [u _ _ a]
 simp [u _ _ e]

omit h s pc
variable {J:Type} [Fintype J]
lemma within_mono {A:Ink I}{M O:Finset I}(w:A.Within M)(h:M⊆O):A.Within O:=
   fun i j a=> ⟨h (w i j a).1,h (w i j a).2⟩

lemma within_sum {M:Finset I}(s:Finset J)(A:J→Ink I)(p:∀j∈s,(A j).Within M):
    Within (∑j∈s,A j) M:=by
    intro i j h
    simp only [Finset.sum_apply] at h
    obtain ⟨k,g,q⟩:= exists_ne_zero_of_sum_ne_zero h
    exact p k g _ _ q
lemma sym_sum (s:Finset J)(A:J→Ink I)(p:∀j∈s,(A j).Sym):
    Sym (∑j∈s,A j):=by
    intro i j;simp only [Finset.sum_apply]
    exact sum_congr rfl fun k g=>p k g i j
lemma qty_sum (s:Finset J)(A:J→Ink I): qty (∑j∈s,A j) ≤ ∑j∈s,qty (A j):=by
    simp only [qty,Finset.sum_apply]
    rw [sum_comm (s:=s)]
    refine sum_le_sum (fun i _=>?_)
    rw [sum_comm (s:=s)]; exact sum_le_sum fun _ _=> norm_sum_le ..
lemma gilt_sum (s:Finset J)(A:J→Ink I)(y:I→ℝ):gilt (∑j∈s,A j) y= ∑j∈s,(A j).gilt y:=by
    simp only [gilt,Finset.sum_apply,sum_mul]
    rw [sum_comm (s:=s)]
    exact sum_congr rfl (fun _ _=> sum_comm)


lemma dye_ink (a:ℂ)(A:Ink I){M:Finset I}
 (w:A.Within M)(p:A.Sym):
 Within (a • A) M∧ Sym (a • A) ∧ qty (a • A)=‖a‖*qty A∧
   ∀y,gilt (a • A) y=a*gilt A y:=by
 refine ⟨?_,?_,?_,?_⟩
 · intro i j h;apply w; exact right_ne_zero_of_mul h
 · intro i j; simpa [p i j]
 · simp [qty,smul_eq_mul,mul_sum]
 · simp [gilt,smul_eq_mul,mul_sum,mul_assoc]
