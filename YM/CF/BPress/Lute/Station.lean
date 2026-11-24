import YM.CF.BPress.Lute.Oak
/- buys incl determ refs. S and Ψ. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Lute
open Function Filter NormedSpace InnerProductSpace Set Complex Fock SU SU.Pair Mesa Music Spin Spin.Paint Fort Fort.Oak
open scoped Topology ContDiff BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
namespace Kite
-- numeric controls
local notation "ωβ"=> (1/8:ℝ)
local notation "μ0"=> (1/2:ℝ)
variable {v:ℝ} {h n:ℕ}
def bound := jogger ωβ (1-ωβ)
abbrev α0:= jogger ωβ (μ0-ωβ)
abbrev β0:= jogger (μ0+ωβ) (1-ωβ)
def α:=α0∘ bound
def β:=β0∘ bound
lemma bet_f : Monotone bound:=Real.smoothTransition.monotone.comp (show Monotone (fun t:ℝ=> (t-ωβ)/(1-ωβ-ωβ)) from fun x y h=>by have hx:0 ≤ 1-ωβ-ωβ:=(by norm_num); dsimp only; gcongr) -- indent tune
lemma bet_m : bound μ0= μ0:=by
 rw [bound,jogger,show (μ0-ωβ)/(1-ωβ-ωβ)=μ0 by norm_num,inward, Real.smoothTransition]; have he := expNegInvGlue.pos_of_pos (show (0:ℝ)<μ0 from one_half_pos); rw [show 1-μ0=μ0 from by norm_num, ←two_mul]; field_simp -- tune
lemma mid_bound (u:ℝ) : bound u∈ Hotel:=jogB ..
@[simp] lemma bound_lo {u:ℝ}(p:u ≤ ωβ): bound u=0:=jog_lo (by norm_num) p
@[simp] lemma bound_hi {u:ℝ}(p:1-ωβ≤u): bound u=1:=jog_hi (by norm_num) p
@[simp] lemma alpha_hi0 {u:ℝ}(p:μ0≤u):α0 u=1:=jog_hi (by norm_num) ((sub_le_self μ0 (by norm_num)).trans p)
@[simp] lemma beta_lo0 {u:ℝ}(p:u≤ μ0):β0 u=0:=jog_lo (by norm_num) (p.trans (le_add_of_nonneg_right (by norm_num)))
lemma alpha_final {u:ℝ}(p:μ0≤u): α u=1:= alpha_hi0 ((bet_f p).trans' (le_of_eq bet_m.symm)) -- orientation
lemma beta_start {u:ℝ}(p:u≤μ0): β u=0:= beta_lo0 (le_trans (bet_f p) bet_m.le)
@[simp] lemma bounds01 : bound (0:ℝ)=0∧bound (1:ℝ)=1:=⟨bound_lo (by norm_num),bound_hi (by norm_num)⟩
@[simp] lemma α_0 : α0 0=0:=jog_lo (by norm_num) (by norm_num)
@[simp] lemma β_1 : β0 1=1:=jog_hi (by norm_num) (by norm_num)
@[simp] lemma al0 : α 0=0:=by rw [α,Function.comp_apply,bounds01.1,α_0]
@[simp] lemma al1 : α 1=1:=alpha_final (by norm_num)
@[simp] lemma be0 : β 0=0:=beta_start (by norm_num)
@[simp] lemma be1 : β 1=1:=by rw [β,Function.comp_apply,bounds01.2,β_1]
lemma al(x:ℝ): α x∈ Hotel:=jogB ..
lemma be(x:ℝ): β x∈ Hotel:=jogB ..
@[fun_prop] lemma bound_smooth : ContDiff ℝ ∞ bound:=jog_smooth ..
@[fun_prop] lemma αs : ContDiff ℝ ∞ α:=(jog_smooth ..).comp bound_smooth
@[fun_prop] lemma βs : ContDiff ℝ ∞ β:=(jog_smooth ..).comp bound_smooth

-- SU factoring $uuᵀ$. h->ω
variable {J:Type}[Fintype J][DecidableEq J][Nonempty J]
def cap (U:Op J):= U*Uᵀ
lemma capgate (A:Op Slot)(p:trueS A): Spin.Sym (cap A):=by
 unfold cap; refine ⟨by rw [Matrix.transpose_mul,Matrix.transpose_transpose], (unitary _).mul_mem p.1 (Matrix.transpose_mem_unitaryGroup_iff.mpr p.1),by rw [Matrix.det_mul,Matrix.det_transpose,p.2,mul_one]⟩
lemma cap_side (V A:Op J): cap (V*A)=V*cap A* Vᵀ:=by unfold cap; simp [Matrix.transpose_mul,mul_assoc]
lemma real_cap(U:Op J)(p:Stone U): cap U=1:=by rw [cap,show Uᵀ=star U from ?_,p.rim.1.2]; have he:=p.realC; unfold cc at he; rw [← he,Matrix.transpose_transpose]; rw [he] -- repeated
lemma cap_iff(A:Op J)(h:trueS A)(p:cap A=1):Stone A:=by
 refine ⟨h,?_⟩; suffices ht:Aᵀ=star A by rw [cc,←ht,Matrix.transpose_transpose]
 calc
    _ = star A * (A*Aᵀ):=by rw [←mul_assoc,h.1.1,one_mul]
    _ = _:= by rw [show A*Aᵀ=1 from p,mul_one] -- syntax
lemma cap_path(A B: Op J)(h:trueS A)(g:trueS B)(p:cap A=cap B):∃ X:ℝ→Op J,Friendly Hotel X∧ X 0=A∧ X 1=B∧ ∀ x∈Hotel,trueS (X x)∧cap (X x)=cap A:=by
 let C:=star A*B; have he:A*C=B:=by unfold C; rw [←mul_assoc, h.1.2,one_mul]
 have hc:cap C=1:=by unfold C; rw [cap_side,← p,cap, ←mul_assoc,h.1.1,one_mul,← Matrix.transpose_mul,h.1.1,Matrix.transpose_one] -- tune
 obtain ⟨X,H,x,y,T⟩:= Oak.route (V:=1) (⟨suit_one,cc_one⟩:Stone (1:Op J)) (cap_iff C (suit_mul (suit_star h) g) hc); refine ⟨fun i=>A*X i,fun i u=>contDiffAt_const.mul (H i u),?_,?_,fun i f=>⟨suit_mul h (T i f).rim,?_⟩⟩; simp [x]; exact (by simpa [y] using he); rw [cap_side,real_cap _ (T _ f),mul_one]; rfl -- tune simp
-- factor without route-real determinant requirement; right reflection if needed
lemma lift_sym (A:Op J)(h:trueS A)(p:Aᵀ=A)(u:IsSelfAdjoint A): ∃ B:Op J,trueS B ∧cap B=A:=by
 -- projection H=(1-A)/2. J conventional. det is sign.
 have ha:A*A=1:= by nth_rw 1 [←u.star_eq]; exact h.1.1 -- tune
 let P: Op J:= (1/2:ℂ) • (1-A); let Q:=1-P; let F:= Q+I • P; have hP:star P=P:=by unfold P; simp only [star_smul,star_sub,star_one,u.star_eq]; norm_num
 have hp:Pᵀ=P:=by unfold P; rw [Matrix.transpose_smul,Matrix.transpose_sub,p,Matrix.transpose_one]
 have hs:P*P=P:=by unfold P; rw [Matrix.smul_mul, Matrix.mul_smul, sub_mul,one_mul,mul_sub,mul_one,ha]; module -- tune
 have hQ:IsStarProjection P:=⟨hs,hP⟩; let T:=hQ.one_sub; have ht:Fᵀ=F:=by unfold F Q; rw [Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_one, Matrix.transpose_smul I P,hp]
 have he:cap F=A:=by rw [cap,ht]; unfold F Q; simp only [add_mul,mul_add,Matrix.smul_mul,Matrix.mul_smul,T.isIdempotentElem.eq,hQ.mul_one_sub_self,hQ.one_sub_mul_self,hs,smul_zero,zero_add,add_zero,smul_smul, I_mul_I]; unfold P; module -- tune Q def
 have hx:F∈unitary (Op J):=by
    have hq:star F=Q-I • P:=by unfold F; rw [star_add, star_smul,hP, T.isSelfAdjoint,show star I= -I from conj_I];  unfold Q; rw [neg_smul,sub_eq_add_neg]; abel
    apply Matrix.mem_unitaryGroup_iff.mpr; rw [hq]; unfold F Q; simp only [add_mul,mul_sub,Matrix.smul_mul,Matrix.mul_smul,mul_one,hQ.one_sub_mul_self,hs,smul_zero,smul_smul, I_mul_I]; module
 by_cases k:F.det=1; exact ⟨F, ⟨hx,k⟩, he⟩; have hF:F.det= -1:=by
    have hv: F.det*F.det=1:= by have hy:= h.2; rw [← he,cap,ht,Matrix.det_mul] at hy; exact hy
    exact (mul_self_eq_one_iff.mp hv).resolve_left k -- tune
 let i:=Classical.arbitrary J; let R:Op J:=Matrix.diagonal (fun j=> if i=j then -1 else 1); have hr:cc R=R:=by ext j k; unfold R; by_cases h:j=k; subst k; rw [cc_apply,Matrix.diagonal_apply_eq]; split_ifs <;> simp; simp [h]; -- indent
 have hr':R*R=1:=by unfold R; rw [Matrix.diagonal_mul_diagonal,show (fun j:J=>_)= (1:J→ℂ) by ext j; split_ifs <;> simp]; rfl
 have hs' : cap R=1:=by rw [cap, show Rᵀ=R from Matrix.diagonal_transpose _]; exact hr'; -- not defeq transpose_diag probably fails tune
 refine ⟨F*R, ⟨(unitary _).mul_mem hx ?_ ,?_⟩, by rw [cap_side,hs',mul_one]; exact he⟩
 · have H: star R=R:= by unfold cc at hr; rw [←Matrix.transpose_transpose (star R),hr, show Rᵀ=R from Matrix.diagonal_transpose _]; -- tune
   constructor <;> rw [H,hr']
 rw [Matrix.det_mul,hF]; simp [R]
end Kite
end YM.CF.BPress.Lute
