import YM.CF.Cascade.Lect
set_option autoImplicit false
noncomputable section
namespace YM.CF.Cascade
open Function Filter Metric Finset Lattice Wilson Next.Free Bloch Laurent Scroll Precision Exterior Lat Ember Aroma
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker
variable {j t:ℕ}{n c f:Side}{k a b:ℝ}
open Tree SU Font Cube Extra.Iteration Nacre
open Thera Fock Dial Peaks Tulip Paige NormedSpace
local notation "G"=> SU.group
-- single-color abelian subgroup tests; Lie jet opNorm
abbrev rollH (x:CoreX)(t:ℝ): E:=group.lieExp (t • x)
section
open scoped Matrix.Norms.Frobenius
lemma rollAdd(x:CoreX)(t u:ℝ):rollH x (t+u)=rollH x t*rollH x u:=by apply group.mat_injective; unfold rollH; rw [group.mat_mul, group.mat_lieExp,group.mat_lieExp,group.mat_lieExp,add_smul,map_add,map_smul,map_smul]; exact exp_add_of_commute (((Commute.refl (group.colorMat x)).smul_left t).smul_right u)
lemma roll_inv(x:CoreX)(t:ℝ):(rollH x t)⁻¹=rollH x (-t):=inv_eq_of_mul_eq_one_right (by rw [←rollAdd]; simp [rollH]) -- tune side
lemma roll_link(x:CoreX)(i l: Fin group.repDim): HasDerivAt (fun t:ℝ=> group.mat (rollH x t) i l) (group.colorMat x i l) 0:=by
 let F(t):=group.mat (rollH x t)
 let L:group.Mat→L[ℝ]ℂ:=Laic.entry_F i l; have he: HasDerivAt F (group.colorMat x) 0:=group.expDiff_zero.comp_hasDerivAt_of_eq (0:ℝ) (((hasDerivAt_id' (0:ℝ)).smul_const x).congr_deriv (by simp)) (zero_smul ..).symm -- tune
 exact L.hasFDerivAt.comp_hasDerivAt 0 he
end
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
def green (X:CoreX): Op Slot:= dMatter (group.colorMat X)
lemma greenD(X:CoreX): HasDerivAt (fun t=> (matter (rollH X t)).val) (green X) 0:=by
 apply actual; · simp [rollH]
 exact op_deriv.mpr (fun i j=> roll_link X i j)
lemma greenN(X:CoreX):star (green X)= -green X:=by
 let f(t):=(matter (rollH X t)).val; have he:f 0=1:=by simp only [f,rollH,zero_smul, show group.lieExp 0=1 by simp,map_one]; rfl
 have hx: (fun t=>f t * star (f t))=fun _=>1:=funext fun i=> (matter _).property.2
 have hp: HasDerivAt (fun t=> f t * star (f t)) (green X*star (f 0) + f 0*star (green X)) 0:= (greenD X).mul (greenD X).star
 rw [hx, he,star_one,mul_one,one_mul] at hp; rw [eq_neg_iff_add_eq_zero,add_comm]; exact hp.unique (hasDerivAt_const ..)
def ting (X:CoreX):Op Slot:= (-Complex.I) • green X
lemma ringH(X): Complex.I • ting X=green X:=by simp only [ting,smul_smul,mul_neg,Complex.I_mul_I,neg_neg,one_smul]
lemma tingP(X): star (ting X)=ting X:=by unfold ting; rw [star_smul,star_neg,show star Complex.I= -Complex.I from Complex.conj_I,neg_neg,greenN,smul_neg,neg_smul]
lemma tingV (X:CoreX)(h:‖X‖=1): Matrix.trace (ting X*ting X)=60:=by
 have ht:= hue_v X h; change Matrix.trace (green X^2)= _ at ht; rw [←ringH, sq,Matrix.smul_mul, Matrix.mul_smul,smul_smul,Complex.I_mul_I,neg_smul, one_smul,Matrix.trace_neg,neg_inj] at ht; exact ht
lemma gauge_line (x:Air n)(q:Aroma.Dir x)(u: CoreX)(v:ℝ):represent (pour n u (v • lop x))= Lattice.gauge (fun i=>rollH u (v*x i)) 1:=by
 funext i; simp only [Lattice.gauge,Pi.one_apply,mul_one]; rw [roll_inv, ←rollAdd]; rcases i with ⟨i,b⟩; rw [Work.F03.represent_link]; apply congrArg group.lieExp; change (if coord b=coord 1 then v* _ else 0) • u= _
 by_cases h:b=1; · subst b; rw [if_pos rfl]; unfold lop; rw [mul_sub]; rfl
 rw [if_neg (show coord b ≠coord 1 from (Equiv.injective axisEquiv).ne h),q _ _ h]; simp
private lemma leaves {κ:Type}[Fintype κ][DecidableEq κ]{V:ℝ→Op κ} (p:∀ i j,V (i+j)=V i*V j)(v:V 0=1){z:Op κ}(h:HasDerivAt V z 0): ∀ x,V x=exp (x • z):=by
 letI : NormedAlgebra ℚ (Op κ) := NormedAlgebra.restrictScalars ℚ ℂ _
 let W(x:ℝ):=exp (x • z); have ht(t u): W (t+u)=W t*W u:=by unfold W; rw [add_smul]; exact exp_add_of_commute (((Commute.refl z).smul_left t).smul_right u) -- tune C algebra
 have he(t):HasDerivAt V (V t*z) t:=by
    have hk:= (hasDerivAt_id (x:=t)).sub_const t; have hp: HasDerivAt V z (id t-t):=by rw [id_eq,sub_self]; exact h
    have HH:=hp.scomp t (h:=fun x:ℝ=> x-t) hk; have hh:= (HH.const_mul (V t)); rw [one_smul] at hh; apply hh.congr_of_eventuallyEq
    filter_upwards with x; change V x=V t*V (x-t); rw [←p]; congr 1; abel --]
 have hu(t): HasDerivAt (fun s:ℝ=> W (-s)) (-z*W (-t)) t:=by
    have hx:=hasDerivAt_exp_smul_const z (-t:ℝ); have hv: HasDerivAt (fun x:ℝ=>-x) (-1) t:=(hasDerivAt_id' t).neg -- tune
    apply (hx.scomp t hv).congr_deriv; change -(1:ℝ) • (W (-t)*z)=_; rw [neg_smul,one_smul,neg_mul,show W (-t)*z=z*W (-t) from (((Commute.refl z).smul_left (-t)).exp_left).eq]
 let X(s:ℝ):=V s* W (-s); have hk(s): HasDerivAt X 0 s:=by apply ((he s).mul (hu s)).congr_deriv; rw [neg_mul,mul_neg,mul_assoc]; abel
 intro x; have hx: X x=1:=by have he:=intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=x) (fun i _=> hk i) (by simp); simp [X,v,W] at he; simpa [X,W] using (sub_eq_zero.mp he.symm)
 calc
   V x =X x * W x:=by unfold X; rw [mul_assoc,← ht]; simp [W]
   _ = _:=by rw [hx,one_mul]
lemma twine(u: Site (More n)→ E): (love n).symm (tradew n u).val = jump (Equiv.refl (Site n)) (fun i=> (1:Op SpinIdx) ⊗ₖ (matter (u (node i))).val):=by
 apply (love n).injective; change love n _ = love n _; rw [StarAlgEquiv.apply_symm_apply, loveAt]; ext ⟨⟨x,i⟩,p⟩ ⟨⟨y,j⟩,q⟩; by_cases h:x=y<;>by_cases g:i=j<;>simp [h,g,unityP,helix,tradew, jump_apply, Matrix.one_apply]
lemma party (u: CoreX)(v:Air n)(x:ℝ):(love n).symm (tradew n (fun i=> rollH u (x*v i))).val= exp (x • ski (ting u) v):=by
 let F(t:ℝ):=(love n).symm (tradew n (fun i=> rollH u (t*v i))).val; let g(t:ℝ)(i:Site (More n)):= (matter (rollH u (t*v i))).val; have he (t):F t= jump (Equiv.refl _) (fun i=> (1:Op SpinIdx)⊗ₖ g t (node i)):= twine _
 apply leaves (V:=F) _ _ _ x
 · intro i j; simp_rw [he, jump_mul,op_kron_mul,mul_one, g,add_mul,rollAdd,map_mul]; rfl
 · rw [he]; have h(i:Site n): (1:Op SpinIdx)⊗ₖ g 0 (node i)=1:=by unfold g; rw [zero_mul,show rollH u 0=1 by simp [rollH],map_one]; exact Matrix.one_kronecker_one
   simp_rw [h]; exact jump_id
 rw [funext he]; refine op_deriv.mpr ?_; rintro ⟨i,p,l⟩ ⟨k,c,b⟩
 have ht: thrust (ting u)=1 ⊗ₖ green u:=by rw [thrust,ringH]
 unfold Aroma.ski; rw [ht]; simp_rw [jump_apply]; by_cases he:i=k; swap; simp only [Equiv.refl_apply, he,ite_false]; exact hasDerivAt_const ..
 subst k; simp only [Equiv.refl_apply,ite_true]; have hp(k):HasDerivAt (fun t=> g t k) (v k • green u) 0:=by
    let f(t:ℝ):=t*v k; have hp:f 0=0:=zero_mul _; have hx:HasDerivAt f (v k) 0:=by simpa [f] using ((hasDerivAt_id' (0:ℝ)).mul_const (v k))
    exact (hp.symm ▸ greenD u : HasDerivAt _ _ (f 0)).scomp (0:ℝ) hx -- order tune
 simp only [Matrix.smul_apply,smul_eq_mul,Matrix.kronecker_apply]
 refine ((op_deriv.mp (hp (node i)) l b).const_mul _).congr_deriv ?_; rw [Matrix.smul_apply,Complex.real_smul, mul_left_comm]
end YM.CF.Cascade
