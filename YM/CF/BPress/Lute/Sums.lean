import YM.CF.BPress.Lute.Sparkle
import YM.CF.Mir.Spin
/-! Swing calculus and radial purchase. Pow interpolation along spectral angles. -/
set_option linter.unusedSectionVars false
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Lute
open Function Finset Filter NormedSpace InnerProductSpace SU SU.Pair Spin Spin.Paint Lattice Fock Complex Join
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker InnerProductSpace ContDiff
attribute [local instance] opCStarAlgebra
variable {J K : Type*}[Fintype J][DecidableEq J][Fintype K][DecidableEq K]
local notation "π"=>Real.pi

def refit (e:J≃K): Op J ≃⋆ₐ[ℂ] Op K:= { Matrix.reindexAlgEquiv ℂ ℂ e with map_star' _:=rfl,map_smul' a b:=rfl }
lemma replaces(e:J≃K)(A:Op J) (i j : K):refit e A i j=A (e.symm i) (e.symm j):=rfl
lemma refit_T(e:J≃K)(A:Op J): refit e Aᵀ=(refit e A)ᵀ:=rfl
lemma refit_ne (e:J≃K) (A:Op J): (refit e A).det=A.det:=Matrix.det_reindex_self ..
def renU (e:J≃K)(U:UNI J):UNI K:=⟨refit e U.val, ⟨by rw [←map_star, ←map_mul,U.property.1,map_one],by rw [←map_star, ←map_mul,U.property.2,map_one]⟩⟩
lemma rot_refit (e:J≃K)(U:UNI J)(f:J→ℝ)(t:ℝ): refit e (rotationU U f t)=rotationU (renU e U) (f∘e.symm) t:=by
 unfold rotationU spectralC; rw [twist_formula,twist_formula,map_mul,map_mul,map_star]; congr 2; ext i j; rw [replaces]; by_cases h:i=j <;> simp [h]
lemma refit_back(e:J≃K)(A: Op K):refit e (refit e.symm A)=A:=by ext i j; rw [replaces,replaces]; simp
abbrev zoneC {J K : Type*}[DecidableEq J] (f:J→Op K) := jump (Equiv.refl J) f
lemma zone_diag(f:J→K→ℂ): zoneC (fun j=>Matrix.diagonal (f j))=Matrix.diagonal (Function.uncurry f):=by
 ext ⟨i,x⟩ ⟨j,u⟩; by_cases h:i=j<;>by_cases t:x=u<;>simp [zoneC,jump_apply,h,t, Function.uncurry]
lemma diag_both(f:J→ℂ)(g:K→ℂ): both (Matrix.diagonal f) (Matrix.diagonal g)=Matrix.diagonal (Sum.elim f g):=by
 ext (x|x) (y|y)<;> simp [both,Matrix.diagonal_apply]
lemma both_tran (A:Op J)(B:Op K): (both A B)ᵀ=both Aᵀ Bᵀ:=by simp [both,Matrix.fromBlocks_transpose]
lemma zone_tran(f:J→Op K):(zoneC f)ᵀ=zoneC (fun i=> (f i)ᵀ):=by
 ext ⟨i,v⟩ ⟨j,t⟩; by_cases h:i=j <;> simp [zoneC,jump_apply,h,Ne.symm]
abbrev bothU(U:UNI J)(V:UNI K):UNI (J⊕K):= ⟨both U.val V.val,both_unitary U.property V.property⟩
lemma rot_both (U:UNI J)(V:UNI K)(f:J→ℝ) (g:K→ℝ)(t:ℝ): rotationU (bothU U V) (Sum.elim f g) t=both (rotationU U f t) (rotationU V g t):=by
 unfold rotationU spectralC; simp only [twist_formula]; rw [show (fun i:J⊕K=>χ (t*Sum.elim f g i))=Sum.elim (fun i:J=>χ (t*f i)) (fun i=>χ (t*g i)) from funext (fun x=>by cases x <;> rfl),←diag_both]; rw [both_mul,star_both, both_mul] -- star orientation
abbrev zoner(U:J→UNI K): UNI (J×K):=⟨zoneC (fun i=>(U i).val), jump_unitary _ _ fun i=>(U i).property⟩
lemma rot_mix (U:J→UNI K)(f:J→K→ℝ) (t:ℝ): rotationU (zoner U) (Function.uncurry f) t=zoneC (fun i=> rotationU (U i) (f i) t):=by
 unfold rotationU spectralC; simp only [twist_formula]; let F(i:J)(j:K):= χ (t*f i j); change ((zoneC (fun i=>(U i).val))*Matrix.diagonal (Function.uncurry F))*_= _; rw [← zone_diag]; simp [F, jump_star, jump_mul, zoneC]

variable {A:Op J}{B:Op K}{a b:ℝ}
namespace Swing
lemma renameS(e:J≃K) (h: Swing A a):Swing (refit e A) a:=by
 obtain ⟨U,f,u,F,H⟩:= h.curve; rw [u,rot_refit]; exact ⟨renU e U,f ∘ e.symm,rfl,fun i=>F _,(Equiv.sum_comp e.symm f).trans H⟩
lemma left_right (p:Swing A a)(q:Swing B b):Swing (both A B) (a+b):=by obtain ⟨U,f,u,F,e⟩:=p.curve; obtain ⟨W,g,w,G,h⟩:=q.curve; rw [u,w,←rot_both]; refine ⟨_,_,rfl,(fun i=>Sum.rec F G i),?_⟩; rw [Fintype.sum_sum_type]; simpa [e,h]
lemma together (f:J→Op K) (s:J→ℝ)(p:∀ i,Swing (f i) (s i)):Swing (zoneC f) (∑ i,s i):=by
 choose U F h hf sf using fun i=>(p i).curve; refine ⟨zoner U,Function.uncurry F,?_,fun i=> hf ..,?_⟩; rw [rot_mix]; exact congrArg zoneC (funext h); rw [Fintype.sum_prod_type]; simp [Function.uncurry,sf]
lemma dial (f:J→ℝ)(s:ℝ)(p:∀ i, |f i|<π)(b:∑ i,f i=s): Swing (Matrix.diagonal (fun i=>χ (f i))) s:=by
 refine ⟨1,f,?_,p,b⟩; simp [rotationU,spectralC,twist_formula]
lemma zeroS(J:Type*)[DecidableEq J][Fintype J]: Swing (1:Op J) 0:=by
 convert dial (fun _:J=>0) 0 (fun _=>by simpa using Real.pi_pos) (by simp) using 1; simp
lemma const (a:ℝ)(p:|a|<π): Swing (χ a • (1:Op J)) (Fintype.card J*a):=by
 convert dial (fun _:J=>a) (Fintype.card J*a) (fun _=>p) (by simp) using 1; ext i j; by_cases h:i=j <;> simp [h]
-- two eigenvalues from trace/det, principal theta matter unaffected by twists
lemma second {V: Op (Fin 2)}(p:V∈unitary (Op (Fin 2)))(a b:ℝ)(r:|a|<π)(s:|b|<π)(h:V.trace=χ a+χ b)(k:V.det=χ a*χ b): Swing V (a+b):=by
 obtain ⟨U,f,v⟩:= spectralC_diag_exists V p; rw [v,spectralC,trace_twist,Matrix.trace_diagonal] at h; rw [v,twist_T] at k; simp [Fin.sum_univ_succ,Fin.prod_univ_succ] at h k
 have ht(x y:ℝ)(a b:ℂ)(u:spectralC U ![χ x,χ y]=V)(p:|x|<π)(q:|y|<π): Swing V (x+y):=by
    refine ⟨U,![x,y], u.symm.trans ?_,fun i=> by fin_cases i <;> first | exact p | exact q, ?_⟩
    · unfold rotationU; congr; funext i; fin_cases i <;> simp
    simp [Fin.sum_univ_succ]
 have he:(f 0-χ a)*(f 0-χ b)=0:=by linear_combination -k + (f 0) * h
 simp only [mul_eq_zero, sub_eq_zero] at he; rcases he with p|p
 · have g:f 1=χ b:=add_left_cancel ((congrArg (·+f 1) p.symm).trans h); apply ht a b 0 0 _ r s; rw [v]; congr; funext i; fin_cases i <;> first | exact p.symm | exact g.symm
 have g:f 1=χ a:=add_left_cancel ((congrArg (·+f 1) p.symm).trans (h.trans (add_comm ..))); rw [add_comm]; apply ht b a 0 0 _ s r; rw [v]; congr; funext i; fin_cases i <;> first | exact p.symm | exact g.symm

lemma weights(U:UNI J)(f:J→ℝ)(p:∀ i,|f i|<π)(t:ℝ)(u:t∈Set.Icc (0:ℝ) 1):∃ M : Op J,M=spectralC U (fun i:J=> (χ (f i/2)*(Real.cos (f i/2):ℂ))) ∧ ‖rotationU U f t-M‖ <1:=by
 let F(i):=χ (f i/2)*(Real.cos (f i/2):ℂ); let G(i):=χ (t*f i); refine ⟨spectralC U F,rfl,?_⟩; unfold rotationU spectralC; rw [← map_sub,twist_norm,Matrix.diagonal_sub,Matrix.l2_opNorm_diagonal]; exact (pi_norm_lt_iff zero_lt_one).mpr fun i=> χ_ball (p i) u
end Swing
end YM.CF.BPress.Lute
