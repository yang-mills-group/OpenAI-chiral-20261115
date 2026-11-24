import YM.CF.BProof.Dream.Firth
import YM.CF.BProof.Dream.North
import YM.CF.BProof.Centers
/-! Center-root phase totals, and B^z. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Dream
open Matrix Function SU Join Finset Mag
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator Kronecker ContDiff
attribute [local instance] opCStarAlgebra
local notation "D"=>Matrix.diagonal
local notation "π"=>Real.pi
local notation "τ"=>2*π/5

-- center given t, R(z^{-1}) here.
def centre2 (t:ℝ)(i:Fin 7) : Duo:= if i<4 then dress t else rose (-2*t) • 1
def lonely (t:ℝ) : Op Unit:=rose t • 1
def centreB (t:ℝ): Op Keys := both (choir (centre2 t)) (lonely t)
lemma centreB_tr (t:ℝ): (centreB t)ᵀ=centreB t:=by unfold centreB; rw [both_trans,choir_trans, lonely,transpose_smul,transpose_one]; simp only [centre2,dress,apply_ite Matrix.transpose, diagonal_transpose, transpose_smul, transpose_one]; rfl
lemma notionW (a:ℂ) : ExTwo.wedgeOp (a • (1:Op F))= (a*a) • (1:Op Ten):=by rw [←ExTwo.wedge_one]; ext i j; simp [ExTwo.wedge_entry]; ring
lemma double_f (a:ℝ): rose a*rose a=rose (2*a):=by rw [←rose_add]; congr 1; ring
set_option maxHeartbeats 600000 in
lemma keys_diag (t:ℝ): atlas board (centreB t)=both (rose (-2*t) • (1:Op Ten)) (rose t • (1:Op F)):=by
 let L:=rose (-2*t); let W(s:Sheet):= Sum.elim (fun _=>L) (fun _=>rose t) s
 rw [show both _ _=D W from ?_]; swap; · ext i j; rcases i with i|i <;> rcases j with j|j <;> simp [W,both, L, Matrix.diagonal_apply,Matrix.one_apply,mul_ite] -- tune notation simp!
 apply seats_sub; intro i j; simp only [atlasP, Matrix.diagonal_apply, keyX_b.1.eq_iff]; by_cases H:i=j; subst j; rcases i with ⟨i,b⟩|⟨⟩; · fin_cases i <;> fin_cases b <;> norm_num [keyX,W,centreB,centre2,show dress t=D ![L,rose t] from rfl,Fin.lt_def,choir,jump_apply,both,topX,botX,L, F,Pair.f,Pair.p] -- ltT private hidden
 · simp [keyX,W,centreB,lonely,both,Pair.f]
 simp only [H,↓reduceIte]; rcases i with ⟨i,b⟩|⟨⟩ <;> rcases j with ⟨j,c⟩|⟨⟩
 · by_cases h:i=j; subst j; have he:b≠c:=fun e=>H (by rw [e]); simp only [centreB, both, Matrix.fromBlocks_apply₁₁,choir,jump_apply,Equiv.refl_apply,ite_true,centre2]; split <;> simp [dress,he]; simp [h,centreB,choir,jump_apply,both]
 all_goals simp_all [centreB,both]
lemma centre_form (z:E)(t:ℝ)(e: fund z= rose t • (1: Op F)) : each (fund z⁻¹)=atlas board (centreB t):=by
 rw [fund_inv,e,star_smul,star_one,each, keys_diag, notionW,cc_smul,cc_one,star_star, rose_star,double_f,show 2*(-t)= -2*t from by ring] -- final
lemma centreB_cc (t:ℝ): cc (atlas board (centreB t))=atlas board (centreB (-t)) := by
 rw [keys_diag,keys_diag, show cc (both (_ : Op Ten) (_: Op F))=both (cc (rose (-2*t) • 1)) (cc (rose t • 1)) from ?_]; simp only [cc_smul, rose_star, cc_one]; rw [show -(-2*t)= -2*(-t) from by ring]; ext i j; rcases i with i|i <;> rcases j with j|j <;> simp only [cc_apply, both, fromBlocks_apply₁₁,fromBlocks_apply₁₂,fromBlocks_apply₂₁,fromBlocks_apply₂₂,Matrix.zero_apply,star_zero]

def living : Op Sheet:= shiftB 1
def colour (Z:E): Op Sheet:=each (fund Z) * living*(each (fund Z))ᵀ
def rotated (t:ℝ): Op Sheet:= atlas board (centreB t)* living * atlas board (centreB t)
lemma colour_eq(z:E)(t:ℝ)(p:fund z=rose t • 1) : colour z⁻¹=rotated t:=by rw [colour,centre_form _ _ p,← atlas_trans,centreB_tr]; rfl
-- relation blocks
abbrev trayB (θ:ℝ)(i:Fin 7):Duo:=if i < 4 then doubleU θ (topAngle i) else rose (-4*θ) • 1
lemma plainT (t θ:ℝ): (rose (-2*θ) • (1:Duo))*flect t*(rose (-2*θ) • (1:Duo))*flect t=rose (-4*θ) • (1:Duo):=by rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm, one_mul,mul_one,smul_smul,Algebra.smul_mul_assoc,double_f,show 2*(-2*θ)= -4*θ from by ring, show flect t*flect t=1 from by nth_rw 1 [← flect_self]; exact (flect_unit t).1]
lemma rotated_parts (t:ℝ): rotated t*star living=atlas board (both (choir (trayB t)) (rose (2*t) • 1 :Op Unit)):=by
 rw [rotated,living, shiftB_star,shiftB_p]; rw [←map_mul,←map_mul,←map_mul]; apply congrArg; unfold cabinet centreB; rw [both_mul,both_mul,both_mul,choir_mul,choir_mul,choir_mul]
 refine congrArg₂ _ (congrArg _ ?_) ?_; · ext1 i; by_cases h:i<4; simp only [Pi.mul_apply,centre2,trayB,h,↓reduceIte]; rfl; simp only [Pi.mul_apply,centre2,trayB,h,↓reduceIte]; exact plainT ..
 unfold lonely; simp only [mul_neg,mul_one,neg_mul,neg_neg,Algebra.smul_mul_assoc,one_mul,smul_smul,double_f]

lemma whirl_total (θ a b v:ℝ)(k: MainT (-θ))(h:MainT a)(u: rose (-4*θ)=rose a)(H:MainT b)(y:rose (2*θ)=rose b)
 (p:Whirl (doubleU θ (π/4)) v)(e:6*a+b+v=6*θ) : Whirl (rotated θ*star living) 0 := by
 let m : Fin 7→ℝ := ![-θ*2,-θ*2,-θ*2,v,a*2,a*2,a*2]
 have hw := fives -- not needed
 rw [rotated_parts θ]; refine whirlAt _ (m:=0) ?_; rw [y,show (0:ℝ)= (∑ i,m i)+b*(Fintype.card Unit : ℝ) from by simp [m,Fin.sum_univ_succ]; linarith]; refine whirlJoin (whirlChoir _ m fun i=>?_) (scalarWhirl b H)
 have hk: Whirl (doubleU θ (π/2)) (-θ*2):=by rw [switchT]; simpa using (scalarWhirl (-θ) k (I:=Fin 2))
 have hu: Whirl (rose (-4*θ) • (1:Duo)) (a*2):=by rw [u]; simpa using scalarWhirl a h (I:=Fin 2)
 fin_cases i; exact hk; exact hk; exact hk; exact p; exact hu; exact hu; exact hu
lemma whirl1 : Whirl (rotated (τ) * star living) 0 := by
 let t:ℝ:=(τ); have ht:t=τ:=rfl; have hp:= Real.pi_pos; refine whirl_total t t (2*t) (-t*2) ?_ ?_ ?_ ?_ rfl half1 ?_
 · exact abs_lt.mpr ⟨by linarith,by linarith⟩
 · exact abs_lt.mpr ⟨by linarith,by linarith⟩
 · rw [← around (-4*t),show -4*t+2*π=t from by linarith]
 · exact abs_lt.mpr ⟨by linarith,by linarith⟩
 linarith
lemma whirl2 : Whirl (rotated (2*(τ)) * star living) 0 := by
 let t:ℝ:=(τ); have ht:t=τ:=rfl; have hp:=Real.pi_pos; refine whirl_total (2*t) (2*t) (-t) t ?_ ?_ ?_ ?_ ?_ half2 ?_
 · exact abs_lt.mpr ⟨by linarith,by linarith⟩
 · exact abs_lt.mpr ⟨by linarith,by linarith⟩
 · rw [← around (-4*(2*t)),← around (-4*(2*t)+2*π),show -4*(2*t)+2*π+2*π=2*t from by linarith]
 · exact abs_lt.mpr ⟨by linarith,by linarith⟩
 · rw [←around (-t), show 2*(2*t)=-t+2*π from by linarith]
 linarith
lemma living_star : star living=living:= shiftB_star 1
lemma rotate_cc (t:ℝ) : cc (rotated t)=rotated (-t):=by simp only [rotated,cc_mul,centreB_cc]; rw [cc,living_star,show livingᵀ=living from shiftB_T 1]
lemma whirl_neg (t:ℝ)(h:Whirl (rotated t * star living) 0): Whirl (rotated (-t) * star living) 0:=by
 have he:=cc_Whirl h; simp only [neg_zero,living_star, cc_mul,rotate_cc] at *; rw [cc, living_star,show livingᵀ=living from shiftB_T 1] at he; exact he

def petal (i: Fin 5):ℝ :=![0,(τ),2*(τ),-(2*(τ)),-(τ)] i
lemma factor_rose : rose (τ) = eta:=by unfold rose Mag.eta; push_cast; congr 1; ring
lemma centreFund(i:Fin 5) : fund (center i)=rose (petal i) • (1:Op F):=by
 rw [fund, mat_center]; apply congrArg (fun x:ℂ=> x • (1:Op F)) _; rw [←factor_rose]; let s:= rose (τ); have hs:s^5=1:= by unfold s; rw [factor_rose]; exact Mag.eta_root.pow_eq_one
 have hq : s≠0:=rose_ne _
 have hx : rose (-(2*(τ)))=s^3:=by rw [rose_minus,←double_f]; change (s*s)⁻¹=_; field_simp; linear_combination -hs -- tune
 have hu : rose (-(τ))=s^4:=by rw [rose_minus]; change s⁻¹=s^4; field_simp; linear_combination -hs
 fin_cases i <;> simp [petal,hx,hu,←double_f,pow_two,s] -- tune `←double_f` rewriting τ inside (2*pi)/5? which top multiplicative no. simp loops hs def
lemma centreS(i:Fin 5) : Whirl (colour (center i)⁻¹*star living) 0:=by
 by_cases h:i=0
 · subst i; rw [center_zero,inv_one, colour,fund_one,each_one,transpose_one,one_mul,mul_one,show living*star living=1 from (shiftB_U 1).2]; exact whirl_one
 rw [colour_eq _ _ (centreFund i)]; fin_cases i; exact (h rfl).elim; exact whirl1; exact whirl2; exact whirl_neg _ whirl2; exact whirl_neg _ whirl1
lemma tray_not {θ:ℝ}(h:θ≠0)(e:MainT θ) : rotated θ≠living:=by
 intro p; have hv : rotated θ*star living=1:=by rw [p]; exact (shiftB_U 1).2
 rw [rotated_parts,← map_one (atlas board)] at hv; replace hv:= (atlas board).injective hv
 let x:Keys:=.inl (0,0); have hz:= Matrix.ext_iff.mpr hv x x; unfold x at hz; norm_num [both,choir,trayB,topAngle,jump_apply,switchT,show (0:Fin 7)<4 from by decide] at hz -- tune
 exact h (neg_eq_zero.mp (main_inject e.neg main0 (hz.trans rose_zero.symm))) -- name
lemma colour_n(i:Fin 5)(h:i≠0): colour (center i)⁻¹≠living:=by
 rw [colour_eq _ _ (centreFund i)]; have hp:= Real.pi_pos; refine tray_not ?_ ?_ <;> fin_cases i <;> first| exact (h rfl).elim| (norm_num [petal,MainT,abs_lt,-abs_neg] <;> (first | (constructor <;> linarith) | (try positivity)))
 rw [abs_of_nonneg (by positivity : 0≤ (τ))]; linarith
end YM.CF.BProof.Dream
