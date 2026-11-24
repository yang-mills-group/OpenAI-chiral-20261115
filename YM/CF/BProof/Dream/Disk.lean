import YM.CF.Operator.Spectral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! B-Gz fixed-dimensional principal phase criterion. Scalar disks. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Dream
open Matrix Complex Finset Function
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff BigOperators ComplexConjugate
attribute [local instance] opCStarAlgebra
local notation "π" => Real.pi

def rose (t:ℝ):ℂ:= Complex.exp ((t:ℂ)*I)
@[simp] lemma rose_zero : rose 0=1:=by rw [rose]; simp
lemma rose_spokes (t:ℝ): rose t= ↑(Real.cos t)+ (↑(Real.sin t):ℂ)* I:= by rw [rose, exp_mul_I]; push_cast; rfl
lemma rose_add (s t:ℝ): rose (s+t)=rose s* rose t:=by rw [rose,ofReal_add,add_mul,exp_add]; rfl
lemma rose_ne (t:ℝ):rose t≠0:=exp_ne_zero _
lemma rose_minus (t:ℝ): rose (-t)=(rose t)⁻¹:=by simp [rose,exp_neg]
lemma rose_star (t:ℝ): star (rose t)=rose (-t):=by rw [rose_spokes,rose_spokes,star_add,star_mul]; rw [Real.cos_neg,Real.sin_neg, ofReal_neg, Complex.star_def]; simp only [Complex.star_def,conj_I,conj_ofReal,neg_mul]; ring -- tune
lemma roseU (t:ℝ): rose t ∈ unitary ℂ:=by constructor <;> rw [rose_star,← rose_add] <;> simp
lemma rose_smooth : ContDiff ℝ ∞ rose :=ContDiff.cexp (ofRealCLM.contDiff.mul contDiff_const)
@[simp] lemma roseNorm (t:ℝ): ‖rose t‖=1:= by simp [rose,norm_exp]
lemma rose_full : rose (2*π)=1:=by norm_cast; simp [rose,exp_two_pi_mul_I]
def MainT (t:ℝ): Prop:=|t|<π
lemma MainT.neg {t:ℝ}(h:MainT t) : MainT (-t):=by unfold MainT; rw [abs_neg]; exact h
lemma main0 : MainT 0:=by rw [MainT,abs_zero]; exact Real.pi_pos
lemma main_inject {s t:ℝ}(h:MainT s)(e:MainT t)(p:rose s=rose t):s=t:=by
 obtain ⟨ha,hb⟩:=abs_lt.mp h; obtain ⟨hc,ht⟩:= abs_lt.mp e; have ht' : ((↑s:ℂ)*I).im=s:=by simp
 have hu' : ((↑t:ℂ)*I).im=t:=by simp
 rw [← ht',exp_inj_of_neg_pi_lt_of_le_pi (_root_.lt_of_lt_of_eq ha ht'.symm) (ht'.trans_le hb.le) (_root_.lt_of_lt_of_eq hc hu'.symm) (hu'.trans_le ht.le) p,hu'] -- tune type syntax
-- midpoint disk distance estimate
private def rootT (t:ℝ):= Real.cos (t/2)
lemma cos_ac (x:ℝ): Real.cos |x|= Real.cos x:=by rcases le_total 0 x with h|h; rw [abs_of_nonneg h]; rw [abs_of_nonpos h,Real.cos_neg]
lemma scalarDisk (t:ℝ)(h:MainT t) : ∃ (M:ℂ)(r:ℝ),0<r∧r<1∧∀ (s:ℝ),0≤s→ s≤1 → ‖rose (t*s)-M‖≤r:=by
 let c:= Real.cos (t/2); let z:= rose (t/2); obtain ⟨ha,hb⟩:= abs_lt.mp h; have hp:=Real.pi_pos; have hc:0<c:=Real.cos_pos_of_mem_Ioo ⟨by linarith,by linarith⟩
 have hl:c≤1:=Real.cos_le_one ..; let r:= 1-c^2/2; refine ⟨(c:ℂ)*z,r,by dsimp only [r]; nlinarith,by dsimp only [r]; nlinarith,fun s hx hy=>?_⟩
 let a:=t*s-t/2
 have hg: |a|≤ |t/2|:=by unfold a; rcases le_total 0 t with g|g; rw [abs_of_nonneg (show 0≤t/2 by linarith), abs_le]; constructor <;> nlinarith; rw [abs_of_nonpos (show t/2≤0 by linarith),abs_le]; constructor <;> nlinarith
 have hu:|t/2| ≤ π:=abs_le.mpr ⟨by linarith,by linarith⟩; have he:c ≤ Real.cos a:= by unfold c; rw [←cos_ac (t/2),←cos_ac a]; exact Real.strictAntiOn_cos.antitoneOn (Set.mem_Icc.mpr ⟨abs_nonneg _,hg.trans hu⟩) (Set.mem_Icc.mpr ⟨abs_nonneg _,hu⟩) hg
 rw [show t*s=a+t/2 from by unfold a; ring,rose_add]; change ‖_ * z-_‖ ≤ _; rw [←sub_mul,norm_mul,roseNorm,mul_one]; have hh:= Complex.normSq_eq_norm_sq (rose a-(↑c:ℂ)); rw [normSq_apply,rose_spokes] at hh -- better change only lhs
 rw [rose_spokes]; simp only [sub_re,sub_im,add_re,add_im,mul_re,mul_im,ofReal_re,ofReal_im,I_re,I_im,sub_zero,zero_add,add_zero,zero_mul,mul_one,mul_zero, sub_self] at hh
 have hH:= Real.sin_sq_add_cos_sq a; let q:= ‖(↑(Real.cos a):ℂ)+ ↑(Real.sin a)*I-↑c‖; change _=q^2 at hh; have hq:0≤q:=norm_nonneg _; change q≤r; dsimp only [r]; nlinarith only [hc,hl,hh,hH,hq,he,mul_nonneg hc.le (sub_nonneg.mpr he),sq_nonneg (c^2/2),show 0≤1-c^2/2 from by nlinarith] -- tune
end YM.CF.BProof.Dream
