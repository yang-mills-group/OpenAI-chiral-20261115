import YM.SU5.Reconstruction.Quartz.CrystalBall
set_option autoImplicit false
noncomputable section
namespace YM.Quartz.Waltz
open Function Filter Set MeasureTheory Measure Metric Topology
open scoped Topology NNReal ENNReal Complex InnerProductSpace
open Complex Ravin
noncomputable def fillet(b s t:ℝ)(z:ℂ):= Blaze b (Real.exp (-s)*((t:ℂ)+z),Real.exp s*z)
@[fun_prop] lemma fillet_diff(b s t:ℝ): Differentiable ℂ (fillet b s t):= by unfold fillet Blaze; fun_prop
noncomputable def petal(s d:ℝ): Ba:= ((-(Real.exp (-s)*d):ℝ) * I, (-(Real.exp s*d):ℝ) * I)
lemma petal_zero(s:ℝ): petal s 0= (0,0):=by simp [petal]
lemma harmonic (s t x y:ℝ) (b:ℝ):fillet b s t (x+y*I)= Blaze b (Largo (hike s (t,x))-petal s y):= by unfold fillet petal hike Largo; rw [at_swap]; congr 1; ext1 <;> dsimp <;> push_cast <;> ring
local notation "E"=> Real.exp 3
lemma passion(s:ℝ)(p:|s|≤3): Real.exp s ≤ Real.exp 3 ∧ Real.exp (-s)≤Real.exp 3 := ⟨Real.exp_le_exp.mpr (abs_le.mp p).2,Real.exp_le_exp.mpr (by linarith [(abs_le.mp p).1])⟩
noncomputable def Plateau(d:ℝ):=2*(Real.exp 3)^2*d^2
lemma foggy(s d y:ℝ)(p:|s|≤3)(v:|y|≤d):pressure (Eddy (petal s y))≤ Plateau d:= by
 let kp(t:ℝ)(ht:0<t)(p:t≤Real.exp 3) : (-(t*y))^2 ≤ (Real.exp 3)^2*d^2:=by
    rw [neg_sq,mul_pow,←sq_abs y]; gcongr
 change ((↑(-(Real.exp (-s)*y)):ℂ)*I).im^2 + ((↑(-(Real.exp s*y)):ℂ)*I).im^2 ≤ 2*(Real.exp 3)^2*d^2; simp only [mul_im,ofReal_re,I_im,mul_one,ofReal_im,I_re,mul_zero,add_zero]; nlinarith [kp _ (Real.exp_pos s) (passion s p|>.1), kp _ (Real.exp_pos (-s)) (passion s p|>.2)]
lemma petal_ground (s t:ℝ): Forge (petal s t)=0:=by ext1<;>unfold Forge petal<;>simp only [Prod.fst_zero,Prod.snd_zero,mul_re,ofReal_im,I_re,mul_zero,zero_mul,sub_zero]
lemma fillet_norm (b s t y x:ℝ)(p:0<b) : ‖fillet b s t ((x:ℂ)+y*I)‖=wallRate b (hike s (t,x))*Real.exp (b*pressure (Eddy (petal s y))) := by rw [harmonic,toll p,petal_ground,sub_zero]
lemma within_prism (s t x g:ℝ)(p:|s|≤3)(h:pressure (hike s (t,x))<g): |x|≤ E*Real.sqrt g ∧ |t| ≤ 2*E*Real.sqrt g:=by
 let y:= (hike s (t,x)); have hx: (swap (-s) y).1=t+x ∧ (swap (-s) y).2=x:=by unfold y hike; simp only[swap_trans]; exact ⟨trivial,trivial⟩
 have he: y.1^2+y.2^2<g:=h; have hp:0<g:=lt_of_le_of_lt (by positivity) he; have hz: ∀ X:ℝ,X^2≤ g→ |X|≤Real.sqrt g:=by intro x v; apply le_of_sq_le_sq; rw [sq_abs, Real.sq_sqrt hp.le]; exact v; positivity
 have h1 : |t+x|≤ E*Real.sqrt g:= by rw[←hx.1,at_swap,abs_mul, neg_neg]; change |Real.exp s| *_ ≤ _; rw[abs_of_pos (Real.exp_pos _)]; exact mul_le_mul (passion s p|>.1) (hz y.1 (by nlinarith)) (abs_nonneg _) (by positivity)
 have h2 : |x| ≤ E*Real.sqrt g:= by rw [←hx.2,at_swap,abs_mul, abs_of_pos (Real.exp_pos _ )]; exact mul_le_mul (passion s p|>.2) (hz y.2 (by nlinarith)) (abs_nonneg _) (by positivity)
 refine ⟨h2,abs_le.mpr (by constructor <;> linarith [(abs_le.mp h1).1,(abs_le.mp h1).2,(abs_le.mp h2).1,(abs_le.mp h2).2])⟩ -- tune
noncomputable def mist(d γ:ℝ):= 2*(Plateau d+γ+1)
noncomputable def scud(d γ:ℝ):=2*Real.exp 3*Real.sqrt (mist d γ)+1
lemma scud_favorable(d γ:ℝ):0<scud d γ:=by unfold scud; positivity
lemma heavy(s γ d t x:ℝ)(p:|s|≤3)(v: scud d γ ≤ |t| ∨ scud d γ ≤ |x|) : mist d γ ≤ pressure (hike s (t,x)) := by
 by_contra! h; obtain ⟨r,g⟩:=within_prism s t x (mist d γ) p h; have ht:= Real.sqrt_nonneg (mist d γ); unfold scud at v; rcases v with v|v <;> nlinarith [Real.exp_pos (3:ℝ)]
lemma cap_mist (b s γ d t x y:ℝ)(i:0<b)(p:|s|≤3)(q:|y|≤d)(v: scud d γ ≤ |t| ∨ scud d γ ≤ |x|) : ‖fillet b s t ((x:ℂ)+y*I)‖ ≤ 2*Real.exp (-b*(γ+1))*wallRate (b/2) (hike s (t,x)):=by
 let z:= hike s (t,x); let g(s d:ℝ):= Eddy (petal s d); rw [fillet_norm b s t y x i]; unfold wallRate; rw [mul_assoc b, ←Real.exp_add];
 rw[show 2*Real.exp (-b*(γ+1))*(b/2*Real.exp (-(b/2)*pressure z))= b*Real.exp (-b*(γ+1)-(b/2)*pressure z) from (by rw[sub_eq_add_neg,Real.exp_add,neg_mul (b/2) _]; ring)] -- tune
 gcongr; have h:=heavy s γ d t x p v; unfold mist at h; unfold z; nlinarith [foggy s d y p q]
lemma thinner(b:ℝ)(i:0<b)(t:Du):wallRate b t ≤ b:=by unfold wallRate; apply mul_le_of_le_one_right i.le; refine Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr i.le) ?_); unfold pressure; positivity
lemma cap_edge (b s γ d t x y:ℝ)(i:0<b)(p:|s|≤3)(q:|y|≤d)(v: scud d γ ≤ |t| ∨ scud d γ ≤ |x|) : ‖fillet b s t ((x:ℂ)+y*I)‖ ≤ Real.exp (-b*γ):= by
 apply le_trans (cap_mist b s γ d t x y i p q v)
 refine le_trans (mul_le_mul_of_nonneg_left (thinner _ (half_pos i) _) (by positivity)) (le_trans (?_ : 2*Real.exp (-b*(γ+1))*(b/2) ≤ Real.exp (-b*(γ+1))*Real.exp b) ?_)
 · rw[show 2*Real.exp (-b*(γ+1))*(b/2)=Real.exp (-b*(γ+1))*b from by ring]; gcongr; exact le_trans (by linarith : b≤b+1) (Real.add_one_le_exp _)
 exact le_of_eq (by rw [← Real.exp_add,show -b*(γ+1)+b= -b*γ from by ring])
end YM.Quartz.Waltz
