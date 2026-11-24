import SatinThinPattern
-- step amplitudes paid. T cost across gap pulses. <=
set_option autoImplicit false
set_option maxHeartbeats 950000
noncomputable section
namespace YM.CF.QuadClock
open Lattice Finset Mew
variable (L: Side)(n:ℕ)(a b z:ℝ)
def fareMin:ℝ:= (64*((L.val:ℝ)⁻¹)^4)^n
def fareMax:ℝ:= zoomC L^n
structure Premier :Prop where
 nz: a ≠ 0
 big: |a| ≤ fareMax L n
 small: |a⁻¹| ≤ fareMin L n
lemma premier_zero: Premier L 0 1:= ⟨one_ne_zero,by simp [fareMax],by simp [fareMin]⟩
lemma premier_L (D:Funds L)(p:Premier L n a): Premier L (n+1) (D.ticket*a):=by
 refine ⟨mul_ne_zero D.nonzero p.nz,?_,?_⟩
 · rw [abs_mul,fareMax,pow_succ']; exact mul_le_mul D.lid p.big (abs_nonneg _) ((by have h:=zoomC_p L; linarith): 0 ≤ zoomC L)
 rw [mul_inv_rev,abs_mul,fareMin,pow_succ]; refine mul_le_mul p.small D.floor (abs_nonneg _) ?_; positivity
noncomputable def eddy (n:ℕ): ℝ:=(1/4)*(1-(1/4:ℝ)^n)
lemma eddy0 : eddy 0=0:=by simp [eddy]
lemma eddy_lt(n:ℕ) : eddy n < 1/4:=by unfold eddy; nlinarith only [show 0<(1/4:ℝ)^n by positivity]
lemma eddy_small (p:|z-1| ≤ eddy n): |z-1| ≤ 1/4:= p.trans (eddy_lt n).le
noncomputable def re_p(b:ℝ):ℝ:= z+b*a/(zoomM L)^n
lemma stirZ (Q:Funds L)(p:Premier L n a)(h:|z-1| ≤ eddy n): |re_p L n a z Q.adjustment-1| ≤ eddy (n+1):=by
 let T:=fareMax L n; let K:=zoomM L; have k:= zoomM_p L; let b:=(1/4:ℝ)^n;
 unfold re_p; rw [show z+ Q.adjustment*a/zoomM L^n-1=(z-1)+Q.adjustment*a/zoomM L^n by ring]; refine le_trans (abs_add_le ..) (le_trans (add_le_add h (show |Q.adjustment * a / zoomM L^n|≤ b/8 from ?_ )) ?_)
 · have ht:0<K^n:=pow_pos k _; rw [abs_div, abs_of_pos (show 0 < zoomM L^n from ht)]; rw [abs_mul, div_le_iff₀ ht]; apply (mul_le_mul Q.small p.big (abs_nonneg _) (by norm_num)).trans
   rw [fareMax]; change _*(zoomC L)^n ≤ b/8*K^n; rw [show b/8*K^n= 1/8*((1/4)*K)^n from by unfold b; rw [mul_pow]; ring]
   have hx:=zoomC_p L; apply mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith only [hx]) ?_ _) (by norm_num)
   have he:= show 0 ≤ (L.val:ℝ)^4 by positivity
   unfold zoomC K zoomM; linarith only [he]
 unfold b eddy; rw [pow_succ]; nlinarith only [show 0<(1/4:ℝ)^n from by positivity]
end YM.CF.QuadClock
