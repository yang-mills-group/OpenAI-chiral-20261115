import YM.CF.Onyx.Vote
set_option autoImplicit false
noncomputable section
namespace YM.CF.Onyx
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill Flare
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open YM.Stationary (Gaia exileE)
variable {N: Side}{j:ℕ}{M:Male}{r C D:ℝ}{a:Axis}
def soft (R D:ℝ):= (R/D)^2
def sulk (s:Offset N)(j:ℕ)(M:Male)(R D:ℝ)(A:Site N→Peb)(k:Site N):= Real.exp (-(soft R D*disk j M (glen s k))) • A k
def bore(s:Offset N)(R:ℝ)(z:Cover)(A:Site N→Peb):Peb:= (R^3/(N.val:ℝ)^4:ℝ) • liv A s z
def riseX (R:ℝ)(z:Cover):Gaia:=moor fun i=> (z i:ℝ)/R
lemma spanK(s:Offset N)(j:ℕ)(M:Male)(R D:ℝ)(hr:0<R)(hD:0<D)(x:Cover)(A:Site N→Peb):bore s R x A-bore s R x (sulk s j M R D A)=(R^3/(N.val:ℝ)^4:ℝ) • ((soft R D:ℂ) •(liv (flow s j M (soft R D) A) s x)):=by
 let y:=soft R D; have hy:0<y:=by unfold y soft; positivity
 have he:(y:ℂ)≠0:=by exact_mod_cast hy.ne'
 unfold bore; rw [← smul_sub]; congr 1; unfold liv; rw [← sum_sub_distrib,Finset.smul_sum]; refine sum_congr rfl fun i _=>?_ ; let d:=disk j M (glen s i)
 rw [← smul_sub,smul_comm (soft R D:ℂ) (charK s i x),sulk, flow]; change _= _ • ((y:ℂ) •(damp y (d:ℂ) • A i))
 unfold damp; rw [smul_smul (y:ℂ),←mul_assoc,mul_inv_cancel₀ he,one_mul,sub_smul,one_smul]; rw [← BZ.ofReal_action,Complex.ofReal_exp]; push_cast; simp only [y,d,neg_mul]
structure Yard (N:ℕ→Side)(R:ℕ→ℝ) :Prop where
 pos : ∀ i,0<R i
 high : Tendsto R atTop atTop
 water:Tendsto (fun i=>R i*pinch (N i)) atTop (𝓝 0)
 even:∀ i,Even (N i).val -- relax later if needed
namespace Yard
variable {S:ℕ→Side}{R:ℕ→ℝ}(h:Yard S R)
include h
lemma thinner(K:ℝ): Tendsto (fun i=> K/R i) atTop (𝓝 0):=by
 have hx:= tendsto_inv_atTop_zero (𝕜:=ℝ) |>.comp h.high; simpa only [Function.comp_def,← div_eq_mul_inv,mul_zero] using hx.const_mul K
lemma muster(x:ℝ) :∃ d:ℕ→ℤ, Tendsto (fun i=>R i*extent (S i) (d i)) atTop (𝓝 x):=by
 choose d hd using fun i=> fragment (R i * pinch (S i)) (mul_pos (h.pos i) (pinch_pos _)) x; refine ⟨d,?_⟩; rw [tendsto_iff_norm_sub_tendsto_zero]; refine squeeze_zero (fun _=>norm_nonneg _) (fun i=>?_) h.water
 rw [norm_sub_rev,Real.norm_eq_abs]; unfold extent; simpa [mul_left_comm,mul_assoc] using hd i
lemma loom (x:Gaia)(z:ℕ→Cover)(hx:Tendsto (fun i=>riseX (R i) (z i)) atTop (𝓝 x))(e:x≠0):∃ (a:Axis)(d:ℕ→ℤ)(w:ℝ),1≤w ∧ ∀ᶠ i in atTop, let r:=extent (S i) (d i); |r|≤w/R i ∧ 1 ≤ ‖drum (r * z i a)‖ ∧ 8*w/R i<zone∧ R i * pinch (S i)≤1 :=by
 obtain ⟨a,u⟩:∃ a:Axis,x a≠0:=by contrapose! e; ext i; simp [e]
 let v:= Real.pi/x a; obtain ⟨d,g⟩:= h.muster v; let F(i:ℕ):= extent (S i) (d i); let W:=|v|+1; have hv: |v|<W:=by unfold W; linarith
 refine ⟨a,d,W,by unfold W; linarith [abs_nonneg v],?_⟩
 have ht:Tendsto (fun i=>F i*z i a) atTop (𝓝 Real.pi):=by
    have hz:Tendsto (fun i=> ((riseX (R i) (z i)) a)) _ (𝓝 (x a)) := ((show Continuous fun t:Gaia=>t a from (PiLp.continuous_apply ..)).continuousAt.tendsto).comp hx
    convert (g.mul hz) using 1 -- nhds ext
    · ext i; change _=R i*F i*((z i a:ℝ)/R i); have hp:=h.pos i; field_simp
    rw [show v*x a=Real.pi by unfold v; field_simp]
 filter_upwards [cymbal _ ht,g.abs.eventually (gt_mem_nhds hv),(h.thinner (8*W)).eventually (gt_mem_nhds zone_pos),h.water.eventually (gt_mem_nhds one_pos)] with i he ht hx hz
 refine ⟨?_, he,hx,le_of_lt hz⟩; have hp:= h.pos i; rw [le_div_iff₀ hp,mul_comm, ←abs_of_pos hp,← abs_mul]; exact le_of_lt ht
lemma sheen (H:1≤j)(p:0<r)(t:0<C)(x:Gaia)(z:ℕ→Cover)(hx:Tendsto (fun i=> riseX (R i) (z i)) atTop (𝓝 x))(e:x≠0):∃ c:ℝ,0<c∧∀ᶠ i in atTop,∀ D:ℝ,0<D→∀ (s:Offset (S i))(M:Male)(A:Site (S i)→Peb),FormU s j M r C A→‖bore s (R i) (z i) A-bore s (R i) (z i) (sulk s j M (R i) D A)‖≤ c/D^2:=by
 obtain ⟨a,d,T,g,W⟩:= h.loom x z hx e; obtain ⟨c,hc,Z⟩:= rain H p t g a; refine ⟨c/Real.pi^4,by positivity,?_⟩; filter_upwards [W] with i hi; obtain ⟨hx,hu,he,hp⟩:=hi
 intro D u s M A f; have hr:= h.pos i; let y:=soft (R i) D; have hy:0<y:=by unfold y soft; positivity
 rw [spanK s j _ _ _ hr u,norm_smul,norm_smul, Real.norm_of_nonneg (by positivity), Complex.norm_real,Real.norm_of_nonneg hy.le]; refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Z (h.even i) f hr hp hy he _ hx _ hu) hy.le) (show 0≤ R i^3/((S i).val:ℝ)^4 by positivity)).trans_eq ?_; change _=_; unfold y soft pinch; have hz:= nPos (S i); field_simp -- tune
end Yard
end YM.CF.Onyx
