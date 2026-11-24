import YM.CF.BPress.Bias.Flint
/- Partial Fourier turn: time transform on each tangent fiber. Matrices between site/mom use the same basis. Exact time T extraction including anticut. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Bias
open Function Finset Filter Lattice Laurent Bloch Next.Free Metric Fir Lat Spin Rush Blank
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
attribute [local instance] opCStarAlgebra
variable {N:Side} (k:Site N)
abbrev mer(x:Site N):Site N:=needle x 0
lemma coast(x:Site N): needle (mer x) (x 0)=x:=by simp [mer,needle]
@[simp] lemma mer_tick (k:Site N)(u:Per N):mer (needle k u)=mer k:=by simp [mer,needle]
lemma tick_sum (F:Site N→ℂ) : (∑ x:Site N, if mer x=mer k then F x else 0)=∑ b:Per N,F (needle k b):=by
 rw [←sum_filter]; have ht(x:Site N)(h:mer x=mer k):needle k (x 0)=x:=by rw [←coast x]; unfold needle mer; simp only [update_self]; unfold mer needle at h; unfold needle; rw [h]; simp
 refine sum_bij' (fun x _=> x 0) (fun b _=>needle k b) (fun _ _=>mem_univ _) (fun a _=> by simp) (fun a h=>ht a (mem_filter.mp h).2) (fun a _=>by simp [needle]) (fun a h=>by rw [ht a (mem_filter.mp h).2]) -- WRONG goal sum_bij depends function needle
abbrev φ(u b:Per N):= BZ.phase (Lat.principal b)^u.val
abbrev rhythm(k x: Site N):=∏ i∈univ.erase (0:Axis), BZ.phase (pm k i)^(x i).val
lemma fracF(x:Site N)(b:Per N): frequency (needle k b) x=φ (x 0) b * rhythm k x:=by
 unfold frequency; rw [←mul_prod_erase _ _ (mem_univ (0:Axis))]; refine congrArg₂ (· * ·) ?_ ?_; · simp [φ,pm,needle];
 unfold rhythm; exact prod_congr rfl fun i t=>by simp [pm,needle,ne_of_mem_erase t]
lemma clockφ(b u: Per N): frequency (needle 0 b) (needle 0 u) = φ u b:=by rw [fracF,needle,update_self]; rw [show rhythm (0:Site N) (needle 0 u)=1 from prod_eq_one (fun i t=> by simp [needle,ne_of_mem_erase t])]; simp
abbrev pinω(u:Per N) (n:ℕ):=wind (needle 0 u) (n • (step 0 : Cover))
lemma φ_step (b u: Per N)(n:ℕ) : pinω u n * φ (u+(n: Per N)) b= φ u b* markFreq b (n:ℝ):=by
 have hx:= freq_advance (needle 0 b) (needle 0 u) (n • (step 0:Cover)); unfold pinω; rw [show needle (0:Site N) u+_=needle (0: Site N) (u+(n: Per N)) from ?_, clockφ, clockφ] at hx -- placeholder
 rw [hx]; congr 1; unfold mode markFreq; congr 1; simp [step_apply,pm,tmap, mel, needle,sum_ite_eq',mul_ite]; ring
 rw [map_nsmul,wrap_step]; funext i; by_cases h:i=0 <;> simp [h,nsmul_eq_mul,needle,step_apply]
lemma φ_one (x y : Per N):φ x y*star (φ x y)=1:=by unfold φ; rw [star_pow,← mul_pow,BZ.phase_one,one_pow]
lemma φ_diff (x y : Per N)(h:x≠y) : ∑ a: Per N,star (φ a x)*φ a y=0:=by
 let f(a:Per N):ℂ:=star (φ a x)*φ a y; let c b:=markFreq (N:=N) b 1; let Q:=star (c x)*c y; have he(a:Per N):f (Equiv.addRight (1:Per N) a)=Q*f a:=by
    have hy:=φ_step x a 1; have hu:=φ_step y a 1; push_cast at hy hu
    let H:=pinω a 1; have hz:star H*H=1:=by change star (fee _)*fee _=1; rw [fee_real,fee_one]
    change star (φ (a+1) x)*φ (a+1) y = _; rw [show star (φ (a+1) x)*φ (a+1) y= star (H*φ (a+1) x)*(H*φ (a+1) y) by rw [star_mul,← mul_assoc, mul_assoc _ _ H,hz,mul_one], show H*φ (a+1) x=_ from hy, show H*φ (a+1) y=_ from hu,star_mul]; unfold Q c f; ring
 let F:=∑ a:Per N,f a; by_contra H; have hx:Q=1:=mul_right_cancel₀ (show F≠0 from H) (by unfold F; rw [one_mul,mul_sum]; simp_rw [← he]; exact Equiv.sum_comp ..); have hb(b:Per N):c b=BZ.phase (Lat.principal b):=by unfold c markFreq; rw [mul_one]; rfl
 apply h; apply phase_inj; rw [← hb, ← hb]; calc
    _ = c x*Q:=by rw [hx,mul_one]
    _ = _:=by rw [← mul_assoc,hb x, BZ.phase_one,one_mul] -- tune
variable (N)
abbrev Nsq:ℂ:= (Real.sqrt (N.val:ℝ):ℂ)
lemma sqNe : Nsq N≠0 := by have hp:= Real.sqrt_pos.mpr (nPos N); unfold Nsq; exact_mod_cast hp.ne'
lemma sqMore : Nsq N * Nsq N=(N.val:ℂ):= by rw [← Complex.ofReal_mul, Real.mul_self_sqrt (nPos N).le,Complex.ofReal_natCast]
@[simp] lemma sq_star : star (Nsq N)= Nsq N:=by simp [Nsq]
private def Ω : Op (Per N):=Matrix.of fun x y=> φ x y/Nsq N
local notation "ΩN"=> Ω N
lemma φ_cols(x y:Per N): ∑ v: Per N,star (φ v x/Nsq N)*(φ v y/Nsq N)=if x=y then (1:ℂ) else 0:=by
 simp_rw [star_div₀,sq_star,div_mul_div_comm, sqMore, ←sum_div]; by_cases h:x=y; swap; · rw [φ_diff _ _ h,zero_div,if_neg h]
 rw [h,if_pos rfl]; simp_rw [show ∀ v:Per N, star (φ v y)*φ v y=1 by intro v; rw [mul_comm,φ_one],sum_const,card_univ]; simp [Per]
lemma φ_rows(x y:Per N): ∑ v: Per N,φ x v*star (φ y v)=if x=y then (N.val:ℂ) else 0:=by
 let A:=ΩN; have he:star A*A=1:=by ext i j; rw [Matrix.one_apply]; exact φ_cols N i j
 have hp:= mul_eq_one_comm.mp he; have ht:= Matrix.ext_iff.mpr hp x y; unfold A Ω at ht; simp only [Matrix.mul_apply,Matrix.star_apply,Matrix.of_apply, star_div₀,sq_star, div_mul_div_comm,sqMore,←sum_div, Matrix.one_apply] at ht; rw [div_eq_iff (side_ne _)] at ht; rw [ht]; split <;> simp -- tune
-- time only transform pos or momentum coordinate
abbrev evoke (k x : Site N):=φ (x 0) (k 0)/Nsq N
def temporal : Op (Site N):= Matrix.of fun x k=> if mer x=mer k then evoke N k x else 0
lemma tempUni : temporal N ∈ unitary (Op (Site N)):=by
 apply Matrix.mem_unitaryGroup_iff'.mpr; ext x y; by_cases h:mer x=mer y; swap; · rw [Matrix.one_apply_ne (by intro h; subst x; contradiction), Matrix.mul_apply]; apply sum_eq_zero; intro k _; by_cases g:mer k=mer x; have hu:mer k≠mer y:=g ▸ h; simp [temporal,hu]; simp [temporal,g]
 let F(k:Site N):= star (evoke N x k)*evoke N y k; rw [Matrix.mul_apply]; have ht(k:Site N):(star (temporal N)) x k * (temporal N) k y=if mer k=mer x then F k else 0:=by simp only [temporal, Matrix.of_apply, Matrix.star_apply,← h]; split <;> simp_all only [F,star_zero,zero_mul]
 simp_rw [ht]; rw [tick_sum]; unfold F evoke; simp_rw [needle,update_self]; rw [φ_cols, Matrix.one_apply]; simp only [show (x 0=y 0)=(x=y) from propext ⟨fun hx=> (coast x).symm.trans (by rw [h,hx,coast]),fun hx=> congrFun hx _⟩] -- tune equivalence
-- Full Fourier * inverse temporal
lemma horiz (x y:Site N)(h:x 0≠ y 0) : (Fourier N * star (temporal N)) x y=0:=by
 rw [Matrix.mul_apply]; have hx(k:Site N):Fourier N x k*star (temporal N) k y=if mer k=mer y then Fourier N x k*star (evoke N k y) else 0:=by
    unfold temporal; rw [Matrix.star_apply,Matrix.of_apply]; split <;> rename_i p; · simp [p]
    simp [Ne.symm p]
 simp_rw [hx]; rw [tick_sum]; unfold evoke Fourier; simp only [Matrix.of_apply]; simp_rw [fracF, star_div₀,sq_star]; simp_rw [div_mul_div_comm,needle,update_self]; rw [←sum_div]; apply div_eq_zero_iff.mpr; left
 let A(b:Per N):=φ (x 0) b; let f:=rhythm y x; have hb (b:Per N): A b*f*star (φ (y 0) b)=f*(A b*star (φ (y 0) b)):=by ring
 change (∑ b, A b*f*star (φ (y 0) b))=0; simp_rw [hb]; unfold A; rw [←mul_sum,φ_rows,if_neg h,mul_zero]
end YM.CF.BPress.Bias
