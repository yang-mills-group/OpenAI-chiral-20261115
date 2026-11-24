import ForceSatin.Pizzicato
import YM.Work.C12
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.Taylor
set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option maxHeartbeats 440000
set_option quotPrecheck false
noncomputable section
namespace YM.Regis.Circuit.SpringDay
open Function Filter Metric Lattice Laurent Next.Free Bloch Finset CF CF.Lat CF.Jill CF.Ember CF.Flare CF.Onyx CF.Fir
open Precision Exterior RG Work.F06
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix


-- smooth chord for cutting the symbolic trigonometric price; two-sided cost.
section
variable {E V :Type*} [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup V][NormedSpace ℝ V]
noncomputable abbrev tayM(n:ℕ)(f:ℝ→ E)(t:ℝ): E:=∑ i∈range n, ((i.factorial:ℝ)⁻¹*t^i) • iteratedDeriv i f 0
lemma podium (f:ℝ→E)(n:ℕ)(t R C:ℝ)(h:0 ≤ t)(p:0<R)(u:t≤R)(hc:0≤C)(a:ContDiff ℝ (↑(n+1:ℕ)) f)(P:∀ x:ℝ, |x| ≤ R → ‖iteratedDeriv (n+1) f x‖≤ C) : ‖f t-tayM (n+1) f t‖ ≤ C*t^(n+1):=by
 let B:= Set.Icc 0 R; have hg (x:ℝ)(j:ℕ)(hx:x∈B)(h:j≤ n+1):iteratedDerivWithin j f B x=iteratedDeriv j f x:=iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc p) (a.of_le (by exact_mod_cast h)|>.contDiffAt) hx
 have ht:= taylor_mean_remainder_bound p.le (f:=f) (n:=n) (a.of_le (by simp)|>.contDiffOn) (show t∈B from ⟨h,u⟩) (show ∀ x∈B,_ from fun x hx=> show ‖iteratedDerivWithin (n+1) f B x‖ ≤ C from (hg x _ hx le_rfl) ▸ P x (by rw [abs_of_nonneg hx.1]; exact hx.2)) -- ▸ symmetric? tune
 rw [sub_zero] at ht; rw [show tayM (n+1) f t=taylorWithinEval f n B 0 t from (by rw [taylor_within_apply,sub_zero]; apply sum_congr rfl; intro x p'; rw [hg 0 _ ⟨le_rfl,p.le⟩ (mem_range.mp p').le])]
 exact ht.trans (div_le_self (by positivity) (by exact_mod_cast n.factorial_pos))
lemma podium_v(f:ℝ→E) (n:ℕ)(p:0<n)(t R C:ℝ)(u:|t|≤ R) (e:0<R)(hc:0≤C)(h:ContDiff ℝ n f)(a:∀ x:ℝ,|x|≤ R→ ‖iteratedDeriv n f x‖ ≤ C): ‖f t-tayM n f t‖ ≤ C*|t|^n:= by
 obtain ⟨m,rfl⟩:= Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt p)
 cases le_total 0 t with
 | inl ht=> rw [abs_of_nonneg ht]; exact podium f m _ R _ ht e ((le_abs_self _).trans u) hc h a
 | inr ht=> rw [abs_of_nonpos ht] at u ⊢; let F(x:ℝ):= f (-x); have hf: ContDiff ℝ (↑(m+1:ℕ)) F := h.comp (f:=fun i:ℝ=> -i) (by fun_prop)
            rw [show tayM (m.succ) f t=tayM _ F (-t) from ?_,show f t= F (-t) from (by simp [F])]
            apply podium F m _ R C (by linarith) e u hc hf; intro x g; unfold F; rw [iteratedDeriv_comp_neg,norm_smul,norm_pow]; simp only [norm_neg,norm_one,one_pow,one_mul]; exact a (-x) (abs_neg x ▸ g)
            apply sum_congr rfl; intro i h; unfold F; rw [iteratedDeriv_comp_neg,smul_smul,neg_zero]; congr 1; rw [mul_assoc,← mul_pow]; simp -- tune indentation
-- joint purity
lemma planar (S:Set V)(b:IsCompact S)(f:V→ℝ→E)(h:ContDiff ℝ ∞ (uncurry f))(n:ℕ)(p:0<n)(w:ℝ)(hw:0<w):∃ C:ℝ,0<C∧∀ i∈S,∀ t:ℝ,|t|≤w→ ‖f i t-tayM n (f i) t‖ ≤ C*|t|^n:=by
 have ht:= (Work.C12.contDiff_partialJets h n).continuous.norm; obtain ⟨A,a⟩:= (b.prod (isCompact_closedBall (0:ℝ) w)).bddAbove_image ht.continuousOn
 refine ⟨max A 1,lt_max_of_lt_right one_pos,fun i y t z=> podium_v (f i) n p t w (max A 1) z hw (zero_le_one.trans (le_max_right ..)) ?_ (fun x v=>?_ )⟩
 · exact ((h.comp (contDiff_const.prodMk contDiff_id)).of_le (by exact_mod_cast le_top)) -- tune
 rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]; exact (a ⟨(i,x),Set.mk_mem_prod y (mem_closedBall_zero_iff.mpr v),rfl⟩).trans (le_max_left ..)
end
-- coordinate vector; `step`; no truncation costs charged on Mark. 
lemma axoplasm(k:ℕ)(n:ℕ)(g:n<k)(v:ℝ): ∑ i∈range k,(debtM k i)* (↑(((i:ℝ)*v)^n):ℂ)= (↑((-v)^n):ℂ):=by
 have he:= line_g k n g (-1) v (1:ℂ); simp only [smul_eq_mul,mul_one] at he; simp only [Complex.ofReal_pow,Complex.ofReal_mul,Complex.ofReal_natCast,Complex.ofReal_neg] at *; simpa only [Complex.ofReal_one,neg_one_mul] using he
lemma stencil_eff (f:ℝ→ℂ)(v:ℝ)(k:ℕ): ∑ i∈range k,(debtM k i)* tayM k f ((i:ℝ)*v) = tayM k f (-v):=by
 unfold tayM; simp_rw [Finset.mul_sum, Complex.real_smul,Complex.ofReal_mul (↑_ ) _] -- tune
 rw [sum_comm]; apply sum_congr rfl; intro i g
 let U:ℂ:= (↑((i.factorial:ℝ)⁻¹):ℂ); let V:=iteratedDeriv i f 0
 change (∑ j∈range k,debtM k j*(_*V))=U*_ *V; calc
   _=(∑ j∈range k,debtM k j * (↑(((j:ℝ)*v)^i):ℂ))*(U*V):=by rw [Finset.sum_mul]; apply sum_congr rfl; intro j h; unfold U; ring
   _=_:=by rw [axoplasm k i (mem_range.mp g)]; ring
-- bank absolute, can pay separable constant.H parameters after k
lemma verdant (n:ℕ)(p:0<n)(f:Bin→ℂ)(h:ContDiff ℝ ∞ f)(x:Axis):∃ C:ℝ,0<C∧∀ i:Bin, ‖i‖≤2*Real.pi → ∀ v:ℝ, |v|≤2*Real.pi → ‖f (i+beam x (-v))- ∑ j∈range n,debtM n j*f (i+beam x ((j:ℝ)*v))‖ ≤ C*|v|^n:=by
 let A(i:Bin)(v:ℝ):= f (i+beam x v); let X:=2*Real.pi*(n:ℝ); have hx:0<X:= by unfold X; positivity
 have hp: ContDiff ℝ ∞ (uncurry A):= h.comp (show ContDiff ℝ ∞ (fun p:Bin×ℝ=> p.1+beam x p.2) by unfold beam; fun_prop); -- tune
 obtain ⟨C,u,P⟩:= planar (closedBall 0 (2*Real.pi)) (isCompact_closedBall ..) A hp n p X hx; obtain ⟨K,hK,H⟩:= bead_bound n; let y:= (n:ℝ); refine ⟨C+ K*(C*y^n),by positivity [y],fun i z v hv=>?_⟩
 let B(t:ℝ):=A i t-tayM n (A i) t
 have he(t:ℝ)(h:|t|≤X): ‖B t‖ ≤ C * |t|^n:=P i (mem_closedBall_zero_iff.mpr z) t h; have ht:1≤y:=by unfold y; exact_mod_cast p -- tune
 have hy:0<y:=zero_lt_one.trans_le ht; have hh: 0≤2*Real.pi:= by positivity
 change ‖A i (-v)-∑ j∈range n,debtM n j*A i ((j:ℝ)*v)‖ ≤_
 rw [show A i (-v)-_=B (-v)- ∑ j∈range n,debtM n j*B ((j:ℝ)*v) from (by unfold B; simp_rw [mul_sub,sum_sub_distrib]; rw [stencil_eff]; abel)]
 let W:= C*(y*|v|)^n; exact (norm_sub_le ..).trans ((show _ ≤ C*|v|^n+ K*W from add_le_add ((he (-v) (by rw [abs_neg]; exact hv.trans (le_mul_of_one_le_right hh ht))).trans_eq (by rw [abs_neg])) (by
    apply (norm_sum_le ..).trans
    have he(j:ℕ)(z:j<n): ‖B ((j:ℝ)*v)‖ ≤ W:=by
        have ht : 0≤ (j:ℝ):=Nat.cast_nonneg _; have hz:(j:ℝ) ≤ y:=by unfold y; exact_mod_cast z.le
        have hk: |(j:ℝ)*v|≤ y*|v| := by rw [abs_mul,abs_of_nonneg ht]; gcongr
        apply (he _ (hk.trans ((mul_le_mul_of_nonneg_left hv hy.le).trans_eq (mul_comm ..)))).trans; unfold W; gcongr
    refine (sum_le_sum (g:=fun j=>|bead n (-1) j| *W) (fun j h=>by rw [norm_mul, mul_comm]; unfold debtM; rw [Complex.norm_real,Real.norm_eq_abs]; apply le_of_le_of_eq (mul_le_mul_of_nonneg_right (he j (mem_range.mp h)) (abs_nonneg _)) (mul_comm ..))).trans ?_
    rw [←Finset.sum_mul]; gcongr; exact H (-1) (by norm_num))).trans_eq (by unfold W; rw [mul_pow]; ring))
-- CUT θ
open MeasureTheory
local notation "π" => Real.pi
def fog : ContDiffBump (0:Bin):= ⟨π/4,π/2,by positivity,by linarith [Real.pi_pos]⟩
def puff : ContDiffBump (0:Bin):= ⟨π/64,π/32,by positivity,by linarith [Real.pi_pos]⟩
lemma fog_s (x:Bin)(p: ‖x‖≤Real.pi/4):fog x=1 := fog.one_of_mem_closedBall (mem_closedBall_zero_iff.mpr p)
lemma fog_far (x:Bin)(p: Real.pi/2 ≤ ‖x‖):fog x=0 := fog.zero_of_le_dist (show fog.rOut≤_ from dist_zero_right x ▸ p)
lemma fog_c: ContDiff ℝ ∞ (fog:Bin→ℝ) := fog.contDiff
abbrev offFog(f:Bin→ℂ)(x:Bin):ℂ:= (1-(puff x:ℂ))*f x
lemma offClear (f:Bin→ℂ)(x:Bin)(p:Real.pi/32≤‖x‖): offFog f x = f x:=by rw [offFog,puff.zero_of_le_dist (show _ from dist_zero_right x ▸ p)]; simp
lemma offDiff (f:Bin→ℂ)(hf:∀ x:Bin,x≠0→ContDiffAt ℝ ∞ f x): ContDiff ℝ ∞ (offFog f):=by
 apply contDiff_iff_contDiffAt.mpr; intro x; by_cases h:x=0
 · subst x; refine (contDiffAt_const (c:=(0:ℂ))).congr_of_eventuallyEq ?_; filter_upwards [closedBall_mem_nhds (0:Bin) (show 0<Real.pi/64 by positivity)] with i p; unfold offFog; rw [puff.one_of_mem_closedBall p]; push_cast; rw [sub_self,zero_mul] -- tune instance syntax
 apply ContDiffAt.mul _ (hf x h); exact contDiffAt_const.sub (Complex.ofRealCLM.contDiff.contDiffAt.comp x puff.contDiff.contDiffAt)
-- no seam
lemma peerBond {x y:Bin}(h:‖x‖+‖y‖<2*Real.pi)(u:peers x y): x=y:=by
 obtain ⟨z,rfl⟩:=u; by_contra! e; obtain ⟨i,t⟩:= Function.ne_iff.mp e; have hz:z i≠0:=fun g=>t (by dsimp [stem]; simp [g]); have hv:1≤ |(z i:ℝ)|:= by exact_mod_cast (show (1:ℤ)≤ |z i| from (by have h:=abs_pos.mpr hz; omega))
 let Y:=x+stem z; have he: ‖Y‖+‖x‖ ≥ 2*Real.pi:=by
    calc
       _ ≤ (2*Real.pi)*|(z i:ℝ)|:=le_mul_of_one_le_right (by positivity) hv
       _ = |(Y i-x i)|:=by change _=|x i+2*Real.pi*(z i)-x i|; rw [add_sub_cancel_left, abs_mul,abs_of_nonneg (by positivity : 0≤ 2*Real.pi)] -- tune
       _ ≤ _:= (abs_sub ..).trans (add_le_add (b_abs Y i) (b_abs x i)) -- tune abs_sub
 linarith

#print axioms podium_v
#print axioms verdant
end YM.Regis.Circuit.SpringDay
