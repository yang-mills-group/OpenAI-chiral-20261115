import YM.CF.BPress.Pf.High
import YM.CF.BPress.Spin.Stoop
/-! Extension at zero in power norm: no differentiation of infinite-torus eigenvectors; exact population projection on original tilted ket. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Pf
open Function Filter NormedSpace Finset Fock Spin Quad Spin.Cellar Spin.Cellar.Pass
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {I:Type}[Fintype I][LinearOrder I][Nonempty I] {S J:Finset I}{A P Q L T: Op I}{x:Wave I}{ε a:ℝ}
def light (P Q:Finset I): Finset (Finset I):= univ.filter fun i=> P⊆i∧ Disjoint i Q -- names conflicts
-- presence P and absence Q
abbrev occupy (P Q:Finset I): FC I:= cutM (light P Q)
namespace Arrival
def board (S J:Finset I)(u:ℝ):= warp (cutM S) (cutM J) (1-(cutM S+cutM J)) u
lemma footM (S J:Finset I)(h:Disjoint S J)(u:ℝ): board S J u=Matrix.diagonal fun i=> (if i∈ S then (u:ℂ)⁻¹ else 1)*(if i∈J then (u:ℂ) else 1):=by
 unfold board warp; ext i j; by_cases g:i=j; subst j; by_cases p:i∈S; have he:i∉ J:= disjoint_left.mp h p; simp [cutM,p,he]; by_cases t:i∈J <;> simp [cutM,p,t]; simp [cutM,g]
def ψ(S J: Finset I)(u:ℝ): FC I:= (u:ℂ) ^ S.card • quant (board S J u)
def powerK (S J t: Finset I):= (S.card-(t∩S).card)+(t∩J).card
lemma ride (h:Disjoint S J)(e:a≠0) (t : Finset I) : acts (ψ S J a) (basisKet t)=(a:ℂ)^powerK S J t • basisKet t:=by
 rw [ψ,act_smul,footM _ _ h,quant_diag,diag_basis,smul_smul]; congr 1; rw [prod_mul_distrib]; let u:ℂ:=a
 have hz (v:ℂ)(S:Finset I):(∏ i∈t,if i∈S then v else 1)=v^(t∩S).card:=by rw [←prod_filter, prod_const]; congr 2 -- tune
 rw [hz,hz,powerK,pow_add, ←mul_assoc]; congr 1; rw [inv_pow]; have hp:= card_le_card (inter_subset_right (s₁:=t) (s₂:=S)); have he: (a:ℂ) ≠0:=Complex.ofReal_ne_zero.mpr e; nth_rw 1 [show S.card=(S.card-(t∩S).card)+(t∩S).card from (Nat.sub_add_cancel hp).symm]; rw [pow_add,mul_inv_cancel_right₀ (pow_ne_zero _ he)]
lemma attains (h:Disjoint S J)(u:Wave I): Tendsto (fun a:ℝ=>acts (ψ S J a) u) (𝓝[>] 0) (𝓝 (acts (occupy S J) u)):=by
 have H(t:Finset I): powerK S J t=0 ↔ t∈light S J:=by
    have he:(t∩S).card≤ S.card:=card_le_card inter_subset_right; have hg:S.card≤ (t∩S).card↔ S ⊆ t:=by
       refine ⟨fun q=>?_ ,fun q=>?_⟩; have hp:= Finset.eq_of_subset_of_card_le (s:=t∩ S) inter_subset_right q; rw [←hp]; exact inter_subset_left; rw [inter_eq_right.mpr q]
    simp [powerK,light,Nat.sub_eq_zero_iff_le, hg, ← Finset.disjoint_iff_inter_eq_empty] -- tune hg orientation
 let D(t:Finset I):=u.ofLp t • basisKet t; have e' : u=∑ t:Finset I,D t:=(basis_expand u).symm
 rw [e']; simp_rw [map_sum]; refine tendsto_finsetSum _ fun t _=>?_ ; unfold D; simp_rw [map_smul,cut_basis]
 let F:= fun a:ℝ=> u.ofLp t • ((a:ℂ)^powerK S J t • basisKet t); refine Tendsto.congr' (f₁:=F) ?_ ?_ -- tune parameters
 · filter_upwards [self_mem_nhdsWithin] with y hy; rw [ride h (by exact ne_of_gt hy)]
 have ht: Tendsto F (𝓝[>] 0) (𝓝 (F 0)):= (show Continuous F by unfold F; fun_prop).continuousWithinAt.tendsto
 by_cases g:t∈ light S J
 · rw [if_pos g]; simpa only [F,(H t).mpr g,pow_zero,one_smul] using ht
 rw [if_neg g]; simpa only [F, Complex.ofReal_zero,zero_pow (mt (H t).mp g),zero_smul,smul_zero] using ht
lemma det_scale (u:ℝ)(p:IsStarProjection A)(e:A.trace=(S.card:ℂ)) : (1+(u-1) • A).det=(u:ℂ)^S.card:=by
 obtain ⟨U,T,f⟩:=spot_projection _ p; have ht:T.card=S.card:=Nat.cast_injective (R:=ℂ) (by rwa [f,trace_twist,trace_cut] at e); rw [f,←map_smul,show 1+(twist U) _=twist U (1+(u-1) • cutM T) from by rw [map_add,map_one],det_twist]; rw [show (1+(u-1) • cutM T)= Matrix.diagonal fun i=> if i∈T then (u:ℂ) else 1 from ?_,Matrix.det_diagonal, ← Finset.prod_filter]; simp [ht]
 ext i j; by_cases h:i=j; subst j; by_cases t:i∈T <;> simp [cutM,t]; simp [cutM,h]
lemma skate (u:ℝ)(v:0<u)(p:Top A x) (h:Disjoint S J) (X:Pass (cutM S) (cutM J) L A ε):
 acts (ψ S J u) x=acts (quant (slide (cutM S) (cutM J) L A u)) x:=by
 rw [X.rapid u v]; let V:=cutM S; let D:= rent1 V A; let T:= u • D+rent0 V A; let B:=warp (cutM S) (cutM J) L u; have he:T*A=T:=by unfold T; rw [add_mul,Algebra.smul_mul_assoc,X.ray1',X.ray0']
 have hh: A*T=T:=by unfold T; rw [mul_add, Algebra.mul_smul_comm, X.ray1,X.ray0]
 rw [psiSp (u:=u), quant_mul,act_smul,act_mul]; change _= acts (quant B) (acts (quant T) x); rw [operates p (hh.trans he.symm), map_smul]; congr 1; symm; rw [terrace,hh,he, show T+(1-A)= 1+(u-1) • D by unfold T rent0; rw [sub_smul,one_smul]; change u • D+(A-D)+_= _; abel]; exact det_scale u X.r1 (X.gate1.trace.trans (trace_cut _))
where psiSp {u:ℝ} : ψ S J u=(u:ℂ)^S.card • quant (warp (cutM S) (cutM J) L u):=by unfold ψ board; rw [←X.l0]
lemma enter (X: Pass (cutM S) (cutM J) L A ε) (p:Top A x)(u:Disjoint S J): acts (quant (slide (cutM S) (cutM J) L A 0)) x=acts (occupy S J) x:=by
 let F(t:ℝ):= acts (quant (slide (cutM S) (cutM J) L A t)) x; have he : Continuous F:=by unfold F slide coeff1 coeff0; exact (acts_cont.comp (quant_cont.comp (by fun_prop))).clm_apply continuous_const
 apply tendsto_nhds_unique he.continuousWithinAt.tendsto ((attains u x).congr' ?_)
 filter_upwards [self_mem_nhdsWithin] with y hy; exact skate y hy p u X

lemma coexist {Z: Op I}(h:Disjoint S J)(u:Commute Z (cutM S))(v:Commute Z (cutM J)) : Commute (quant Z) (occupy S J):=by
 have he(t): Commute (quant Z) (ψ S J t):= by
    unfold Commute SemiconjBy ψ; rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,←quant_mul,←quant_mul]; apply congrArg; refine congrArg quant ?_; unfold board warp; simp only [mul_add,add_mul,Algebra.smul_mul_assoc, Algebra.mul_smul_comm,sub_mul,mul_sub,add_mul,mul_add,u.eq,v.eq,mul_one,one_mul]
 apply op_columns; intro i; rw [act_mul,act_mul]; let v:= acts (quant Z); let l:= v (basisKet i); apply tendsto_nhds_unique ((v.continuous.tendsto _).comp (attains h (basisKet i))) -- tune limits comp
 apply (attains h l).congr; intro t; change acts (ψ S J t) (acts _ _)= acts (quant Z) (acts _ _); rw [←act_mul,←act_mul,(he t).eq]
end Arrival
end YM.CF.BPress.Pf
