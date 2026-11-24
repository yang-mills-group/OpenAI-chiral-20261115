import YM.CF.Sods.Fort
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
set_option autoImplicit false
noncomputable section
namespace YM.CF.Sods
open Function Filter Metric Finset Kea
open scoped Topology BigOperators Matrix ContDiff Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {E:Type*}[Fintype E][DecidableEq E][Nonempty E]{k:ℝ}{A:Op E}
lemma coreZ(w:ℂ):∃ t:ℝ,|t|≤Real.pi∧w=(‖w‖:ℂ)*pw t:= by refine ⟨w.arg,abs_le.mpr ⟨(Complex.neg_pi_lt_arg _).le,Complex.arg_le_pi _⟩,?_⟩; exact (Complex.norm_mul_exp_arg_mul_I _).symm -- tune norm
lemma pw_norm(z:ℝ):‖pw z‖=1:= by simp [pw,BZ.phase]
lemma coast(V:UNI E)(x:E→ℂ)(p:‖V.val-Matrix.diagonal x‖≤k):∃ t:E→ℝ,(∀ i,|t i|≤Real.pi)∧ ‖Matrix.diagonal x-Matrix.diagonal (pw∘t)‖≤ Fintype.card E*k:=by
 have he(i:E):|1-‖x i‖|≤k:=by
   let D:=Matrix.diagonal x; let f:= EuclideanSpace.single i (1:ℂ); have hx:‖f‖=1:=by simp [f]
   have hf: acts D f=x i • f:=by
     apply PiLp.ext; intro a; change (acts D f).ofLp a= _; rw [act_at]; by_cases h:a=i<;>simp [D,f,h]
   rw [show (1:ℝ)=‖acts V.val f‖ from ((act_unit_norm V f).trans hx).symm,show ‖x i‖=‖acts D f‖ by rw [hf,norm_smul,hx,mul_one]]
   refine (abs_norm_sub_norm_le ..).trans ?_; rw [show acts V.val f-acts D f=acts (V.val-D) f from ?_]; exact (ContinuousLinearMap.le_opNorm ..).trans (by rw [hx,mul_one]; unfold acts; rw [Matrix.l2_opNorm_toEuclideanCLM]; exact p); symm; change _= (acts (V.val)) f-(acts D) f; simp [acts]
 choose t ht H using (fun i=>coreZ (x i)); refine ⟨t,ht,?_⟩; have ha:0≤k:= (norm_nonneg _).trans p; apply Branch.schur (fun _ _=>k) _ _ (by positivity)
 · intro i j; by_cases h:i=j; swap; · simp [h,ha]
   subst j; rw [Matrix.sub_apply,Matrix.diagonal_apply_eq,Matrix.diagonal_apply_eq,H i]; rw [show (‖x i‖:ℂ)*pw (t i)-(pw∘t) i=(((‖x i‖-1):ℝ):ℂ)*pw (t i) from (by push_cast; simp [sub_mul]),norm_mul,pw_norm,mul_one, Complex.norm_real, Real.norm_eq_abs,abs_sub_comm]; exact he i
 · intro i; simp
 intro i; simp
lemma cost_D (A:Op E)(h:∀ i j, ‖A i j‖≤k)(u:0≤k):‖A‖≤ Fintype.card E*k:= Branch.schur _ _ _ (by positivity) h (fun i=>by simp) (fun i=>by simp)
-- fit exact angle trace with last pivot
lemma mojo (t:E→ℝ):Matrix.diagonal (pw∘t)∈unitary (Op E):=by
 apply Matrix.mem_unitaryGroup_iff.mpr
 rw [show star _=Matrix.diagonal (star ∘ (pw∘t)) by ext i j; by_cases h:i=j<;>simp [h,Ne.symm],Matrix.diagonal_mul_diagonal]; ext i j; by_cases e:i=j<;>simp [e,BZ.phase_one,pw,Matrix.one_apply]
 exact BZ.phase_one _
lemma mat_curve (E:Type*)[Fintype E][DecidableEq E]:ContDiff ℝ 1 (Matrix.det (R:=ℂ) (n:=E)):=by
 apply contDiff_iff_contDiffAt.mpr; intro i; simp_rw [show Matrix.det=(fun x:Op E=> ∑ p:Equiv.Perm E,p.sign • ∏ j:E,x (p j) j) by ext; rw [Matrix.det_apply]]; refine ContDiffAt.sum (fun p _=>?_); have ht: ContDiff ℝ 1 (fun x:Op E=> ∏ j:E,x (p j) j):=by apply contDiff_prod; intro j _; let P:Op E →ₗ[ℝ] ℂ :=⟨⟨fun x=> x (p j) j, fun _ _=>rfl⟩,fun _ _=>rfl⟩; exact P.toContinuousLinearMap.contDiff
 rcases Int.units_eq_one_or p.sign with h|h <;> rw [h]; simpa using ht.contDiffAt; simpa only [Units.smul_def,Units.val_neg,Units.val_one,neg_smul,one_smul] using ht.neg.contDiffAt -- tune Ext f
lemma spark_D (o:E)(t:E→ℝ)(h:∀ i, |t i|≤ Real.pi)(f:UNI E)(p:f.val.det=1)(v:‖f.val-Matrix.diagonal (pw∘t)‖≤k)(C:ℝ)(l:0<C)(b:∀ U:UNI E, ‖f.val.det-U.val.det‖≤ C* ‖f.val-U.val‖):∃ T:E→ℝ,∑ i,T i=0 ∧ (∀ i, |T i|≤Fintype.card E*Real.pi) ∧ ‖f.val-Matrix.diagonal (pw∘T)‖≤ k+Fintype.card E*(C*k):=by
 let S:ℝ:= ∑ i,t i; let T(i:E):= if i=o then t i-S else t i
 let U:= Matrix.diagonal (pw ∘ t); let A:=Matrix.diagonal (pw ∘ T); have ha(i:E)(p:i≠o):T i=t i:=if_neg p
 have he:T o= -(∑ i∈univ.erase o,t i):=by unfold T S; rw [if_pos rfl, ← add_sum_erase _ t (mem_univ o)]; abel
 have hv:pw (T o)*pw S=pw (t o):=by rw [←phase_a, show T o=t o-S from if_pos rfl,sub_add_cancel]
 have hm: U.det=pw S:=by unfold U pw BZ.phase; rw [Matrix.det_diagonal]; simp only [Function.comp_apply,S,Complex.ofReal_sum,sum_mul,Complex.exp_sum]
 have hp:= b ⟨U,mojo t⟩; change ‖_ - U.det‖ ≤ C*_ at hp; rw [hm,p] at hp; refine ⟨T,?_,fun i=>?_,(norm_sub_le_norm_sub_add_norm_sub f.val U A).trans (add_le_add v ?_)⟩
 · rw [← add_sum_erase _ T (mem_univ o),he,sum_congr (s₁:=univ.erase o) (f:=T) rfl fun i p=> ha i (mem_erase.mp p).1,neg_add_cancel]
 · have hi:Fintype.card E ≥ 1:=Fintype.card_pos; by_cases v:i=o; swap; · rw [ha i v]; exact (h _).trans (le_mul_of_one_le_left Real.pi_pos.le (by exact_mod_cast hi))
   subst i; rw [he,abs_neg]; exact (Finset.abs_sum_le_sum_abs ..).trans ((sum_le_sum (fun i _=> h i)).trans (by rw [sum_const,nsmul_eq_mul]; gcongr ; exact (card_le_card (subset_univ ..)).trans_eq card_univ))
 have hb:‖pw S-1‖ ≤ C*k:=(norm_sub_rev ..).trans_le (hp.trans (mul_le_mul_of_nonneg_left v l.le)); have hc:0≤C*k :=(norm_nonneg _).trans hb; apply cost_D _ _ hc; intro i j; by_cases e:i=j
 · subst j; rw [Matrix.sub_apply,show U i i=pw (t i) from Matrix.diagonal_apply_eq ..,show A i i=pw (T i) from Matrix.diagonal_apply_eq ..]; by_cases k:i=o; swap; · rw [ha i k]; simpa
   subst i; rw [← hv,show pw (T o)*pw S-pw (T o)= pw (T o)*(pw S-1) from (by rw [mul_sub,mul_one]),norm_mul,pw_norm,one_mul]; exact hb
 simp [Matrix.sub_apply,e,U,A,hc]
end YM.CF.Sods
