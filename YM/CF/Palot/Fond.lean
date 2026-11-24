/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.CF.Palot.Rill
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Palot
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo
open scoped Classical
open RG Push Push.AbsoluteSums Push.AbsoluteSums.Ursell Push.AbsoluteSums.Graph Push.AbsoluteSums.Coef Push.AbsoluteSums.Gas
open Trees
variable {n:Side}{ι E: Type*}[Fintype ι][NormedCommRing E][NormOneClass E][NormedAlgebra ℝ E][CompleteSpace E]
lemma arctic(R:ι→ι→Prop)(k:Hard R)(u:ι→E)(C q:ℝ)(p:0≤C)(hq:0<q)(hp:q<1)(h:∀ m:ℕ,‖tuneC R u m‖≤ C*q^m): exp (∑' i,tuneC R u i)=∑ s:Finset ι,pace R u s:=by
 let b:=(1+q⁻¹)/2; have hb:1<b:=by unfold b; have he := (one_lt_inv₀ hq).2 hp; linarith
 have hi:q*b<1:=by unfold b; rw [←mul_div_assoc,mul_add]; field_simp; linarith
 let L:=Set.Ioo (-b) b; have h0:0∈L:=⟨by linarith,by linarith⟩; have h1:1∈L:=⟨by linarith,hb⟩; have hc:IsOpen L:=isOpen_Ioo; have hL:IsPreconnected L:=(convex_Ioo (-b) b).isPreconnected
 let F(n:ℕ)(t:ℝ):=t^(n+1) • tuneC R u n; let D(n:ℕ)(t:ℝ):=((n+1:ℝ)*t^n) • tuneC R u n
 let f t:= ∑' i,F i t; let d t:= ∑' i,D i t
 let W(n:ℕ):= C*((n:ℝ)+1)*(q*b)^n; have hw:0≤ q*b:=mul_nonneg hq.le (by linarith); have hv: ‖q*b‖ < 1:=by rwa [Real.norm_of_nonneg hw]
 have he: Summable W:=by
    have he: Summable fun n:ℕ => ((n:ℝ)^1 * (q*b)^n)+ (q*b)^n:= (summable_pow_mul_geometric_of_norm_lt_one 1 hv).add (summable_geometric_of_lt_one hw hi)
    apply (he.mul_left C).congr; intro i; unfold W; ring
 have hh(n)(t)(ht:t∈ L): ‖D n t‖≤ W n:=by
    have hT:‖t‖ ≤ b:=by rw [Real.norm_eq_abs]; exact abs_le.mpr ⟨ht.1.le,ht.2.le⟩
    unfold W D; rw [norm_smul,norm_mul,norm_pow,Real.norm_of_nonneg (show (0:ℝ)≤n+1 by positivity),mul_pow]
    refine (mul_le_mul (show ((n+1:ℝ)*‖t‖^n)≤(n+1:ℝ)*b^n from (by gcongr)) (h n) (norm_nonneg _) (by positivity)).trans (le_of_eq (by ring)) -- tune positivity b
 have hg(x)(hx:x∈L):HasDerivAt f (d x) x:=by
    refine hasDerivAt_tsum_of_isPreconnected he hc hL (fun n y _=>?_) hh h0 ?_ hx
    · convert! ((hasDerivAt_pow (n+1) y).smul_const (tuneC R u n)) using 1; unfold D; push_cast; rfl
    simp only [F,pow_succ,mul_zero,zero_smul]; exact summable_zero
 let U(n:ℕ)(t:ℝ):=t^n • stoneC R u n; let s:= Fintype.card ι; let P(t:ℝ):= ∑ n∈ range (s+1),U n t; let V(n:ℕ)(x:ℝ):=((n+1:ℝ)*x^n) • stoneC R u (n+1)
 have hx(x):HasDerivAt P (∑ n∈range s,V n x) x:=by
    let v(n:ℕ):=((n:ℝ)*x^(n-1)) • stoneC R u n
    have he:=HasDerivAt.sum (u:=range (s+1)) (A:=U) (A':=v) (x:=x) fun i _=> (hasDerivAt_pow i x).smul_const _
    convert! he using 1
    · ext z; simp only [P,Finset.sum_apply]
    rw [Finset.sum_range_succ']; simp [V,v] -- tune
 have hx'(x:ℝ)(hX:x∈L):d x * P x=∑ n∈ range s,V n x:=by
    have he'(i)(y:i ∉ range (s+1)):U i x=0:=by unfold U; rw [streamU i _ _ (show s < i by simp only [mem_range,not_lt] at y; omega), smul_zero]
    have hh' : Summable fun i=> ‖U i x‖:= summable_of_ne_finset_zero (s:=range (s+1)) fun i p=> by rw [he' i p,norm_zero]
    have hy :Summable fun i=> ‖D i x‖:= he.of_nonneg_of_le (fun i=>norm_nonneg _) (fun i=> hh i x hX)
    unfold d; rw [show P x=∑' i,U i x from (tsum_eq_sum he').symm,tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hy hh']
    have hj(n:ℕ):∑ i ∈ range (n+1),D i x*U (n-i) x=V n x:=by
       unfold D U V; rw [mul_comm (n+1:ℝ),mul_smul,vane n R k u,smul_sum]; apply sum_congr rfl; intro i h
       rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_smul,smul_smul]; congr 1; rw [mul_assoc, ← pow_add, show i+(n-i)=n from by have he:=mem_range.mp h; omega, mul_comm (i+1:ℝ)]
    simp_rw [hj]; exact tsum_eq_sum fun i l=>by unfold V; rw [streamU _ _ _ (show s < i+1 by simp only [mem_range,not_lt] at l; omega), smul_zero]
 let T(x:ℝ):= P x * exp (- f x)
 have hv(x)(p:x∈L):HasDerivAt T 0 x:=by
    have he:HasDerivAt (fun i=> exp (- f i)) (exp (- f x)*(-d x)) x:= by
       have hh:= HasFDerivAt.comp_hasDerivAt (l:=exp) x (hasFDerivAt_exp (𝕂:=ℝ) (x:=(-f) x)) (hg x p).neg -- defin
       exact hh
    convert! (hx x).mul he using 1; rw [←hx' x p]; ring
 letI : NormedAlgebra ℚ E := NormedAlgebra.restrictScalars ℚ ℝ E
 have hp:T 1=T 0:= hc.is_const_of_deriv_eq_zero hL (fun x p=> (hv x p).differentiableAt.differentiableWithinAt) (fun x p=>(hv x p).deriv) h1 h0
 have hm : T 0=1:= by unfold T P f F; simp only [pow_succ,mul_zero,zero_smul,tsum_zero,neg_zero,exp_zero,mul_one]; rw [sum_range_succ']; simp [U,start]
 have hl : T 1 * exp (f 1)=P 1:= by unfold T; rw [mul_assoc, ←exp_add,neg_add_cancel,exp_zero,mul_one]
 rw [hp,hm,one_mul] at hl; rw [show ∑' i,tuneC R u i=f 1 by simp [f,F], hl]; unfold P; simp only [U,one_pow,one_smul]; exact vanish R u
variable {R:ι→ι→Prop}{X:ι→Support n}{B:ℕ}{a q γ δ:ℝ}{W:ι→ℝ}
lemma shrink_f (F:ι→ E)(c:∀ i,‖F i‖ ≤ W i)(H:Ready X B W a γ δ q):Ready X B (fun i=> ‖F i‖) a γ δ q:=by
 obtain ⟨i,j,p,l,m,g⟩:=H; refine ⟨i,j,p,l,fun _=> norm_nonneg _,fun x=>?_ ⟩; apply budget_mono (g x)
 · intro i; split; exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le; exact le_rfl
 intro i; dsimp only; split; exact mul_le_mul_of_nonneg_right (c i) (Real.exp_pos _).le; exact le_rfl
lemma iceQ (z:Clusters ι)(F:ι→E): ‖guava R F z‖≤‖term R (fun i=> ‖F i‖) z‖:=by
 unfold guava Gas.term; rw [norm_smul,norm_div,norm_div,norm_mul]; apply (mul_le_mul_of_nonneg_left (Finset.norm_prod_le ..) (by positivity)).trans; simp_rw [norm_prod,Real.norm_of_nonneg (norm_nonneg (F _)),div_mul_eq_mul_div]; exact le_rfl
lemma shineP (F:ι→ E)(hr: Hard R)(hx:Tests R X)(v:0≤a)(c:∀ i,‖F i‖ ≤ W i)(H:Ready X B W a γ δ q): Summable (fun z=> ‖guava R F z‖)∧ exp (∑' z, guava R F z)=∑ i:Finset ι,pace R F i :=by
 have he := shrink_f F c H; have hp(i): (X i).Nonempty := by obtain ⟨x,h,-⟩:= hx i i (hr.diag i); exact ⟨x,h⟩
 have hg : Ready X B (fun i=> ‖‖F i‖‖) a γ δ q:=by simp [Real.norm_of_nonneg (norm_nonneg (F _)),he]; -- tune simp
 have hh:= (absolute R (fun i=> ‖F i‖) X B hx hp v hg).2.1
 have hh' := hh.of_nonneg_of_le (fun z=> norm_nonneg (guava R F z)) (fun z=> iceQ z F)
 refine ⟨hh',?_ ⟩; have ht:∑' z,guava R F z= ∑' i,tuneC R F i:= hh'.of_norm.tsum_sigma.trans (tsum_congr fun i=> tsum_fintype _)
 rw [ht]; let C :ℝ:=(n.val^4:ℕ)*γ; have hi:= H.1
 refine arctic R hr F C q (mul_nonneg (Nat.cast_nonneg _) hi.le) (ready_pos X B H) H.2.2.2.1 (fun t=>?_ )
 unfold tuneC; exact le_trans ((norm_sum_le ..).trans (sum_le_sum (fun i _=>iceQ ⟨_,i⟩ F))) (budget_sum (absolute_at R _ X B hx hp v hg t) univ)
end YM.CF.Palot
