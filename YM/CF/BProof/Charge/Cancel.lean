import YM.CF.BProof.Charge.Jerk
import YM.CF.BProof.Angular.Avenue

/- Actual cancellation identity of eq:B-magcancel. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Charge.Form
open Function Filter RG Wilson Lattice Finset Work Micro Moment MeasureTheory Angular Angular.Yard AnalyticBridge.SectorAffine Mag
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
variable {s:Side}(W:Argument s)(Y:Yard s)(T:PathData SU.group)(M:ℕ)(σ:Signed)(x:Site s)(t:Per s)
variable (c:Clip)(β y:ℝ)
def duo (a b:PlaqAxes) := inner ℝ (mark σ a) (∑ p: Space s, curlP σ (origin σ t p+x,b) W)
lemma duo_a (a b:PlaqAxes)(h:¬cross σ a) : duo W σ x t a b=0:=by
 unfold cross at h; push_neg at h; unfold duo; rw [no_mark σ a (by tauto),inner_zero_left]
lemma duo_b (a b:PlaqAxes)(h:cross σ b) : duo W σ x t a b=0:=by unfold duo; rw [jersey0 W σ x t b h,inner_zero_right]
lemma symmetry (a b:PlaqAxes): ∑ σ:Signed, duo W σ x t a b=0:=by
 by_cases h: ∃ e,use a e∧ ¬ use b e
 · obtain ⟨e,u,g⟩:=h
   have he(σ:Signed): duo W (odd σ e) x t a b = -duo W σ x t a b:=by
     by_cases k:cross σ a; swap; · rw [duo_a W σ x t a b k,duo_a W _ x t a b (by simpa [cross] using (show ¬ cross σ a from k)),neg_zero] -- tune simp
     have ht : σ.perm e≠ 0:=by rcases u with p|p; exact p ▸ k.1; exact p ▸ k.2
     unfold duo; rw [odd_jersey W σ x t ht b g, odd_rest σ u,inner_neg_left]
   have H:∑ σ:Signed,duo W (odd σ e) x t a b=∑ σ: Signed,duo W σ x t a b:= Equiv.sum_comp (Equiv.mulRight (Signed.mirror e)) (fun σ=>duo W σ x t a b) -- tune
   simp_rw [he,sum_neg_distrib] at H; linarith only [H]
 have v: ∀ a b:PlaqAxes, (∀ i, (i= (a.val.1) ∨ i=a.val.2) → i=b.val.1 ∨ i=b.val.2)→ a=b:=by decide
 have he:a=b:= v a b (fun i hi=>not_not.mp (show ¬¬use b i from fun p=> h ⟨_,hi,p⟩))
 subst b; exact sum_eq_zero (fun σ k=> by by_cases hh:cross σ a; exact duo_b W σ _ _ _ _ hh; exact duo_a W σ _ _ _ _ hh)
lemma cog (a:PlaqAxes) : (∑ σ:Signed, ∑ p:Space s, L T M c β y (.inr (σ,a,join t p)) W)=0:=by
 let J:=Stack.allShort M; let r:= mA y
 let F (σ:Signed)(p:Space s)(j:RG.Slot):= curlP σ (F03.slotFace j (origin σ t p)) W
 let k:= coeff T a; let z(σ:Signed)(p:Space s)(i j: RG.Slot):= ((β*share)*r*k i*k j)*(inner ℝ (mark σ i.plaq) (F σ p j))
 have he(σ:Signed)(p:Space s): L T M c β y (.inr (σ,a,join t p)) W=∑ i∈J,∑ j∈J,z σ p i j:=by
   unfold L unit root linear; dsimp only [Sum.elim_inr]; rw [rays]; unfold glow; change β*share*inner ℝ (r • ∑ i∈J,k i • mark σ i.plaq) (∑ i∈J, k i • F σ p i)=_
   simp_rw [real_inner_smul_left,sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,mul_sum]; apply sum_congr rfl; intro i hi; apply sum_congr rfl; intro j hj; unfold z; ring -- tune
 have H (i j:RG.Slot): ∑ σ:Signed,∑ p:Space s,z σ p i j=0:=by
   let a':=(wrap s j.offset); have hh (σ:Signed): ∑ p:Space s,z σ p i j=((β*share)*r*k i*k j)*duo W σ a' t i.plaq j.plaq:=by
      unfold z F duo; simp_rw [← mul_sum, inner_sum]; unfold F03.slotFace; simp only [add_comm (wrap s _)]; rfl
   simp_rw [hh, ← mul_sum, symmetry,mul_zero]
 simp_rw [he]; conv_lhs => arg 2; ext; rw [sum_comm]
 rw [sum_comm]; refine sum_eq_zero fun i hi=>?_ ; conv_lhs=> arg 2; ext; rw [sum_comm] -- tune after? get explicit
 rw [sum_comm]; exact sum_eq_zero fun j h=>H i j
lemma linear_lit : (∑ a: Lam s with ¬ColdQ Y M a.center, L T M c β y (.inr a) W)=0:=by
 unfold Lam; rw [sum_filter]; simp_rw [Fintype.sum_prod_type]; let F(σ:Signed)(a:PlaqAxes)(t:Per s):ℝ:=∑ p:Space s,L T M c β y (.inr (σ,a,BProof.join t p)) W
 let X(t:Per s):=∀ j:Y.Index, ¬Y.Vic j (4*M) t
 have h(σ:Signed)(a:PlaqAxes):
    (∑ x:Site s, if ¬ColdQ Y M (Lam.center (σ,a,x)) then L T M c β y (.inr (σ,a,x)) W else 0) = ∑ t:Per s, if ¬X t then F σ a t else 0:=by
     rw [← Equiv.sum_comp (joinEquiv s),Fintype.sum_prod_type]; apply sum_congr rfl; intro t ht; unfold ColdQ; dsimp only [Lam.center]; split
     next h=> unfold F; apply sum_congr rfl; intro i hi; rw [if_pos (by exact h)]; rfl
     next h=> apply sum_eq_zero; intro i hi; rw [if_neg]; exact h
 simp_rw [h]; rw [sum_comm]; refine sum_eq_zero fun x _=>?_ ; rw [sum_comm]; refine sum_eq_zero fun t _=> ?_ ; split; exact cog W T M t c β y x; simp -- if not at outer, split_ifs simp needed
lemma linear_raw (i:Y.Door): L T M c β y (.inl (Y.rise i)) W=0:=by
 unfold L; change _*inner ℝ (mA y • mark 1 (Y.rise i).2) _ = _; rw [no_mark 1 _ (Or.inl rfl)]; simp
lemma linear_direct : (∑ a: Cell s with ¬Y.Marked a,L T M c β y (.inl a) W)=0 := by
 have hn(t:Per s)(p:Space s)(i:TAxis): L T M c β y (.inl (nf t p i)) W=0:=by
   unfold L; change _*inner ℝ (mA y • mark 1 _) _ = _; rw [no_mark 1 _ (Or.inl rfl)]; simp -- tune
 have hh(t:Per s)(i:TAxis):∑ p:Space s,L T M c β y (.inl (hf t p i)) W=0:=by
   let a: PlaqAxes:= (hf t 0 i).2; change (∑ p:Space s, β*c.direct * inner ℝ (mA y • mark 1 a) (curlP 1 (join t p,a) W))=0; rw [← mul_sum, ← inner_sum]
   have h: ∑ p:Space s,curlP 1 (join t p,a) W=0:=by
      have g(p:Space s): origin (1:Signed) t p+(0:Site s)=join t p:=by simp only [add_zero]; exact Signed.act_one _
      simp_rw [← g]; apply jersey0; exact ⟨Fin.succ_ne_zero _,Fin.succ_ne_zero _⟩
   rw [h,inner_zero_right,mul_zero]
 let X(u: Cell s) := if ¬ Y.Marked u then L T M c β y (.inl u) W else 0; rw [sum_filter]; change ∑ a: Cell s,X a=0
 rw [← Equiv.sum_comp plEquiv X,Fintype.sum_sum_type]; change (∑ a:Per s × Space s×TAxis, X (nf a.1 a.2.1 a.2.2))+(∑ a:Per s × Space s×TAxis,X (hf a.1 a.2.1 a.2.2))=0
 rw [Finset.sum_eq_zero (s:=univ) (f:=fun a:Per s× Space s × TAxis=> X (nf a.1 a.2.1 a.2.2)) _,zero_add]; simp_rw [Fintype.sum_prod_type]; refine sum_eq_zero fun t _=>?_ ; rw [sum_comm]; refine sum_eq_zero fun i _=>?_; unfold X; simp_rw [marked_h]; split_ifs; simp; exact hh t i
 intro a _; unfold X; rw [hn,ite_self]
lemma total : (∑ p: Tile s with ¬coldG Y M p, L T M c β y p W)=0:=by rw [sum_filter,Fintype.sum_sum_type]; have h:=linear_direct W Y T M c β y; have g:=linear_lit W Y T M c β y; rw [sum_filter] at h g; convert (congrArg₂ (·+·) h g).trans (add_zero _) using 1; congr! 5
end YM.CF.BProof.Charge.Form
