import YM.CF.Thera.Sage
set_option autoImplicit false
noncomputable section
namespace YM.CF.Thera
open Filter Function MeasureTheory Gauge Matrix Fock SU Finset NormedSpace
open scoped Topology BigOperators Matrix.Norms.Frobenius InnerProductSpace
lemma yet_one: SU.group.Simple:=by
 let a:F₀:=0; let b:F₀:=1; have he:a≠b:=by decide
 refine ⟨⟨_,hutL a,_,curl_v a b 1 he,?_⟩,?_⟩
 · intro ht; have hv:=Matrix.ext_iff.mpr ((curl_x a b 1 he).symm.trans ht) a b; simp [curlA,he,Ne.symm] at hv -- tune
 intro K hl H
 change ∀ A∈_,∀ B∈K,bracket A B∈K at H; rcases eq_or_ne K ⊥ with e|e; exact Or.inl e; right
 obtain ⟨W,p,L⟩:= (Submodule.ne_bot_iff _).mp e -- tune
 have hx:∃ y∈K,∃ a b:F₀,a≠ b∧ (y a b) ≠0:=by
   by_contra! q
   have ha: W=diagonal W.diag:=by ext i j; by_cases h:i=j; simp [h]; rw [q _ p i j h]; simp [h]
   have ht i : W i i=W a a:=by
      by_cases he:i=a; rw [he]
      have hm:= q _ (H _ (curl_v a i 1 (Ne.symm he)) _ p) a i (Ne.symm he)
      change bracket _ W a i=0 at hm
      unfold bracket at hm
      nth_rewrite 1 [ha] at hm; nth_rewrite 2 [ha] at hm -- tune
      simp [curlA,he,Ne.symm] at hm; exact sub_eq_zero.mp hm -- tune
   have hT: W a a=0:=by
      have hw:= (league.mp (hl p)).2; unfold Matrix.trace at hw; change (∑ i:F₀,W i i)=0 at hw; simp_rw [ht] at hw; simpa [F₀,Gauge.repDim,group] using hw -- danger simp_rw loop on W a a
   apply L; ext i j; by_cases h:i=j; rw [h,ht,hT]; rfl
   exact q _ p _ _ h
 obtain ⟨y,u,v,w,hV,hx⟩:=hx
 let z:=y v w; have H₁ :∀ k:ℂ,curlA v w k∈K:=by
   have hp:curlA v w z∈K:=(curl_p v w hV (league.mp (hl u)).1).symm ▸ H _ (hutL v) _ (H _ (hutL w) _ u) -- tune direction
   have hj:curlA v w (Complex.I*z)∈ K := (curl_x _ _ _ hV) ▸ H _ (hutL v) _ hp
   intro k; let r:=k/z
   have ht:r.re • z + r.im • (Complex.I*z)=k:=by simp only [Complex.real_smul]; rw [←mul_assoc, ←add_mul,Complex.re_add_im]; exact div_mul_cancel₀ k hx
   rw [← ht,curl_u, curl_s,curl_s]; exact K.add_mem (K.smul_mem _ hp) (K.smul_mem _ hj)
 have H₂:∀ i:F₀,i≠w→∀ t:ℂ,curlA i w t∈K:=by
   intro i h t; by_cases p:i=v; exact p ▸ H₁ t
   rw [←one_mul t, ←puppet i v w 1 t p hV h]; exact H _ (curl_v _ _ _ p) _ (H₁ t)
 have Hq(j h:F₀)(p:j≠h)(z:ℂ):curlA j h z∈K:=by
   by_cases hx:h=w; rw [hx]; exact H₂ _ (hx ▸ p) z; by_cases hz:j=w
   · rw [curl_n h j z p.symm,hz]; exact H₂ h hx _
   rw [← mul_one z,← puppet _ _ _ z 1 hz (Ne.symm hx) p]; exact H _ (curl_v _ _ _ hz) _ (by rw [curl_n h w _ hx]; apply H₂ h hx)
 have H'(j:F₀):hut j-hut a∈K:=by
   by_cases p:j=a; rw [p, sub_self]; apply K.zero_mem
   have hx : (2:ℝ) • (hut j-hut a)∈K:= (quartD j a p) ▸ H _ (curl_v j a _ p) _ (Hq j a p _); simpa using K.smul_mem (2:ℝ)⁻¹ hx -- tune
 refine hl.antisymm ?_; intro y t
 obtain ⟨hp,hT⟩:=league.mp t
 let F (i j:F₀):= if i=j then 0 else curlA i j (y i j); let P:= (2:ℝ)⁻¹ • ∑ i: F₀,∑ j:F₀, F i j
 have hg:P∈K:=K.smul_mem _ (K.sum_mem (fun i h=> K.sum_mem fun j _=>by unfold F; split; exact K.zero_mem; next h=>exact Hq i j h _))
 have hZ (i j:F₀):star (y j i)= -y i j:=Matrix.ext_iff.mpr hp i j
 have he:P=y-Matrix.diagonal y.diag:=by
   ext l h; unfold P; simp only [Matrix.smul_apply,Matrix.sum_apply,Matrix.sub_apply,Matrix.diagonal_apply, Matrix.diag_apply]; by_cases p:l=h
   · have he(i j:F₀):F i j h h=0:=by by_cases u:i=j <;> by_cases p:i=h<;> by_cases k:j=h <;> simp_all [F,curlA,Matrix.single_apply,Ne.symm] -- dangers context
     rw [p]; simp only [he,sum_const_zero,ite_true,sub_self,smul_zero]
   rw [if_neg p]; have hv (i j:F₀): F i j l h=(if i=l then if j=h then y l h else 0 else 0)+(if j=l then if i=h then y l h else 0 else 0):=by
     unfold F; split_ifs <;> first|rfl|simp_all [curlA, Matrix.single_apply, Ne.symm] -- tune
   simp_rw [hv,sum_add_distrib]; rw [sum_comm (f:=fun i j=> if j=l then if i=h then _ else 0 else 0)]; simp [sum_ite]; ring
 rw [he] at hg
 refine sub_add_cancel y (diagonal y.diag) ▸ K.add_mem hg ?_
 have hx : diagonal y.diag= ∑ i:F₀,(y i i).im • (hut i - hut a):=by
    ext l h; by_cases q:l=h; swap; simp only [q,hut,Matrix.sum_apply,Matrix.smul_apply,Matrix.sub_apply,Matrix.diagonal_apply,ite_false,sub_self,smul_zero,sum_const_zero]
    subst h
    simp only [Matrix.sum_apply,Matrix.smul_apply,Matrix.sub_apply,hut,Matrix.diagonal_apply_eq,Matrix.diag_apply,Complex.real_smul]; have hz := congr_arg Complex.im hT; simp only [Matrix.trace,Matrix.diag_apply,Complex.im_sum,Complex.zero_im] at hz
    have hX i:= congr_arg Complex.re (hZ i i); have hy:∀ i:F₀,y i i=(y i i).im*Complex.I:=by
       intro i; apply Complex.ext; change _=(Complex.re _); simp; have hh:=hX i; simp at hh; linarith; simp
    have hh(i): (if l=i then (4:ℂ)*Complex.I/5 else (-Complex.I)/5)-(if l=a then 4*Complex.I/5 else (-Complex.I)/5)= (if l=i then Complex.I else 0)-(if l=a then Complex.I else 0):=by split_ifs <;>ring
    simp_rw [hh,mul_sub,mul_ite, mul_zero]; rw [sum_sub_distrib]; split_ifs with h
    · simp only [sum_ite_eq,mem_univ,ite_true, ←Finset.sum_mul, ← Complex.ofReal_sum,hz,map_zero,Complex.ofReal_zero,zero_mul,sub_zero]; exact hy _
    simp only [sum_ite_eq,mem_univ,ite_true,sum_const_zero,sub_zero]; exact hy _
 rw [hx]; exact K.sum_mem fun i _=> K.smul_mem _ (H' _)
end YM.CF.Thera
