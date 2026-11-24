import YM.CF.BProof.Bias.Sloop
/-! Uniform root-neighborhood. Buy A physical (Π,P+ costs reconnection).
Sphere growth as in Stint/Mask; appeal to the sharp-box globalization. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Bias
open Function Filter Fock Finset Branch Tenant Cube SU Tulip Lat Lattice Dial Spin Fig Align Stint Wick Hearth
open Fir Laurent Rush Bloch Next.Free BZ Real
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {D:Type}[TopologicalSpace D]{N:Side}{v b:ℝ}{r:ℕ}
abbrev Level (U:Finset (Per N)):= spot (rowsX U)
lemma seat_day (U:Finset (Per N))(b:Feet N D): Seat U=strip b.st (Level U):= by
 unfold Seat timeR Branch.strip; apply congrArg; ext i; rw [board,b.index]; simp [Level,badgeOf,row_at]
lemma places : ∃ p: Stint.Pay,∀ {N:Side}{D:Type}[TopologicalSpace D](b:Feet N D)(U:Finset (Per N))(a:Tag b.st), Earn p a a (fun _=>Seat U):=by
 let q:= quota*((↑(0:ℕ):ℝ)+1)^4 * Real.exp (1*(quota*((↑(0:ℕ):ℝ)+1)^4))*1; have hp:=Spin.quota_p; refine ⟨⟨1,q,one_pos,(by unfold q; positivity)⟩,?_⟩; intro N D _ b U a; refine row_earn (F:=fun _=>Seat U) (m:=0) b.cap hp.le zero_le_one (fun g x=>?_) continuous_const zero_le_one (fun i x y t=>?_) (fun i j _=> (norm_entry ..).trans ((timeR_proj ..).norm_le _)) (fun i j x y=>?_)
 · rw [seat_day U b]; exact strip_tag ..
 · have ht:x≠y:=fun e=> by rw [e,b.st.F.reflex] at t; omega
   exact Matrix.diagonal_apply_ne _ ht
 simp [b.st.pos]
variable {I:Type}[Fintype I][DecidableEq I][Nonempty I] (x:Ket I)
lemma index_cap(i:I): ‖x.ofLp i‖≤‖x‖:=by rw [←basis_inner]; exact le_trans (norm_inner_le_norm ..) (by simp [basisKet])
lemma pill_day(A:Op I)(J:Finset I)(p:0≤v)(u:∀ i∈J, ‖acts A (basisKet i)‖≤v): ‖A*cutM J‖≤ J.card*v:=by
 apply norm_bound_act (by positivity); intro x; nth_rw 1 [←basis_expand x]; rw [map_sum]; apply le_trans (b:=∑ _∈J,‖x‖*v) ((norm_sum_le ..).trans ?_);
 · rw [sum_const,nsmul_eq_mul,mul_comm ‖x‖ v,←mul_assoc]
 rw [show ∑ _∈J,‖x‖*v=∑ i:I, if i∈J then ‖x‖*v else 0 from (by rw [←sum_filter,filter_mem_eq_inter, univ_inter])]; apply sum_le_sum; intro i _; rw [map_smul,norm_smul, act_mul,cut_basis]; split; next t=> exact mul_le_mul (index_cap x i) (u i t) (norm_nonneg _) (norm_nonneg _)
 simp
-- helper second bound
variable {c K:ℝ}
lemma crisp (b:Feet N D)(Z:Op (Single N))(U Y:Finset (Per N))(X:Finset (Single N))(p:0≤v)(s:U⊆ Y)(g:∀ i:Single N,ht i∈Y→ ‖acts (star Z) (basisKet i)‖≤v): ‖star Z*Seat U *cutM X‖≤ X.card*v:=by
 apply pill_day _ _ p; intro i _; rw [act_mul,Seat,timeR,cut_basis]; split; rename_i t; exact g i (s (mem_filter.mp t).2); simpa
lemma crisp_cost (p:Stint.Pay)(h:0<c): ∃ g:ℝ, 0<g ∧ ∀ {D:Type}[TopologicalSpace D]{N:Side}(b: Feet N D){Z:Raw D (Single N)}{a k:Tag b.st}, Earn p a k Z →∀ (U Y:Finset (Per N))(x:D), U⊆ Y→ (∀ i:Single N, ht i∈Y→‖acts (star (Z x)) (basisKet i)‖ ≤g)→ ‖Seat U * Z x‖≤c:=by
 obtain ⟨r,hR⟩:= places; obtain ⟨K,H⟩:= purchases (half_pos h).le (half_lt_self h) (p.mul r); let q:= quota*((K:ℝ)+1)^4; have hx:0<q:=by unfold q; apply mul_pos Spin.quota_p; positivity
 let d:=c/2/q; have he:0<d:=by unfold d; positivity
 refine ⟨d,he,?_⟩; intro D _ N b Z v k t U Y x u F; rw [←norm_star (Seat U *Z x),star_mul,(timeR_proj ..).isSelfAdjoint]; apply H (t.adj.times (hR b U v)) b.town; intro T; let V:= bay b.st.F T K; let X:= board b.st V; rw [←b.town]; exact le_trans (crisp b _ _ _ X he.le u F) ((mul_le_mul_of_nonneg_right (b.cap.place T K) he.le).trans_eq (mul_div_cancel₀ _ hx.ne'))
abbrev Extend (U Y:Finset (Per N))(r:ℕ):= ∀ x∈U, cent x r ⊆ Y
lemma Extend.sub {U Y:Finset (Per N)}(h:Extend U Y r) : U ⊆ Y := fun x p=> h _ p (cent_base ..)
lemma Extend.meh {U Y:Finset (Per N)}(h:Extend U Y r){Z:Op (Single N)}(u: Span ht r Z): Seat Y*(Z*Seat U)=Z*Seat U:=by
 ext i j; rw [timeL]; split; rfl; rename_i t; rw [timeS]; split; next e=> exact (u i j (Nat.lt_of_not_ge fun v=>t ((h _ e) ((cent_at ..).2 v)))).symm
 rfl
lemma Extend.limit{U Y:Finset (Per N)}(h:Extend U Y r){Z:Op (Single N)}(u:Near ht r v Z)(t: ‖Seat Y * Z‖≤K): ‖Z*Seat U‖≤K+2*v:=by
 obtain ⟨Q,f,g⟩:=u; let X:= Seat U; let P:=Seat Y; have he:‖Q*X‖≤K+v:=by rw [← h.meh f,←mul_assoc]; apply le_trans (timeUB ..); nth_rw 1 [← sub_sub_cancel Z Q]; rw [mul_sub]; exact (norm_sub_le ..).trans (add_le_add t ((timeLB ..).trans g))
 apply (norm_le_norm_sub_add _ (Q*X)).trans; change ‖Z*X-Q*X‖+_ ≤_; rw [← sub_mul]; apply (add_le_add ((timeUB ..).trans g) he).trans_eq; ring
lemma regionP (p:Stint.Pay)(h:0<v): ∃ g:ℝ, ∃ r:ℕ, 0<g ∧ ∀ {D:Type}[TopologicalSpace D]{N:Side}(b: Feet N D){Z:Raw D (Single N)}{a k:Tag b.st}, Earn p a k Z →∀ (U Y:Finset (Per N))(x:D), Extend U Y r→(∀ i:Single N, ht i∈Y→‖acts (star (Z x)) (basisKet i)‖ ≤g)→ ‖Seat U*Z x‖≤v∧ ‖Z x*Seat U‖≤ v:=by
 obtain ⟨g,k,H⟩:=crisp_cost p (half_pos h); obtain ⟨r,t⟩:=((tailPaid p).eventually (gt_mem_nhds (show 0<v/4 by positivity))).exists; refine ⟨g,r,k,?_⟩; intro D _ N b Z a f u U Y x V F; refine ⟨(H b u U Y x V.sub F).trans (half_le_self h.le),(V.limit (temporal_near b x u r) (H b u Y Y x subset_rfl F)).trans ?_⟩; linarith -- tune
end YM.CF.BProof.Bias
