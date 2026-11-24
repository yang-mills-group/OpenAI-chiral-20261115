import YM.CF.BPress.Bias.Prism
/- B-bias: magnitude jump upper from Mark projections cross-fired aperture. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Bias
open Function Finset Filter NormedSpace Metric Lattice Fock Cube Fir Lat Spin Paint Rush Blank Nacre SU Tulip Spin.Cellar Spin.Cellar.Pass Spin.Hole Spin.Trans Spin.Pledge Spin.Stride Dial Eye Pf Branch Tenant
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {N: Side} {j:ℕ} {M:Jill.Male} {F C:Op (Single N)} {u:Paint (More N)} {t:Finset (Per N)} (P:Pledge) {K a r:ℝ}
abbrev distH (i j: Single N):ℕ:= separation (node (penX i)) (node (penX j))
def Appear (A: Op (Single N)) (P: Pledge):Prop:=∃ (G: Form N Unit), G.Comes P (fun _=>A)
lemma rows_ev{D:Type}[TopologicalSpace D]{G:Form N D}{V: Raw D (Single N)}(h:RootedK (Pledge.solo G.stage) (Pledge.solo G.stage) a K V) (s:0≤a)(x:D)(i):∑ j:Single N, ‖V x i j‖≤ K:=by
 obtain ⟨F,C,p,T,u⟩:= h; rw [u]; apply le_trans ?_ (T.rows i); refine sum_le_sum fun j _=>?_ ; rw [Matrix.sum_apply]; exact (norm_sum_le ..).trans (sum_le_sum (fun W _=> ((p W).expo i j|>.bounded x).trans (le_mul_of_one_le_left ((p W).nonn i j) (rent_one s W))))
lemma looming(f:Per N→ℝ)(X:Op (Single N))(i j): ‖(X* LoomOp f-LoomOp f*X) i j‖= ‖X i j‖*|f (fog j)-f (fog i)|:=by rw [Matrix.sub_apply,LoomOp,Matrix.diagonal_mul,Matrix.mul_diagonal,mul_comm ((f (fog i):ℝ):ℂ), ←mul_sub,← Complex.ofReal_sub,norm_mul,Complex.norm_real]; rfl
lemma fences (P:Pledge)(h:0<a): ∃(n:ℕ)(q:ℝ),0<q ∧ ∀ (N:Side) (f:Per N→ℝ), (∀ x y, |f x-f y|≤1)→∀ A:Op (Single N), IsSelfAdjoint A → Appear A P → (∀ i j:Single N,distH i j≤n → ‖A i j‖*|f (fog i)-f (fog j)|≤ q)→‖A*LoomOp f-LoomOp f*A‖≤a :=by
 obtain ⟨v,hv⟩:= (Eye.tailBuys P (half_pos h)).exists; let c:ℝ:=quota*((v:ℝ)+1)^4; have hc:0<c:=by have hx:0<quota:= lt_of_lt_of_le (by norm_num) quota_bound; unfold c; positivity
 let q:=a/2/c; have hq:0<q:=by unfold q; positivity
 refine ⟨v,q,hq, fun N f B A e R K=>?_⟩; obtain ⟨G,S⟩:=R; let E:= A*LoomOp f - LoomOp f*A; have hz(i j: Single N):‖E i j‖=‖E j i‖:=by
   unfold E; rw [looming,looming,←abs_sub_comm (f (fog j)),show ‖A i j‖=‖A j i‖ from ?_]; nth_rw 1 [←e.star_eq]; simp
 suffices Q:∀ i:Single N,∑ j:Single N,‖E i j‖≤a by exact schur _ E a h.le (fun i j=> le_of_eq (rfl:‖E i j‖=‖E i j‖)) Q (fun j=> (sum_le_sum fun i _=> (hz i j).le).trans (Q j))
 obtain ⟨F,C,R,H,T⟩:=S; let b:=G.stage; intro i; let J:=board b (bay b.F (b.home i) v); have hp:(J.card:ℝ)≤c:= G.full.place ..; have he(k:Single N) : k∈ J ↔ distH i k≤v:=by unfold J; simp only [board,mem_filter,mem_univ,true_and,bay,b,mem_filter]; exact Iff.rfl -- tune
 rw [← sum_add_sum_compl J]; let W:=lop F v (); have hy : (∑ j∈Jᶜ,‖E i j‖) ≤ ∑ j, ‖(A-W) i j‖:=by
    apply le_trans ?_ (sum_le_sum_of_subset_of_nonneg (f:=fun j=>‖(A-W) i j‖) (s:= Jᶜ) (subset_univ _) (fun i _ _=> norm_nonneg _)); apply sum_le_sum; intro j p; have hW:W i j=0:= lop_rad F C R () i j (lt_of_not_ge (fun t:(distH i j≤v)=>mem_compl.mp p ((he j).mpr t))); rw [Matrix.sub_apply,hW,sub_zero]; rw [show ‖E i j‖=_ from looming f A i j]; exact mul_le_of_le_one_right (norm_nonneg _) (B _ _)
 have ht: (∑ j∈J,‖E i j‖)≤ a/2:=by
    apply (sum_le_sum (g:=fun _=>q) ?_).trans; swap; · intro j u; unfold E; rw [looming,abs_sub_comm]; exact K i j ((he j).mp u)
    rw [sum_const,nsmul_eq_mul]; exact (mul_le_mul_of_nonneg_right hp hq.le).trans_eq (mul_div_cancel₀ _ hc.ne')
 apply (add_le_add ht (hy.trans ((rows_ev (G:=G) (V:=fun x=>A-lop F v x) (lip_tail F C R H T P.pos.le) (half_pos P.pos).le () i).trans hv))).trans_eq (add_halves _) -- tune

-- input geometry on time plus mismatch against clothing H at nodes near patch.
structure ColorR (u: Paint (More N))(B U:Op Slot)(f:Per N→ℝ) (q:ℝ)(n:ℕ)(t J:Finset (Per N)):Prop where
 carousel(x y:Per N): |f x-f y|≤1
 cross(i j:Single N)(s:distH i j ≤ n)(t':fog i ∉ t)(p:fog j ∉ t)(v:q< |f (fog i)-f (fog j)|) :
   fog i ∈ J ∧ fog j ∈ J ∧ let x:=u (node (penX i)); let y:=u (node (penX j)); ((x=U ∧ y=B)∨(x=B ∧ y=U))
abbrev screen (j:ℕ)(M:Jill.Male)(t:Finset (Per N)):=ramp (loose (Lower t)) (pos (Lower t)) (nativeX j M N)
theorem fencing (j d:ℕ) (h: 1≤j) (P:Pledge) (U B:Op Slot) (t:U≠ B): ∃ (n m:ℕ)(q c:ℝ), 0<q∧0<c∧∀ (M:Jill.Male)(N:Side), n≤ N.val →∀ (f:Per N→ℝ) (u:Paint (More N))(t J: Finset (Per N))(w:Per N)(i:ℕ), i≤ d → w∉t → w+(i:Per N)∉t → f w=0→f (w+(i: Per N))=1→
 ColorR u B U f q m t J → ∀ a r:ℝ, Pass (pos (Lower t)) (Hole.neg (Lower t)) (loose (Lower t)) (nativeX j M N) a→ let F:=screen j M t ; Bore F (coupling u) r → Appear F P→ ∃ x: Site N,x 0∉t∧x 0∈J ∧ c ≤ ash x (Pf.lost F (coupling u)):=by
 obtain ⟨η,v,l,G⟩:= sparkP j d h; obtain ⟨m,q,r,K⟩:=fences P l; obtain ⟨c,s,V⟩:=C_entry t; let c₀:= (q/(2*c))^2; have hc:0<c₀:=pow_pos (by positivity) _; refine ⟨v,m,q,c₀,r,hc,?_⟩; intro M N h' f u T J w i g₁ g₂ g₃ h1 h2 H a r Q F S R; by_contra! ν
 let A(x:Site N):=Real.sqrt (ash x (Pf.lost F (coupling u))); have f₀:= G M N h' f T w i g₁ g₂ g₃ h1 h2 Q; have e:= Q.ramp_star; suffices g:‖F*LoomOp f-LoomOp f*F‖ ≤η by exact (not_lt.mpr g) f₀
 refine K N f H.carousel F e.isSelfAdjoint R (fun i j g=>?_); by_cases l:q< |f (fog i)- f (fog j)|; swap
 · exact (mul_le_of_le_one_left (abs_nonneg _) ((norm_entry ..).trans (IsStarProjection.norm_le F e))).trans (le_of_not_gt l)
 have hs(i j:Single N): ‖F i j‖= ‖F j i‖:=by nth_rw 1 [←show star F=F from e.isSelfAdjoint]; simp
 have hW(i j:Single N)(p:fog i∈ T):‖F i j‖=0:=by nth_rw 1 [←(show loose (Lower T)* F=F from Q.ramp_L)]; rw [shutter_empty, shutter, slabL]; simp [shutters,p]
 apply (mul_le_of_le_one_right (norm_nonneg _) (H.carousel ..)).trans; by_cases v₁:fog i∈ T; rw [hW i j v₁]; exact ‹0<q›.le; by_cases v₂:fog j∈ T; rw [hs,hW j i v₂]; exact ‹0<q›.le
 have gz(x: Per N) := H.carousel x x
 obtain ⟨ht,hu,L⟩:= H.cross i j g v₁ v₂ l; let x:=penX i; let y:=penX j; have G(z:Site N)(h:z 0∉T)(p:z 0∈J): A z ≤ q/(2*c):=Real.sqrt_le_iff.mpr ⟨by positivity,(ν z h p).le⟩
 have hk:c*(A x+A y) ≤ q:= (mul_le_mul_of_nonneg_left (add_le_add (G x v₁ ht) (G y v₂ hu)) s.le).trans_eq (by field_simp; ring); rcases L with L|L; · exact (V N r F u S (toll_r T M a h Q) i j L.1 L.2).trans hk
 rw [hs]; exact (V N r F u S (toll_r T M a h Q) j i L.2 L.1).trans (by rwa [add_comm (A x) (A y)] at hk)
end YM.CF.BPress.Bias
