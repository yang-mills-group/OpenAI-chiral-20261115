import YM.CF.BProof.Fig.Layout

/-! Temporal unmarked-set gap compression price. Uniform since each gap is fixed
width, independent of consecutive mark periods growing. Antiperiodic seam fully
retained in Δ. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Fig
open Function Filter Fock Finset Branch Tenant Cube SU Tulip Lat Lattice Dial Spin Align Stint
open Fir Laurent Rush Bloch Next.Free BZ
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N:Side}{Y:Support N}{w:ℕ}
def Shut (w:ℕ)(i:Axis)(Y:Support N): Prop:=∀ p∈Y, ∃ k:ℕ,k≤w∧ p+k • step i ∉ Y
lemma Shut.thin {i:Axis} (h: Shut w i Y){Y':Support N}(s:Y'⊆Y): Shut w i Y':=by intro p t; obtain ⟨k,p,v⟩:= h p (s t); exact ⟨k,p, fun z=> v (s z)⟩
def addK (x:Site N): Equiv.Perm (Single N):= ((Equiv.addRight x).prodCongr (Equiv.refl SpinIdx)).prodCongr (Equiv.refl Slot)
lemma addK_add(x y: Site N)(b:Single N): addK x (addK y b)=addK (y+x) b:= by unfold addK; obtain ⟨⟨x,i⟩,j⟩:=b; simp [add_assoc]
variable (x: Ket (Single N))(i:Axis) (p: Single N)
lemma actAxis : (acts (axisShift N i) x).ofLp p= seam (anticut N) p.1.1 i*x.ofLp (addK (step i) p):=by
 rw [act_at,Matrix.mulVec,dotProduct,axis_shift i p]; obtain ⟨⟨z,l⟩,k⟩:= p; unfold Single; rw [Fintype.sum_prod_type,Fintype.sum_prod_type (α₁:=Site N)] -- tune
 simp only [Matrix.one_apply]; simp [ite_mul,mul_ite, sum_ite_irrel,ite_and,addK]; left; rfl
lemma coinQuest : ‖x.ofLp p‖ ≤ ‖(acts (axisShift N i-1) x).ofLp p‖+ ‖x.ofLp (addK (step i) p)‖:=by
 rw [act_sub,act_one,WithLp.ofLp_sub,Pi.sub_apply,actAxis]; rw [←one_mul ‖x.ofLp (addK (step i) p)‖]; rw [← seam_norm (anticut N) p.1.1 i, ← norm_mul]; rw [norm_sub_rev]; exact norm_le_norm_sub_add ..
lemma tollK (u:ℕ) : ‖x.ofLp p‖ ≤ (∑ j∈range u,‖(acts (axisShift N i-1) x).ofLp (addK (j • step i) p)‖) + ‖x.ofLp (addK (u • step i) p)‖:=by
 induction u with
 | zero => simp [addK]
 | succ u ih=> rw [sum_range_succ,add_assoc,add_smul,one_smul,←addK_add]; exact ih.trans (add_le_add_right (coinQuest x i (addK (u • step i) p)) _)
theorem levied (h:Shut w i Y)(t:∀ p:Single N,p.1.1 ∉ Y→x.ofLp p=0) : ‖x‖^2≤ w^2*‖acts (axisShift N i-1) x‖^2:=by
 let d:=acts (axisShift N i-1) x; have he(a:Single N): ‖x.ofLp a‖^2 ≤ w*∑ j∈range w, ‖d.ofLp (addK (j • step i) a)‖^2:=by
   by_cases g: a.1.1∈Y; swap; · rw [t a g,norm_zero,zero_pow (by decide:2 ≠0)]; positivity -- tune
   obtain ⟨k,e,hv⟩:= h a.1.1 g; have ht := tollK x i a k; rw [t (addK (k • step i) a) hv, norm_zero,add_zero] at ht
   let F(j:ℕ):=‖d.ofLp (addK (j • step i) a)‖; apply (pow_le_pow_left₀ (norm_nonneg _) (ht.trans (show (∑ j∈range k, F j)≤∑ j∈range w,F j from sum_le_sum_of_subset_of_nonneg (range_mono e) (fun i _ _=> norm_nonneg _))) _).trans; exact le_trans (sum_sq_le_sum_mul_sum_of_sq_le_mul (range w) (r:=F) (f:=fun _=>1) (g:=fun i=> F i^2) (fun i _=> zero_le_one) (fun i _=> sq_nonneg _) (by simp)) (by simp [F]) -- API
 rw [EuclideanSpace.norm_sq_eq]; apply (sum_le_sum (fun i _=> he i)).trans_eq; rw [←mul_sum,sum_comm,EuclideanSpace.norm_sq_eq]
 simp_rw [Equiv.sum_comp (addK (N:=N) _) (fun p=>‖d.ofLp p‖^2),sum_const,card_range,nsmul_eq_mul]; rw [←mul_assoc, pow_two]
lemma drain (i:Axis)(u:Bool)(S:Support N)(w:ℕ)(h:Shut w i S) : let P:=bandCut S u; let T:=axisShift N i-1; P ≤ ((w:ℝ)^2) • (P*(star T*T)*P) := by
 intro P T; have hp:IsStarProjection P:= cutM_idp _; have ht:P*(star T*T)*P=star (T*P)*(T*P):=by rw [star_mul,hp.isSelfAdjoint]; noncomm_ring
 rw [ht]; apply by_hil hp.isSelfAdjoint (IsSelfAdjoint.of_nonneg (smul_nonneg (sq_nonneg _) (star_mul_self_nonneg _))); intro x; rw [hil_linear,hil_gram, hil_idem _ hp,act_mul]; exact levied (acts P x) i h fun p v=>by rw [show (acts P x).ofLp p=_ from cut_apply ..]; exact if_neg (fun H=> v ((mem_band ..).mp H).1)
end YM.CF.BProof.Fig
