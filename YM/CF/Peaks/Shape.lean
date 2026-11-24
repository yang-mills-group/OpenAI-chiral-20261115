import YM.CF.Peaks.Orange
set_option autoImplicit false
noncomputable section
namespace YM.CF.Peaks
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {N P : Side}(G:Ratio N P)
def breath : St (G.count) → SpinIdx:=Prod.snd
def lobe (u:Bool): Op (Iota G):=plates N (fun _=> sA u G.count) ⊗ₖ 1
def hood :Op (Iota G):=endorse G 1
lemma shoulder: hood G=plates N (fun _=>peb G.count)⊗ₖ 1:=by
  have he := low_pose (N:=N) G.count (fun _=> (1:Op SpinIdx))
  rw [piles1] at he
  rw [hood,← show 1= (1:Op (Single N)) from rfl,show (1:Op (Single N))=(1:Op (Site N ×SpinIdx))⊗ₖ 1 from Matrix.one_kronecker_one.symm,endorsement,← he]; rfl -- tune
lemma lobe_plus: lobe G false = 1-lobe G true:=by
  let P:=G.count; have he: (plates N fun _=>sA false P)=(1 - plates N fun _=> sA true P):=by rw [← piles1,pilesM]; simp_rw [show sA false P=1-sA true P from s_neg true _]
  unfold lobe; rw [he]; ext ⟨x,a⟩ ⟨y,b⟩; by_cases h:a=b <;> by_cases g:x=y <;> simp [h,g,Matrix.one_apply,mul_ite] <;> rfl
lemma lobe_sq (u:Bool): IsStarProjection (lobe G u):=by
  have he: plates N (fun _=>sA u G.count)*plates N (fun _=>sA u G.count)=plates N (fun _=>sA u G.count):=by rw [pilesP]; simp only [slate]
  unfold lobe; exact ⟨(by unfold IsIdempotentElem; rw [op_kron_mul,he,one_mul]),(by rw [isSelfAdjoint_iff,op_star_kron,star_one,pilesS]; simp only [slateS])⟩
lemma hood_proj:IsStarProjection (hood G):=by rw [hood]; exact ⟨(by unfold IsIdempotentElem; rw [rude,mul_one]),(by rw [isSelfAdjoint_iff,← endorse_star, star_one])⟩
lemma hood_left :Lively (fun (_ : Unit) N (x:Chin N)=> (1:Op (Single N))):=Lively.one
lemma hood_tag {ι: Type*}(L:Side)(ho:Odd L.val): Save L false false (fun (_:ι) _ _ G _=> hood G):= hailing L ho (fun _ _ _=> 1) Lively.one
lemma gr_diag (x y:SpinIdx)(h:x≠y): Aop x y=0:=by rw [Adef,Matrix.smul_apply,Matrix.add_apply, Matrix.one_apply_ne h]; fin_cases x <;> fin_cases y <;> first| contradiction| simp [grading]
lemma angle_out (u:Bool)(x y:SpinIdx)(h:x≠y): angle u x y=0:=by cases u <;> simp [angle,h,gr_diag]
lemma lobe_fine (u:Bool)(x:Inta G)(a:Slot): lobe G u (x,a) (x,a)=angle u (x.2.2) (x.2.2) :=by rcases x with ⟨x,r,b⟩; simp [lobe,pilesV,sA,slashA,stack,jump_apply]
lemma lobe_diag (u:Bool):(lobe G u)=Matrix.diagonal (fun i:Iota G=> lobe G u i i):=by
  ext ⟨⟨x,r,b⟩,i⟩ ⟨⟨y,t,c⟩,j⟩
  by_cases h:i=j<;> by_cases g:b=c<;>by_cases e:r=t<;>by_cases f:x=y <;> simp [lobe,pilesV,sA,slashA,stack,jump_apply,h,g,e,f,angle_out, Matrix.diagonal_apply, Matrix.one_apply]
lemma gradeBudget {ι:Type*}(L:Side)(u v:Bool): Save L u u (fun (_:ι) _ _ G _=> lobe G v):=by
  refine recorded (k:=0) (d:=1) (e:=1) (C:= quota*((((0:ℕ):ℝ))+1)^4 * Real.exp (1*(quota*((((0:ℕ):ℝ))+1)^4))*1) (A:=fun (_:ι) _ _ G _=> lobe G v) ?_ one_pos one_pos
  intro i N P G p hg
  have hc:0≤quota:=le_trans (by norm_num:(0:ℝ)≤16) quota_bound
  let S:=parcel G u 1; let f : Raw (legal G 1) (Iota G):= fun _=> lobe G v
  have he:∀ x y:Iota G,x ≠ y→ lobe G v x y=0:=fun x y h=>by conv_lhs=>rw [lobe_diag]; rw [Matrix.diagonal_apply_ne _ h]
  have hh : Inter S S f:=by
    intro t x
    unfold f S; rw [lobe_diag,warrant]; ext ⟨y,a⟩ ⟨z,b⟩
    rw [Matrix.diagonal_mul,Matrix.mul_diagonal]; by_cases h:y=z <;> simp [lobe_fine,jump_apply,h,mul_comm]
  -- Crown.sheet with m=0 (distance)
  refine Crown.sheet (temper_cap G 1) hc zero_le_one hh continuous_const zero_le_one 0 ((badge _).base _) (fun x a b he'=> he _ _ ?_) (fun i j x=> ?_) ?_
  · intro h; rw [h, Branch.Field.reflex] at he'; omega
  · exact (norm_entry (lobe G v) i j).trans (IsStarProjection.norm_le _ (lobe_sq ..))
  intro i j x y; dsimp only [f]; rw [sub_self,norm_zero,one_mul]; exact Stage.pos ..
end YM.CF.Peaks
