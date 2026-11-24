import YM.CF.Mesa.Atlas

/-! Strip one coordinate in real extension proof. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Mesa
open Function Matrix
open scoped Topology Matrix.Norms.Frobenius NNReal BigOperators InnerProductSpace
abbrev Keys (n:ℕ):=Op (Fin n)
variable {n:ℕ}
def layer (A:Keys n):Keys (n+1):= Matrix.of (Fin.cons (Pi.single 0 1) (fun i=> Fin.cons 0 (A i)))
def aside (A:Keys (n+1)):Keys n:= A.submatrix Fin.succ Fin.succ
@[simp] lemma layer₁ (A:Keys n)(j:Fin _):layer A 0 j=(Pi.single 0 (1:ℂ): Fin (n+1)→ℂ) j:=rfl
@[simp] lemma layer₂ (A:Keys n)(i):layer A (Fin.succ i) 0=0:=by simp [layer]
@[simp] lemma layer₃ (A:Keys n)(i j):layer A (Fin.succ i) (Fin.succ j) = A i j:=by simp [layer]
lemma layer_mul (A B:Keys n): layer A * layer B=layer (A*B) := by
  ext i j; refine Fin.cases ?_ (fun i=>?_) i <;> refine Fin.cases ?_ (fun j=>?_) j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
lemma layer_star (A:Keys n): star (layer A)=layer (star A):=by
  ext i j; refine Fin.cases ?_ (fun i=>?_) i <;> refine Fin.cases ?_ (fun j=>?_) j <;> simp
lemma layer_one : layer (1:Keys n)=1:= by
  ext i j; refine Fin.cases ?_ (fun i=>?_) i <;> refine Fin.cases ?_ (fun j=>?_) j <;> simp [Matrix.one_apply] <;> exact Ne.symm (Fin.succ_ne_zero _)
lemma layer_det (A:Keys n):(layer A).det=A.det:=by
  rw [Matrix.det_succ_row_zero,Fin.sum_univ_succ]
  simp
  congr 1
lemma suit_layer (A:Keys n): trueS (layer A) ↔ trueS A := by
  have he : Injective (layer (n:=n)):= fun a b h=> Matrix.ext fun i j=> by
    simpa using congr_fun (congr_fun h i.succ) j.succ
  change _ ∧ _ ↔ _ ∧ _
  rw [Matrix.mem_unitaryGroup_iff,Matrix.mem_unitaryGroup_iff,layer_det,layer_star,layer_mul,← layer_one,he.eq_iff]
lemma taut {A:Keys (n+1)}(h: shaft 0 A=shaft 0 1)(y:Fin (n+1)) : A y 0=(Pi.single 0 (1:ℂ):Fin (n+1)→ℂ) y:=by
  have hx:= congr_arg (fun v:Ket (Fin (n+1))=>v.ofLp y) h
  by_cases t:y=0 <;> simpa [shaft,t] using hx
lemma shaft_back (A B:Keys n)(x:Fin n) : shaft x (A*B)=jet A (shaft x B) := by simp only [shaft,jet,WithLp.ofLp_toLp,Matrix.mulVec_mulVec]
lemma layer_flat {A:Keys (n+1)}(H:trueS A)(h:shaft 0 A=shaft 0 1):A=layer (aside A):=by
  have he : shaft 0 (star A)=shaft 0 1 := by
    rw [show shaft 0 (star A)=shaft 0 (star A * 1) by simp only [mul_one],shaft_back,← h,← shaft_back,show star A*A=1 from H.1.1]
    exact h.symm -- check
  ext i j; refine Fin.cases ?_ (fun i=>?_) i <;> refine Fin.cases ?_ (fun j=>?_) j
  · rw [taut h]; rfl
  · have ht:=taut he j.succ; simpa using ht
  · simp [taut h]
  simp [aside]
lemma layer_shift (A:Keys n) : shaft 0 (layer A)=shaft 0 1:=by ext i; refine Fin.cases ?_ (fun i=>?_) i <;> simp [shaft]
lemma layer_cont (A:Keys n):ContDiffAt ℝ 1 layer A:= by
  apply mat_smooth; intro i j; refine Fin.cases ?_ (fun i=>?_) i <;> refine Fin.cases ?_ (fun j=>?_) j
  all_goals simp only [layer₁,layer₂,layer₃]
  all_goals first | exact contDiffAt_const | exact (mat_entry _ _).contDiffAt
lemma aside_cont (A:Keys (n+1)): ContDiffAt ℝ 1 aside A:= mat_smooth aside A fun i j=>(mat_entry _ _).contDiffAt
lemma shaft_smooth (i:Fin n)(A:Keys n) : ContDiffAt ℝ 1 (shaft i) A:=by
  let T : Keys n→ₗ[ℝ] Ket (Fin n):=⟨⟨shaft i,?add⟩,?s⟩
  case' add=> intro X Y; unfold shaft; rw [Matrix.add_mulVec]; rfl
  case' s => intro c X; change shaft i (c • X)=c • shaft i X; unfold shaft; rw [Matrix.smul_mulVec]; rfl
  exact T.toContinuousLinearMap.contDiff.contDiffAt
lemma shaft_norm (A:Keys n)(h:trueS A)(i :Fin n) : ‖shaft i A‖=1:=by
  rw [show ‖shaft i A‖=‖jet A (basisKet i)‖ from rfl, jet_norm _ h.1]; simp
end YM.CF.Mesa
