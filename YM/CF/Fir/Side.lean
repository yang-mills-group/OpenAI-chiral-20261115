import YM.CF.Fir.Graph
/-! Holomorphic band agrees with Wilson projection at start. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fir
open Function Filter Lattice Laurent Bloch Next.Free Metric Finset Set WilsonFrame
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
lemma firm_bar (j N)(h:Odd N.val){p:Momentum}(hp:p∈realCube zone): (bar j N p)*(bar j N p)=bar j N p ∧ star (bar j N p)=bar j N p:=by
  by_cases he:p=0
  · rw [he,bar_origin,star_sub,star_one,Aadj]; refine ⟨?_,rfl⟩; rw [mul_sub,sub_mul 1 Aop Aop,AOne, one_mul,mul_one]; abel
  exact bar_frames _ _ hp he h
lemma start_bar (j)(p:BZ.Mom): bar j 1 (tmap p)=projector (BZ.atom p).H:=by
  let q:= tmap p
  let k:= BZ.bare p; let W:=BZ.wave p
  let d:= gD q
  have hk : d=(W:ℂ)+k:=by unfold d gD q; rw [r_real,wave_eq]
  have he : W≠0:=(BZ.wave_pos p).ne'
  have hx : (W:ℂ)≠0:=by exact_mod_cast he
  have ht : D 1 q=d :=by simp [D,d,narrow]
  have hu : extras j 1 q=0:=by unfold extras; rw [show (univ:Finset (Site 1))={0} by ext1 i; simp only [Finset.mem_univ,Finset.mem_singleton,true_iff]; exact (show (i : Axis → ZMod 1)=0 from @Subsingleton.elim (Axis → ZMod 1) _ _ _)]; simp -- inspect
  have hm : mass j 1 q = (2:ℂ)*W :=by simp only [mass,bloom,muff_one,hu, prodM,Pi.zero_apply,mul_zero,sum_const_zero]; simp [Cminus,ht,hk,narrow,q,r_real,wave_eq]; ring
  change bar j 1 q=projector (BZ.atom p).H
  have hv : zen (skin j 1 q)=(2*(W:ℂ))⁻¹ • BZ.slash p:=by rw [skin, hu,hm]; simp [bloom,ds,narrow,q,zenS,slashT]
  rw [bar,shell,hv,ht,hk,hm,projector,BZ.atomS,H, BZ.atom_H0]
  change (1/2:ℂ) • 1+_ • grading+_= (1/2:ℝ) • (1+W⁻¹ • (grading*(k • 1+BZ.slash p)))
  rw [← BZ.ofReal_action,← BZ.ofReal_action W⁻¹, ← BZ.ofReal_action k]; push_cast; simp only [Matrix.mul_smul,mul_add,mul_one]; rw [show ((W:ℂ)+k)/(2*W)=(1/2:ℂ)+(1/2:ℂ)*(W:ℂ)⁻¹*(k:ℂ) by field_simp]; module
lemma bar_overlap (j N) {p : Momentum}(hp:p∈realCube zone) (x : Cover)(hx:p+reciprocal x∈realCube zone): bar j N (p+reciprocal x)=bar j N p:=by
  unfold bar; rw [shell_overlap _ _ _ hp x hx, show skin j N (p+reciprocal x)=skin j N p by ext1 a; exact skin_overlap j N a p hp x hx]
variable {ι : Type*}
lemma zenBudget {w:ι→ℝ}(hs:∀ i, 0≤ w i)(f : ι→Momentum→Momentum)(h:∀ a:Axis, Moderate w fun i p=> f i p a): Pay w fun i p=> zen (f i p) := by
  refine ⟨hs,fun a b=>?_⟩; simp only [zen, Matrix.sum_apply]
  apply Moderate.sum _ _ hs; intro i _; simpa only [Matrix.smul_apply,smul_eq_mul,mul_one] using (h i).mul (Moderate.const (Complex.I*(gammaOp i) a b))
lemma barBudget (j:ℕ)(hj:1≤j)(N:ι→Side)(ho:∀ i,Odd (N i).val): Pay (fun _ : ι=>1) fun i p=> bar j (N i) p := by
  have he:= (Pay.const grading).scale ((shellPay j hj N ho).sub (Moderate.const (1/2)))
  have hx := (Pay.const grading).times (zenBudget (fun _=>zero_le_one) _ (skinPay j hj N ho)); simp only [mul_one] at he hx
  exact ((Pay.const ((1/2:ℂ) • (1:Op SpinIdx))).add he).add hx
end YM.CF.Fir
