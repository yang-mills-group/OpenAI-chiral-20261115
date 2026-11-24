import YM.CF.Continuum.Algebra

/-!
# On-site currents in this local algebra

The stencil uses no link or tag arguments (so is not a gauge-dressed open
color line). Bilinear for each generation and each species separately.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Window
open Function Finset Lattice SU Fock Lat Cube Mir Mir.Trip Phase RP Spire Scroll Tulip Reed Reflect
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 4096
section
variable {m B N : Side}

abbrev Family := Fin 3 × Bool

def family (a : Slot) : Family := (a.1, a.2.isLeft)
/-- `true` labels a 10. -/
def colors (x : Family) := univ.filter fun a : Slot => family a = x

def dimf (x : Family) : ℕ := if x.2 then 10 else 5

lemma colors_card (x : Family) : (colors x).card = dimf x := by
  rcases x with ⟨x,x'⟩; cases x' <;> fin_cases x <;> decide

lemma neq_block {a b : Slot} (g : E) (e : family a ≠ family b) : (matter g).val a b = 0 := by
  rcases a with ⟨a,c|c⟩; all_goals rcases b with ⟨b,d|d⟩
  all_goals by_cases p:a=b <;> simp_all [family,triple,each,Join.both]

lemma matter_block (x : Family) (g : E) :
    Commute (matter g).val (cutM (colors x)) := by
  ext a b; rw [cutM, Matrix.mul_diagonal, Matrix.diagonal_mul]; by_cases h : a∈colors x <;> by_cases p : b∈ colors x
  · rw [if_pos h, if_pos p,one_mul,mul_one]
  · rw [if_neg p,if_pos h,mul_zero,one_mul]; exact Eq.symm (neq_block g (by intro e; apply p; rw [colors, mem_filter]; rw [colors, mem_filter] at h; exact ⟨mem_univ _,e ▸ h.2⟩))
  · rw [if_neg h, if_pos p, zero_mul,mul_one]; exact neq_block g (fun e=> h (mem_filter.mpr ⟨mem_univ _,e.trans (mem_filter.mp p).2⟩))
  rw [if_neg h, if_neg p,zero_mul,mul_zero]

/-- `jOp`: plus row and minus column; no claim that other indices are admitted. -/
def jOp (N : Side) (x : Family) (s : Site N) (i j : SpinIdx) : Op (Single N) :=
  love N (jump (Equiv.refl (Site N)) fun t => if t=s then
    (Matrix.single i j 1 : Op SpinIdx) ⊗ₖ cutM (colors x) else 0)

def current (N : Side) (x : Family) (s : Site N) (i j : SpinIdx) : Evaluation N :=
  fun _ => dg (jOp N x s i j)

lemma jOp_gauge (x : Family) (s : Site N) (i j : SpinIdx) (g : Site (More N) → E) :
    twist (tradew N g) (jOp N x s i j) = jOp N x s i j := by
  apply Mir.twist_comm; rw [tradew_eq_love, jOp, ←map_mul, ←map_mul]
  unfold conjG Lat.color; simp only [jump_mul, Equiv.refl_apply]
  apply congrArg (love N); congr 1; funext t; split_ifs; · rw [op_kron_mul,op_kron_mul,mul_one,one_mul,(matter_block ..).eq]
  rw [mul_zero,zero_mul]

lemma jOp_entry (x : Family) (s : Site N) (i j : SpinIdx) (u v : Site N × SpinIdx) (c d : Slot) :
    jOp N x s i j (u,c) (v,d) = if u=(s,i) ∧ v=(s,j) ∧ c∈colors x ∧ c=d then 1 else 0 := by
  obtain ⟨y,a⟩:=u; obtain ⟨z,b⟩:=v; by_cases p:y=z; swap
  · by_cases h:y=s; subst s; simp [jOp,loveAt,unityP,Matrix.submatrix_apply,helix,jump_apply,p,Ne.symm p]
    simp [jOp,loveAt,unityP,Matrix.submatrix_apply,helix,jump_apply,p,h]
  subst z; unfold jOp; by_cases hy:y=s
  · subst y
    by_cases ha:a=i <;> by_cases hb:b=j <;> by_cases h:c=d <;> simp [ha,hb,h, loveAt, unityP, Matrix.submatrix_apply, helix,jump_apply,cutM, Matrix.single, Eq.comm (a:=i), Eq.comm (a:=j)]

  simp [loveAt,unityP,Matrix.submatrix_apply, helix,jump_apply,hy]

lemma current_words (x : Family) (s : Site N) (i j : SpinIdx) (V) :
    current N x s i j V = ∑ c∈colors x, put ((s,i),c) * takeF ((s,j),c) := by
  unfold colors
  rw [sum_filter]
  unfold current dg dyad; simp_rw [Single,Fintype.sum_prod_type, jOp_entry]
  simp [ite_and,colors]

lemma mem_Tset (s : Site N) (i : SpinIdx) (c : Slot) : ((s,i),c) ∈ Tset N ↔ i∈ plusHalf := by
  simp [Tset, helix, upperP]

lemma current_local (x : Family) (s : Site N) (i j : SpinIdx) (p : i∈ plusHalf) (q : j∉ plusHalf) :
    current N x s i j ∈ localObs N ∅ {s} := by
  refine ⟨continuous_const, fun _ _ _=>rfl,fun V=>?_, fun g V=>?_ ⟩
  · rw [current_words]; apply Fine.sumF; intro c _
    have h := Fine.seed (s:=Tset N) ((s,i),c) ((mem_matterSet {s} _).2 (mem_singleton_self s))
    rw [show (think (Tset N)).term _ = _ from if_pos ((mem_Tset s i c).2 p)] at h
    have t := Fine.seed (s:=Tset N) ((s,j),c) ((mem_matterSet {s} _).2 (mem_singleton_self s)); rw [show (think (Tset N)).term _= _ from if_neg (fun u=> q ((mem_Tset s j c).1 u))] at t
    exact h.grow (show Fine (Tset N) (matterSet N {s}) true _ from (by simpa using t.scale (-1)))
  unfold current; rw [dg_cov,jOp_gauge]

lemma current_positive {s : Site (CSide m B)} (x : Family) (i j : SpinIdx) (p : i∈plusHalf) (q : j∉plusHalf)
    (u : Axis) (v : s∈posY m B u) : current (CSide m B) x s i j∈ nonnegativeTime m B u :=
  localObs_enlarge (empty_subset _) (singleton_subset_iff.mpr v) (current_local x s i j p q)

lemma trace_jOp (x : Family) (s : Site N) {i j : SpinIdx} (p : i≠j) :
    Matrix.trace (jOp N x s i j) = 0 := by
  unfold Matrix.trace; apply Finset.sum_eq_zero; rintro ⟨a,b⟩ _
  rw [Matrix.diag_apply,jOp_entry]; apply if_neg; intro h; exact p (Prod.mk.inj (h.1.symm.trans h.2.1)|>.2)

private lemma block_pin (x : Family) (s : Site N) (i j i' j' : SpinIdx)
    (M : Equiv.Perm (Site N)) (k : Axis)
    (h : pin k * (star (Matrix.single i j 1 : Op SpinIdx)) = -(Matrix.single i' j' 1) * pin k) :
    let U := love N (jump M fun _=>pin k ⊗ₖ (1:Op Slot));
    U*star (jOp N x s i j) = (-jOp N x (M.symm s) i' j')*U := by
  intro U; unfold U jOp; rw [← map_star, ← map_mul, ← map_neg, ← map_mul]
  apply congrArg _; simp only [jump_star, Equiv.refl_symm,Equiv.refl_apply, ←jump_neg,jump_mul,
    Equiv.trans_refl,Equiv.refl_trans]
  congr 1; funext j; split_ifs with p q q
  · rw [op_star_kron,show star (cutM (colors x))=cutM (colors x) from (cutM_idp _).2,
        neg_mul,op_kron_mul,op_kron_mul, mul_one, one_mul,h,neg_mul,op_kron_neg]
  · exact False.elim (q (M.eq_symm_apply.mpr p))
  · exact False.elim (p (M.eq_symm_apply.mp q))
  simp

lemma reflected_current (x : Family) (s : Site (CSide m B)) (i j i' j' : SpinIdx)
    (p : i≠j) (k : Axis)
    (h : pin k * (star (Matrix.single i j 1 : Op SpinIdx)) = -(Matrix.single i' j' 1) * pin k) :
    flipTime m B k (current (CSide m B) x s i j) =
      current (CSide m B) x (matterPoint m B k s) i' j' := by
  funext V; unfold flipTime current; rw [theta_dg,trace_jOp x s p,star_zero,zero_smul,zero_sub]
  let A:=jOp _ x s i j; let S:=matterPoint m B k; have he:S.symm s=S s:=by
    rw [←S.injective.eq_iff]; rw [S.apply_symm_apply,matterPoint_invol k s]
  let P:= jOp _ x (S s) i' j';
  rw [show twist (fullTurn m B k) (star A) = -P from ?_,dg_neg, neg_neg];
  apply Mir.twist_comm; rw [fullTurn_matrix,seen, map_neg];
  rw [neg_mul, mul_neg]; congr 1; unfold P; rw [← he]; exact block_pin x s i j i' j' S k h

lemma adjoint_current (x : Family) (s : Site N) (i j i' j' : SpinIdx) (p : i≠j)
    (k : Axis) (h : pin k * (star (Matrix.single i j 1 : Op SpinIdx)) = -(Matrix.single i' j' 1) * pin k) :
    dagger N k (current N x s i j)=current N x s i' j' := by
  funext V; unfold dagger current; rw [theta_dg,trace_jOp x s p,star_zero,zero_smul,zero_sub]
  rw [show twist (onsite N k) _ = -jOp _ x _ i' j' from ?_,dg_neg, neg_neg]
  apply Mir.twist_comm; exact block_pin x s i j i' j' (Equiv.refl _) k h

-- In the usual last-axis time convention, including this polarization
set_option linter.unusedSimpArgs false in
private lemma pin23 :
    pin 3 * star (Matrix.single 0 2 1 : Op SpinIdx) = -(Matrix.single 0 2 1) * pin 3 := by
  -- normalize Fin literals before reducing γ
  rw [show (3:Axis)=Fin.succ (Fin.succ (Fin.succ 0)) from rfl]; ext i j; fin_cases i <;> fin_cases j <;>
    simp only [pin,Matrix.mul_apply, Matrix.star_apply, Matrix.neg_apply, Matrix.single,
      SpinIdx, Fin.sum_univ_succ,gammaOp,grading,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_succ,
      show (2:Fin 4)=Fin.succ (1:Fin 3) from rfl,
      show (3:Fin 4)=Fin.succ (2:Fin 3) from rfl,
      show (2:Fin 3)= Fin.succ (1:Fin 2) from rfl,
      show (1:Fin 3)=Fin.succ (0:Fin 2) from rfl,
      show (1:Fin 2)= Fin.succ (0:Fin 1) from rfl,
      show (1:Fin 4)= Fin.succ (0:Fin 3) from rfl] <;> norm_num <;> first | decide | (simp only [show (2:Fin 4) = Fin.succ (1:Fin 3) from rfl, show (2:Fin 3)= Fin.succ (1:Fin 2) from rfl, Matrix.cons_val_succ]; split_ifs <;> try contradiction)
  all_goals first | decide | norm_num

/-- Component used in the positive-time Gram tests. Its weight renormalization
will be applied separately. -/
abbrev charge (N : Side) (x : Family) (s : Site N) := current N x s 0 2
lemma reflect_charge (x : Family) (s : Site (CSide m B)) :
    flipTime m B 3 (charge _ x s) = charge _ x (matterPoint m B 3 s) :=
  reflected_current x s 0 2 0 2 (by decide) 3 pin23
lemma charge_dagger (x : Family) (s : Site N) : dagger N 3 (charge N x s)= charge N x s :=
  adjoint_current x s 0 2 0 2 (by decide) 3 pin23

end
end YM.CF.Window
