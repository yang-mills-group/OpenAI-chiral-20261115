import YM.CF.Braid.Trainers
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Braid
open Function Lattice RG Exterior Bloch Laurent Filter Finset Asymptotics Stationary
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators
open Work.F06
variable {α ξ:Type}[Fintype α][DecidableEq α][Fintype ξ] {σ τ A C : ℝ}{M N r t:ℕ}
-- end budget
abbrev fock(t M:ℕ):=Fintype.card (Keys (t+1))*(2*M)
abbrev peak(t M:ℕ):= fock t (fock t M)
def liftCost(t M:ℕ):ℝ:=4*fock t M
lemma twist_phase(v:Axis→ℝ)(p:Corn (Keys t)): twist (axes v) (axes p)=axes (twist v p):=by unfold twist; rw [miss_phase,axes_add]
lemma drift (f:SheetLeg (Keys (t+1)) ξ r)(v:Axis→ℝ) (ha:0≤ A)(hf:Board M A f) {U} (hU:Uniforms _ _ (stick t) U)(h:wall U f)(hc:Cycles (twist (axes v)) r f)(hp:r≠0∨∀ p:Corn (Keys (t+1)),twist v p=0→ f (axes p)=0){s:ℕ}(hn:v=0∨s=0)(hj:JetWall s f): ∃ B: SheetLeg (Keys (t+1)) ξ (r+1),Board (peak t M) (A*liftCost t M) B ∧ JetWall (s-1) B ∧ wall U B ∧ ∀ p:Corn (Keys (t+1)),f (axes p)=cob r (twist (axes v)) B (axes p):=by
 have he: Cycles (projected (stick t)) r (work v f):=by
    cases r; exact trivial
    intro p; rw [money,work,Function.comp_apply,glided]; exact hc _
 have ht:JetWall s (work v f):=by
    rcases hn with hx|rfl
    · subst hx; exact jetP f hj
    exact jet_nil (A:=Real.exp (fock t M)*A) fun i x=> (toss v hf i x).analytic
 obtain ⟨X,H,k,Hx,hx⟩:= wall_pull (stick t) ha (work v f) (toss v hf) he (hp.imp_right (fun H p he => by
    rw [work,Function.comp_apply,glided]; exact H _ ((tips ..).trans he))) ht hU (rake v hU h)
 refine ⟨work v X,toss v H,?_,rake v hU Hx,fun p=>?_⟩
 · rcases hn with he|rfl
   · subst he; exact jetP X k
   exact jet_nil (fun i x=> (toss v H i x).analytic : CostWall 1 (Real.exp (peak t M)*(A*liftCost t M)) _)
 have h':=hx (glide v p); rw [← glided,work,Function.comp_apply,glad,show cob _ _ X=work v (cob r (twist (axes v)) (work v X)) from by simpa only [workout] using money v (work v X), work, Function.comp_apply,glad] at h'; exact h'
-- costs for operations
lemma tri (i:α) : Pond 1 2 (divZ i):=by
 have he:= Pond.modes (1:ℂ) (Pi.single (M:=fun _:α=>ℤ) i 1); have ht:= Pond.modes (α:=α) (1:ℂ) 0
 simp [mode_zero,norm_one,size] at ht; have H := he.rest (ht.mono le_rfl (Nat.zero_le _)); simp only [mode, size,Pi.single_apply] at H; -- tune simplify
 convert H
 · rw [sum_eq_single i]
   · simp
   · intro i _ hi; simp [hi]
   simp
 · norm_num
 ext1 p; simp [divZ,mul_ite]
lemma stride(m:Axis↪α)(i:TypeFace (r+1))(j:TypeFace r): Pond 1 8 (fun p=>symbol r (projected m p) i j):=by
 simp_rw [base_cob]; apply (fundsF univ _ (fun _:Axis=> (2:ℝ)) (fun a _=>?_)).mono _ le_rfl
 · simp; norm_num
 simp_rw [mul_comm (divZ _ _)]; exact ((tri _).scal _).mono (mul_le_of_le_one_left (by norm_num) (norm_left ..)) le_rfl
abbrev topG(r:ℕ):ℝ:= Fintype.card (TypeFace (r+1))*8
lemma cargo(m:Axis↪α){f:SheetLeg α ξ (r+1)}(h:Board M A f)(ha:0≤ A): Board (1+M) (A*topG r) (cob r (projected m) f):=by
 intro i x; unfold cob Matrix.mulVec dotProduct; simp only [Matrix.transpose_apply]
 apply (fundsF univ _ (fun _=>8*A) fun j _=> (stride m j i).mul (h j x) ha).mono _ le_rfl
 unfold topG; rw [sum_const,card_univ,nsmul_eq_mul]; exact (by ring_nf; rfl)
lemma too (v:Axis→ℝ) {f:SheetLeg (Keys (t+1)) ξ (r+1)}(h:Board M A f)(ha:0≤ A) : Board (fock t (1+fock t M)) (A*topG r) (cob r (twist (axes v)) f):=by have hx:=toss v (cargo (stick t) (toss v h) ha); rw [money,workout] at hx; exact hx
end YM.CF.Braid
