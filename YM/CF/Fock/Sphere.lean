import YM.CF.Fock.Dom

/-! Reflection anti-linear multiplicative grading. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Finset Function Filter NormedSpace
attribute [local instance] opCStarAlgebra
variable {n : Type*} [LinearOrder n] [Fintype n]

-- theta(u) = Pin extra i phase, followed by particle hole. Use Θ for *operator* algebra.
def invFilm (U : UNI n) := phaseU Complex.I (by simp)*U
def screenM (U : UNI n) := quantU (invFilm U)*autumn n
def theta (U : UNI n) (A : FC n) := twist (screenM U) (cc A)
lemma theta_one (U : UNI n) : theta U 1=1 := by simp [theta]
lemma theta_zero (U : UNI n) : theta U 0=0 := by simp [theta]
lemma theta_mul (U : UNI n) (A B) : theta U (A*B)=theta U A*theta U B := by simp [theta]
lemma theta_add (U : UNI n) (A B) : theta U (A+B)=theta U A+theta U B := by simp [theta]
lemma theta_sub (U : UNI n) (A B) : theta U (A-B)=theta U A-theta U B := by simp [theta]
lemma theta_smul (U : UNI n) (A) (c : ℂ) : theta U (c • A)=star c • theta U A := by rw [theta,cc_smul,twist_scalar]; rfl
lemma theta_rsmul (U : UNI n) (A) (c : ℝ) : theta U (c • A)=c • theta U A := by rw [theta,cc_rsmul,map_smul]; rfl
lemma theta_star (U : UNI n) A : theta U (star A)=star (theta U A) := by simp only [theta,cc_star,map_star]
@[fun_prop] lemma theta_cont (U : UNI n) : Continuous (theta U) := (breeze (screenM U)).comp cc_cont
lemma theta_sum {I : Type*} (S : Finset I) (U : UNI n) (f : I→FC n) : theta U (∑ x∈S,f x)=∑ x∈S,theta U (f x) := by
  classical
  induction S using Finset.induction_on with
  | empty=> simp [theta]
  | insert i S h ih=> rw [sum_insert h,sum_insert h,theta_add,ih]
lemma put_clear (i : n) : cc (put i) = put i := by
  ext x y; rw [cc_apply, put_entry]; split_ifs <;> first | exact parity_star .. | simp
lemma inv_act (U : UNI n) (v : Ket n) : acts (invFilm U).val v=Complex.I • acts U.val v := by change acts ((phaseU Complex.I _).val*U.val) _=_; rw [act_mul]; change acts (Complex.I • 1) _=_; rw [act_smul,act_one]
lemma theta_up (U : UNI n) (i : n) : theta U (put i) = (-Complex.I) • remove (acts U.val (basisKet i)) := by
  rw [theta,put_clear,screenM,twin,top_swap,← remove_take,twist_remove,inv_act, remove, map_smul,star_smul]; simp
lemma theta_down (U : UNI n) (i : n) : theta U (takeF i)= Complex.I • create (acts U.val (basisKet i)) := by
  rw [takeF,theta_star,theta_up,star_smul]; simp [remove]
lemma theta_upV (U : UNI n) (x : Ket n) : theta U (create x)= (-Complex.I) • remove (acts U.val x) := by
  rw [create_def, theta_sum]; simp_rw [theta_smul,theta_up]; nth_rw 2 [←basis_expand x]
  simp only [remove,map_sum,map_smul,star_sum, star_smul, smul_sum,smul_comm _ (-Complex.I)]
lemma theta_downV (U : UNI n) (x) : theta U (remove x)= Complex.I • create (acts U.val x) := by rw [remove,theta_star,theta_upV,star_smul]; simp [remove]
-- sea vacuum
lemma leaves (s : Finset n) : twist (autumn n) (cutM {s})=cutM {sᶜ} := by
  obtain ⟨c,h,H⟩ := bend s; apply op_columns; intro j
  let U := autumn n
  rw [twist_formula,act_mul,act_mul,cut_oneAct,map_smul,H,cut_oneAct]
  have he : (acts (star U.val) (basisKet j)).ofLp s=star c*(basisKet j).ofLp sᶜ := by
    rw [←basis_inner,←act_inner,star_star,H,inner_smul_left,basis_inner] -- tune U
    rfl
  rw [show _=star c*(basisKet j).ofLp sᶜ from he, smul_smul,mul_right_comm,scale_unit_self h,one_mul]
lemma sea_vac (s : Finset n) (U : UNI n) (h : twist U (cutM sᶜ)=cutM s) (A : FC n) : theta U A s s=star (A s s) := by
  let V := screenM U
  have he : (star (cutM {s}))=(cutM {s}) := (cutM_idp ..).isSelfAdjoint
  have hc : cc (cutM {s})=cutM {s} := by unfold cc; rw [he]; simp [cutM]
  have hp : theta U (cutM {s})=cutM {s} := by
    rw [theta,hc,screenM,twin,leaves,←cutLine,← line_twist, invFilm,twin,h,rankPhase, cutLine]
  have hk (A : FC n) : (A*cutM {s}).trace=A s s := by
    simp [cutM,Matrix.trace,Matrix.diag, Matrix.mul_diagonal,mul_ite]
  have hx : (theta U A*cutM {s}).trace=(cc (A*cutM {s})).trace := by
    nth_rw 1 [←hp]; rw [←theta_mul,theta,trace_twist]
  rw [cc_mul,hc,hk,hk] at hx; exact hx
lemma chi_ket (U : UNI n) (h : U.val*U.val= -1) (x) : acts U.val (acts U.val x)= -x := by rw [←act_mul,h,act_neg,act_one]
lemma chi_put (U : UNI n) (h : U.val*U.val= -1) (i : n) : theta U (theta U (put i)) = put i := by
  rw [theta_up, theta_smul, theta_downV, chi_ket U h]; simp [smul_smul]
lemma theta_twice {S : Finset n} {P : FC n} {b} (U : UNI n) (h : U.val*U.val= -1) (e : Sector S b P) : theta U (theta U P) = P := by
  induction e with
  | zero => rw [theta_zero,theta_zero]
  | one=> rw [theta_one,theta_one]
  | up i _=> exact chi_put U h i -- tune
  | down i _=> rw [takeF,theta_star,theta_star,chi_put U h i]
  | add _ _ ih it=> rw [theta_add, theta_add,ih,it]
  | mul _ _ ih it=> rw [theta_mul, theta_mul,ih,it]
  | scale _ c ih=> rw [theta_smul,theta_smul,star_star,ih]
lemma theta_carries {S T : Finset n} (U : UNI n) {A : FC n} {a} (g : Sector S a A) (h : twist U (cutM S)=cutM T) : Sector T a (theta U A) := by
  have he i (p:i∈S) : Sector T true (create (acts U.val (basisKet i))) := Sector.makeP _ (by rw [←h,← swivel, cut_basis,if_pos p] -- fails tune
    )
  induction g with
  | zero=> rw [theta_zero]; apply Sector.zero
  | one=> rw [theta_one]; apply Sector.one
  | up i g=> rw [theta_up]; exact (he i g).contr.scale _
  | down i g=> rw [theta_down]; exact (he i g).scale _
  | add _ _ ih it=> rw [theta_add]; exact ih.add it
  | mul _ _ ih it=> rw [theta_mul]; exact ih.mul it
  | scale _ c ih=> rw [theta_smul]; exact ih.scale _
lemma theta_square (s : Finset n) (U : UNI n) (h : twist U (cutM sᶜ)=cutM s) (S : Finset n) (g : twist U (cutM S)=cutM Sᶜ) (P Q : FC n) (b) (e : Sector S b P) (f : Sector S b Q) : let k : ℂ := if b then Complex.I else 1;
    (k • (theta U P*Q)) s s=star (P s s)*Q s s := by
  intro k; rw [Matrix.smul_apply,Sector.sliced (theta_carries U e g) f disjoint_compl_left,sea_vac s U h P]; cases b
  · exact one_smul ..
  rw [e.odd_lost,star_zero,zero_mul,smul_zero]
end YM.CF.Fock
