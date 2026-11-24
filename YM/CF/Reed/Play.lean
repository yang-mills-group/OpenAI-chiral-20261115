import YM.CF.Lattice.Bare
import YM.CF.Delta.Echo
import YM.CF.Reed.Dance

/-! Physical observable subspaces. Keep one tested gauge and star convention. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Reed
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Kronecker ComplexOrder
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant Phase Mir Mir.Trip MeasureTheory Finset Reflect Pastry RP Ave
attribute [local instance] opCStarAlgebra
variable {N m B : Side} {σ β e H : ℝ}
lemma plus_joint (U : Bkg N) (s : Site N) : (frame matter U s).plus=cutM (upperP N) := by
  let A:= grading
  rw [plane_diag, raising]; unfold WilsonFrame.plus
  have he (v:ℂ) (S : Op SpinIdx): spin N Slot (v • S) = v • spin N Slot S := by
    unfold spin; rw [←jump_smul]; congr 1; funext i; ext p q; simp [mul_assoc]
  have hp : spin N Slot (1+A)=spin N Slot 1+spin N Slot A:= by unfold spin; rw [←jump_add]; congr 1; funext i; ext p q; simp only [Matrix.kroneckerMap_apply,Matrix.add_apply,Pi.add_apply,add_mul]
  rw [he,hp,spin_one]; change _=(1/2:ℂ) • (1+spin N Slot A); rw [show (1/2:ℂ)=↑(1/2:ℝ) by push_cast; rfl,Complex.coe_smul]; rfl
lemma kinetic {x : Skin m B} (h : Guard x e) (b : Room B e) (c : Phase.Part m B):
    (frame matter (links x) c).overlap * lens m B c x=cutM (upperP (CSide m B))* lens m B c x := by rw [←plus_joint (links x) c]; exact (WilsonFrame.overlap_action _ (wiel_ok c b h))
lemma quotient_kin (U : Op (Elf m B)) {x : Briar m B e} (b : Room B e) (v : UNI (Elf m B)) (T : Finset (Elf m B)) (c:Phase.Part m B) (h : lens m B c x.val=twist v (cutM T)) (p : (frame matter (links x.val) c).overlap=U) : let D := chemical (U*v.val) (upperP _) T; D=chemical v.val (upperP _) T := by
  intro D; let V:= lens m B c x.val; let A := cutM (upperP (CSide m B))
  have he : U*V=A*V:= Eq.subst (motive:=fun z=>z*V=A*V) p (kinetic x.property b _)
  have hx : V*v.val=v.val*cutM T := by unfold V; rw [h]; exact twist_product ..
  have ht : U*(v.val*cutM T)=A*v.val*cutM T := by rw [←hx, ←mul_assoc U, he,mul_assoc, hx, mul_assoc]
  let s:=upperP (CSide m B)
  have hk i j (p:i∈s) (q:j∈T): (U*v.val) i j=v.val i j := by
    have he : U*v.val*cutM T= _ := (mul_assoc ..).trans ht
    have hx := Matrix.ext_iff.mpr he i j; rw [cutM, Matrix.mul_diagonal, if_pos q,mul_one,Matrix.mul_diagonal,if_pos q,mul_one] at hx
    unfold A cutM at hx; rw [Matrix.diagonal_mul,if_pos p,one_mul] at hx; exact hx
  change -∑ i∈s, bar (n:=Elf m B) i*tote T _ i= -∑ i∈s, bar i*tote T _ i; congr 1; refine sum_congr rfl fun i p=>?_
  congr 1; exact sum_congr rfl fun j h=> by rw [hk i j p h] -- tune
-- Orientation wrt arbitrary occupied frames.
lemma chiral (c : Phase.Part m B) (b : Room B e) (x : Briar m B e) (v : UNI (Elf m B)) (S : Finset (Elf m B)) (h : lens m B c x.val=twist v (cutM S)) : ∃ z:ℂ, ‖z‖=1 ∧ ∀ (P:FC (Elf m B)), Plain P →
    let A := upperP (CSide m B); let D:=spell (n:=Elf m B) (syms A) v.val A S P; z*D=inner ℂ (linearB (CSide m B)) (acts ((think A).eval P) (sound m B c x.val)) := by
  let A:= sound m B c x.val; let B' := wedge v.val S; have p:= unity c b x.property
  have hp : A=inner ℂ B' A • B' := by nth_rw 1 [← (show acts _ A = A from p.1)]; rw [h]; exact act_twistLine ..
  have hk : ‖inner ℂ B' A‖ =1 := by
    have he:= congrArg norm hp; rw [show ‖A‖=1 from p.2,norm_smul,wedge_norm v S,mul_one] at he; exact he.symm -- tune
  let u:= unitV (CSide m B); refine ⟨star u * inner ℂ B' A,by rw [norm_mul,norm_star,hk,show ‖u‖=1 from unit_phase _,mul_one],?_⟩
  intro P g s H; rw [show H=_ from moment (n:=Elf m B) v.val s S _ g]; change _=inner ℂ (u • basisKet s) (acts _ A); nth_rw 2 [hp]; rw [map_smul,inner_smul_left,inner_smul_right,mul_assoc]; rfl
-- Define physical readers (gauge invariant coefficients included, ability to also test polar nonsinglets on bare matrices).
def Sensitive (p : Readers m B) (g : Bool) := Continuous p ∧ (∀ x,Fine (upperP (CSide m B)) univ g (p x)) ∧ (∀ t:Court m B,∀ x:Skin m B,p (Lattice.gauge t x)=twist (quantU (n:=Elf m B) (balls m B t)) (p x))
structure Region (p : Readers m B) (i : Axis) (v : Bool) : Prop where
  physical : Sensitive p v
  sector U : Fine (upperP (CSide m B)) (colony m B i) v (p U)
  reach x y : NorthOf m B i x y→ p x.1=p y.1
lemma rPos {p : Readers m B} {i b} (h : Region p i b) (C : Reg β e B) (g : C.Works) (y:Site (More m)) (n : ℕ) : 0 ≤ C.schwinger m n (squareR m B y (C.c m) i (fun x=>p x.1) b) := g.mirror m n (fun x=> p x.1) b i y ⟨h.physical.1.comp continuous_fst,fun x=>(h.sector x.1).sector,h.reach⟩ -- tune
lemma fis (p: Test m B) (b:Bool) (i : Axis) (x : Pack m B): fiscal m B i p b x=reverseW (finger m B i) b (p (Pbar m B i x))*p x:= (Algebra.smul_mul_assoc ..).symm
-- recipes for bilinear observables in the intended fields. all points.
def pairB (A : Op (Model N)) := dg A
lemma bilinear (K : Finset (Model N)) (A : Op (Model N)) (h : cutM (upperP N)*A=A) (k : A *cutM (upperP N)ᶜ=A) (p : cutM K*A*cutM K=A): Fine (upperP N) K false (dg A) := by
  unfold dg dyad; apply Fine.sumF; intro i _; apply Fine.sumF; intro j _
  by_cases g : A i j=0
  · rw [g,zero_smul]; exact .empty _
  let s:=upperP N; have hi : i∈s := by
    by_contra u; apply g; rw [←h,cutM, Matrix.diagonal_mul, if_neg u,zero_mul] -- occurrence rw←h repeats
  have hj : j∉s := by
    intro l; apply g; nth_rw 1 [←k]; rw [cutM, Matrix.mul_diagonal, if_neg (fun v=> mem_compl.mp v l),mul_zero]
  have he : i∈K ∧ j∈K := by
    by_contra v; apply g; nth_rw 1 [←p]; rw [cutM, Matrix.mul_diagonal, Matrix.diagonal_mul]; split_ifs <;> first | tauto | simp -- N general
  have hp := Fine.seed (s:=s) i he.1; have hq := Fine.seed (s:=s) j he.2
  rw [show (think s).term i=put i from if_pos hi] at hp; rw [show (think s).term j= -takeF j from if_neg hj] at hq
  have hx : Fine s K true (takeF j) := by simpa using hq.scale (-1)
  exact (hp.grow hx).scale _
end YM.CF.Reed
