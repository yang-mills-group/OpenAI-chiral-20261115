import YM.CF.Reed.Shift

/-! Turning on same toron field and testing shift in all flavors. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Reed.Bare
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Kronecker
open Function Filter NormedSpace SU Lat Lattice Cube Finset BZ
attribute [local instance] opCStarAlgebra
variable {N : Side}
def guide (x:ℝ) : F→ℂ:=fun i=> phase (if i=0 then -x else if i=1 then x else 0)
def share (x:ℝ):UNI F:=⟨Matrix.diagonal (guide x),by
  apply Matrix.mem_unitaryGroup_iff.mpr; unfold guide; rw [show star (Matrix.diagonal _)= Matrix.diagonal fun i:F=> star (guide x i) from by ext i j; by_cases h:i=j <;> simp [h,Ne.symm,guide]]; rw [Matrix.diagonal_mul_diagonal]
  simp only [guide,phase_one]; simp⟩
def cue (x:ℝ):E:=⟨share x,by
  change Matrix.det (Matrix.diagonal (guide x))=1; unfold guide; rw [Matrix.det_diagonal]; simp [F,Fin.prod_univ_succ,phase, ←Complex.exp_add] -- tune
    ⟩
def fortune (x : ℝ) (k:F) : ℝ:= if k=0 then -x else if k=1 then x else 0
def infla (t:Slot) (x:ℝ) := match t.2 with
  | .inl p=>fortune x p.val.1+fortune x p.val.2
  | .inr i=> -fortune x i
lemma nega (p:ℝ):phase (-p)=star (phase p) := by unfold phase; rw [show star (Complex.exp _)=Complex.exp (star (↑p*Complex.I)) from (Complex.exp_conj _).symm]; simp
lemma clothes (x:ℝ) : (matter (cue x)).val=Matrix.diagonal (fun t=>phase (infla t x)) := by
  rw [matter_matrix, triple, each,show fund (cue x)=Matrix.diagonal (guide x) from rfl,ExTwo.wedge_diag]; ext ⟨b,l⟩ ⟨c,v⟩; cases l <;> cases v <;> simp [Join.both, infla,fortune,Pi.smul_apply,Matrix.one_apply, Matrix.diagonal_apply,phase_ext, guide, nega] <;> split_ifs <;> simp_all -- tune
-- legal domain

def flat (N:Side) (p:Mom) : Bkg (More N):=fun i=>cue (p i.2/2)
def addend (p:Mom) (t:Slot) (i:Axis):=2*infla t (p i/2)
lemma twice (p:Mom) x i : (matter ((links (flat N p)) (x,i))).val=Matrix.diagonal (fun s=>phase (addend p s i)) := by
  unfold links flat; simp only [map_mul]; change (matter (cue _)).val * (matter (cue _)).val=_; rw [clothes,Matrix.diagonal_mul_diagonal]; simp only [←phase_ext,addend,two_mul]
lemma cueComm (x y : ℝ) : Commute (cue x) (cue y):= by
  unfold Commute SemiconjBy; apply Subtype.ext; apply Subtype.ext; change Matrix.diagonal (guide x)*Matrix.diagonal (guide y)= Matrix.diagonal (guide y)*Matrix.diagonal (guide x); rw [Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]; simp only [mul_comm]
lemma flatGuard (p:Mom) (e:ℝ) (h:0≤e): Guard (flat N p) e := by
  have ht (x : Site (More N)) i j : travel (flat N p) x (Lattice.square i j)=1 := by
    have he := cueComm ((p i)/2) ((p j)/2); simp only [Lattice.square, travel,Step.pos_read,Step.neg_read,mul_one]; unfold flat; rw [← mul_assoc _ _ (_ * _),he.eq]; group
  constructor <;> (intro x i j _; rw [ht,map_one]; change ‖1-(1:Op _)‖≤_; simpa)
-- for bar5 all three, flat angles tuned pass, near variation nonzero.
abbrev ply (i:Fin 3):Slot:=(i,Sum.inr 0)
def era (p:Mom) (x:Site N) (i:Fin 3): Op SpinIdx := let W:=scan N (addend p) x (ply i); W.plus*projector W.H
lemma bunch (p:Mom) (i:Fin 3) : addend p (ply i)=p := by funext x; simp [addend,ply,infla,fortune]; ring
lemma p_test {n X Y : Type*} [Fintype n] [DecidableEq n] (W : WilsonFrame n) (v : (X→Y→Op SpinIdx)→ₐ[ℝ] Op n) (A) (h:v A=W.chir) : W.plus=v ((1/2:ℝ) • (1+A)):= by rw [map_smul v,map_add v,map_one v,h,WilsonFrame.plus]
lemma hitTest {n X Y : Type*} [Fintype n] [DecidableEq n] [Nonempty n] (W : WilsonFrame n) (v : (X→Y→Op SpinIdx)→ₐ[ℝ] Op n) (A : X→Y→WilsonFrame SpinIdx) (h : v (fun x y=>(A x y).chir)=W.chir) (g : v (fun x y=>projector (A x y).H)= projector W.H) (p : Safe W.H) : W.overlap*projector W.H=v (fun x y=>(A x y).plus * projector (A x y).H):= by
  rw [W.overlap_action p,←g, p_test W v _ h]; exact (map_mul v (fun x y=>(A x y).plus) (fun x y=>projector (A x y).H)).symm
lemma support (p:Mom) : let W:=frame matter (links (flat N p)) (anticut N); W.overlap*projector W.H=fillT N (fun k x=> (scan N (addend p) k x).plus *projector (scan N (addend p) k x).H) := by
  intro W; have hp := ((flatGuard (N:=N) p 0 le_rfl).children le_rfl); have he : Safe W.H:= band matter (links (flat N p)) (anticut N) (hp.shrink (e:=_) (f:=1/60) (by norm_num)).2
  exact hitTest (n:=Model N) W (fillT N) (scan N (addend p)) (fillSpin (N:=N) grading) ((fillProj _ (addend p) (twice p)).symm) he
lemma vertex (k:Site N) (v:Mom) (i:Fin 3) : HasDerivAt (fun t:ℝ=>era (t • v-pm k) k i*(1-gPos)) ((1/2:ℝ) • (symbolD v*(1-gPos))) 0 := by
  unfold era scan; simp_rw [bunch,add_sub_cancel]; simp_rw [← WilsonFrame.overlap_action _ (atom_safe _)]; exact linear_kinetic v
end YM.CF.Reed.Bare
