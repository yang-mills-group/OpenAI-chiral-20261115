import YM.CF.Lattice.Bare
import YM.CF.Cubes.Refine
import YM.CF.Matter.Mass

/-! Exact link vertex kinematics in the toral test. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Reed.Bare
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Kronecker
open Function Filter NormedSpace SU Lat Lattice Cube Finset BZ
attribute [local instance] opCStarAlgebra
variable {N m B : Side}
-- diagonal commuting at half hops. channels independent labels
def blockT (v : Slot→ Op SpinIdx) : Op (SpinIdx × Slot) := Matrix.of fun i j=>if i.2=j.2 then v i.2 i.1 j.1 else 0
lemma bloc_i (v w) : blockT v*blockT w=blockT (v*w) := by
  ext ⟨i,p⟩ ⟨j,q⟩; rw [Matrix.mul_apply,Fintype.sum_prod_type,sum_comm,sum_eq_single_of_mem _ (mem_univ p)]
  · by_cases g:p=q <;> simp [g,blockT,Matrix.mul_apply]
  intro l _ h; simp [blockT,h.symm]
lemma bloc_p (v w) : blockT v+blockT w=blockT (v+w) := by ext i j; by_cases g:i.2=j.2 <;> simp [blockT,g]
lemma bloc_star (v) : star (blockT v)=blockT (star v) := by
  ext ⟨i,p⟩ ⟨j,q⟩; by_cases e:p=q
  · subst q; simp [blockT]
  simp [blockT,e,Ne.symm e]
lemma bloc_e (v: Op SpinIdx) : blockT (fun _=> v)=v ⊗ₖ (1:Op Slot) := by ext ⟨i,p⟩ ⟨j,q⟩; by_cases g:p=q; subst q; simp [blockT]; simp [blockT,g]
lemma bloc_u : blockT 1=1 := (bloc_e 1).trans Matrix.one_kronecker_one
lemma bloc_s (c:ℝ) (v) : blockT (c • v)=c • blockT v := by ext i j; by_cases g:i.2=j.2 <;> simp [blockT,g]
abbrev mapN (N:Side):= Site N→ Slot→ Op SpinIdx
def vector (v:mapN N): Op (Model N) := jump (Equiv.refl _) (blockT ∘ v)
def jumpT (N : Side): mapN N→ₐ[ℝ] Op (Model N) where
  toFun:=vector
  map_zero':= by ext i j; by_cases g:i.1=j.1 <;> simp [vector,blockT,g,jump_apply]
  map_one' := by unfold vector; simp only [Function.comp_def,Pi.one_apply,bloc_u,jump_id]
  map_add' v w:= by unfold vector; rw [←jump_add]; apply congrArg;  funext i; exact (bloc_p ..).symm
  map_mul' v w:= by unfold vector; rw [jump_mul,Equiv.refl_trans]; apply congrArg;  funext i; exact (bloc_i ..).symm
  commutes' c:= by
    simp_rw [Algebra.algebraMap_eq_smul_one]; change vector (c • 1)=_; unfold vector; simp only [Function.comp_def,Pi.smul_apply,Pi.one_apply]; ext i j; rw [jump_apply]; rw [show blockT (c • 1)= c • 1 by rw [bloc_s,bloc_u]]; by_cases g:i=j; subst j; simp; by_cases h:i.1=j.1
    · have he : i.2≠j.2:= fun h'=>g (Prod.ext h h'); simp [g,h,he]; -- tune
    simp [g,h]
def fillT (N : Side) : mapN N →ₐ[ℝ] Op (Model N) := (twist (spatialU N Slot)).toAlgEquiv.toAlgHom.comp (jumpT N)
lemma fillStar (A : mapN N): fillT N (star A)=star (fillT N A) := by
  change twist _ (vector _)=star (twist _ (vector _)); rw [← map_star]; apply congrArg; rw [vector,vector,jump_star]; simp only [Function.comp_def, Equiv.refl_symm,Equiv.refl_apply,Pi.star_apply,← bloc_star]
lemma fillSpin (A : Op SpinIdx): fillT N (fun _ _=> A)=spin N Slot A := by change twist _ (vector _)=_; rw [twist_bands_spin Slot A]; congr 1; unfold vector bands; simp [Function.comp_def,bloc_e]
-- forward Fourier commuting symbols of color. test representation.
variable (U : Bkg N) (c : Slot→ Mom) (g : ∀ x i, (matter (U (x,i))).val=Matrix.diagonal (fun s=>phase (c s i)))
include g
def scan (N : Side) (c : Slot→ Mom) (k : Site N) (x:Slot):= atom (pm k + c x)
omit g in
lemma phase_ext (a b:ℝ) : phase (a+b)=phase a*phase b := by unfold phase; rw [Complex.ofReal_add,add_mul,Complex.exp_add]
lemma fillShift (i:Axis) : shift matter U (anticut N) i=fillT N (fun k x=>(scan N c k x).T i) := by
  let F := fun k x=>(scan N c k x).T i
  change shift _ _ _ _=twist (spatialU N Slot) (vector F); apply eq_twist; ext ⟨x,a⟩ ⟨y,b⟩; rw [shift,vector]
  rw [rowBlock,colBlock];
  have he l q (p : Site N) : hop matter U (anticut N) i p l q = if l=q then seam (anticut N) p i*phase (c l.2 i) else 0 := by
    unfold hop color; rw [g]; by_cases h:l=q
    · subst q; simp
    by_cases k:l.1=q.1
    · have e:l.2≠q.2:= fun u=>h (Prod.ext k u); simp [h,k,e]
    simp [h,k]
  -- after col collapse with identity Fourier
  simp only [he,ite_mul,zero_mul,sum_ite_eq,mem_univ,ite_true]
  rw [sum_eq_single a] -- tune which column
  · by_cases h:a=b
    · subst b; simp only [spatialU,Matrix.kronecker_apply, Matrix.one_apply_eq,mul_one, Function.comp_apply, blockT, Matrix.of_apply,ite_true,F,atom,scan, Pi.add_apply,phase_ext, Matrix.smul_apply, smul_eq_mul,one_mul]
      rw [show _=seam (anticut N) x i*Fourier N (advance i x) y*phase (c a.2 i) from mul_right_comm .., HF]; ring -- tune
    -- Fourier delta; need distinct spin/slot
    by_cases k:a.2=b.2
    · have e:a.1≠b.1:= fun u=> h (Prod.ext u k); simp [spatialU,h,k,e,blockT,F,atom,scan]
    simp [spatialU,h,k,blockT]
  · intro j _ h; simp [spatialU,h.symm]; -- tune
  simp
omit g
lemma anyT {n A E : Type*} [Fintype n] [DecidableEq n] (F : (A→E→Op SpinIdx)→ₐ[ℝ] Op n) (W : WilsonFrame n) (T:A→ E→WilsonFrame SpinIdx) (ht : ∀ i,F (fun k x=>(T k x).T i)=W.T i) (hx : ∀ i,F (fun k x=>(T k x).gamma i)=W.gamma i) (hv : F (fun k x=>(T k x).chir)=W.chir) (f : ∀ Y,F (star Y)=star (F Y)) : W.H=F (fun k x=>(T k x).H) := by
  have he i : F (fun k x =>(T k x).inc i)=W.inc i := by
    let A:A→E→Op SpinIdx:=fun k x=>(T k x).T i
    change F (1-(1/2:ℝ) • (A+star A)+(fun k x=>(T k x).gamma i)*((1/2:ℝ) • (A-star A)))=_
    rw [map_add F,map_sub F,map_one F,map_smul F,map_add F,map_mul F,map_smul F,map_sub F]; rw [f A,show F A=W.T i from ht i, hx]; rfl
  let A (i:Axis):A→E→Op SpinIdx:= fun k x=>(T k x).inc i
  have hU : (fun k x => (T k x).H0)= -1+∑ i,A i := by funext k x; simp only [WilsonFrame.H0,Pi.add_apply,Pi.neg_apply,Pi.one_apply,Finset.sum_apply]; rfl
  have heq : F (fun k x=> (T k x).H0)=W.H0 := by rw [hU,map_add F,map_neg F,map_one F,map_sum]; unfold WilsonFrame.H0; apply congrArg; exact sum_congr rfl (fun j _=> he j)
  change W.chir*W.H0= F ((fun k x=>(T k x).chir)*(fun k x=>(T k x).H0))
  rw [map_mul F,hv,heq]
include g
lemma fill_w : let W:= frame matter U (anticut N); W.H=fillT N (fun k x=>(scan N c k x).H) := by
  intro W; exact anyT _ W _ (fun i=>(fillShift U c g i).symm) (fun i=> fillSpin (N:=N) (gammaOp i)) (fillSpin (N:=N) _) fillStar
lemma fillProj : let W:=frame matter U (anticut N); projector W.H=fillT N (fun k x=> projector (scan N c k x).H) := by
  intro W; let A:mapN N := fun k x=> (scan N c k x).H; let Q:=fillT N; let B:mapN N:= fun k x=>rsEval (A k x); have ht : W.H=Q A:= fill_w U c g
  have he : ∀ i j, Commute (W.T i) (W.T j) := by
    intro i j; rw [show W.T i=_ from fillShift U c g i,show W.T j=_ from fillShift U c g j]; apply Commute.map
    unfold Commute SemiconjBy; funext k x; exact (Commute.one_left _).smul_left (_:ℂ)|>.smul_right (_:ℂ) -- tune
  have hW : Safe (Q A) := by
    rw [←ht]; refine ⟨W.selfadjoint,W.bounded.trans (by norm_num),?_⟩
    apply le_trans _ (W.gap (e:=1/60) (fun i j _=> (show Switch (W.T i) (W.T j) (1/60) from by unfold Switch; rw [(he i j).eq,sub_self,norm_zero]; norm_num))) -- tune
    norm_num
  have hs : HasSum (fun i k x=> rsTerm (A k x) i) B := by rw [Pi.hasSum]; intro k; rw [Pi.hasSum]; exact fun x=> rs_sum ((atom_safe _).good.trans_lt rho_lt)
  have hx : HasSum (rsTerm (Q A)) (Q B) := by
    convert! hs.map Q Q.toLinearMap.continuous_of_finiteDimensional using 1; ext1 i; change rsTerm (Q A) i=Q (fun k x=>rsTerm (A k x) i)
    rw [show (fun k x=>rsTerm (A k x) i) = SignScalar.c i • (1 - (1/256:ℝ) • A^2)^i from by funext k x; simp only [rsTerm,slack,Pi.smul_apply,Pi.pow_apply,Pi.one_apply,Pi.sub_apply], map_smul,map_pow,map_sub,map_one,map_smul,map_pow]; rfl
  rw [ht]; change projector (Q A)=Q (fun k x=>projector (A k x)); rw [show (fun k x=> projector (A k x))=((1/2:ℝ) • (1+((1/16:ℝ) • A)*B)) from by funext k x; simp only [projector,polarity,B,Pi.smul_apply,Pi.add_apply,Pi.one_apply,Pi.mul_apply]]; rw [projector,polarity,(rs_sum (hW.good.trans_lt rho_lt)).unique hx, map_smul,map_add,map_one,map_mul,map_smul]
end YM.CF.Reed.Bare
