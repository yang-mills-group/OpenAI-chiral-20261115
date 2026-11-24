import YM.CF.Reflect.Center

/-! Reference sea orientation. Does not replace the variable chiral line. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Lat
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Kronecker
open Function Fock Filter NormedSpace SU Lattice Branch Cube Tenant Phase Mir RP Finset
attribute [local instance] opCStarAlgebra
variable {N : Side}
def plusHalf := (Finset.univ:Finset SpinIdx).filter (fun i=>(i.val:ℕ)<2)
def upperP (N : Side) := (Finset.univ:Finset (Model N)).filter fun i=> i.2.1∈plusHalf
lemma plane_diag (N : Side) : cutM (upperP N)= spin N Slot (cutM plusHalf) := by
  unfold spin; ext ⟨x,i,j⟩ ⟨y,k,l⟩; by_cases h:x=y <;> by_cases g:i=k <;> by_cases e:j=l <;> simp [h,g,e,jump_apply,cutM,upperP]
lemma raising : cutM plusHalf=(1/2:ℂ) • (1+grading) := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [SpinIdx, Matrix.one_apply, Matrix.diagonal_apply, plusHalf,cutM,grading]
lemma overJ : cutM plusHalf*spinJ=spinJ*cutM plusHalf := by
  rw [raising, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,add_mul,mul_add,one_mul,mul_one,spinJ_grading,(show cc grading=grading by ext x y; fin_cases x <;> fin_cases y <;> simp [grading])]
lemma onsite_ref (x : Site N→ Vect) : Commute (cutM (upperP N)) (Cfield x) := by
  rw [plane_diag]; unfold spin Cfield Commute SemiconjBy; simp only [jump_mul,Equiv.refl_trans];
  apply congrArg; funext i; simp only [localPair, Equiv.refl_apply,op_kron_mul,one_mul,mul_one,overJ]
lemma turn_plus (t : Site N→E) : cutM (upperP N)*(conjG matter t).val=(conjG matter t).val*cutM (upperP N) := by rw [plane_diag]; have h:= twist_product (conjG matter t) (spin N Slot (cutM plusHalf)); rw [twist_spin] at h; exact h
lemma slide_plus {m B} (i) :
    twist (finger m B i) (cutM (upperP (CSide m B))ᶜ)=cutM (upperP (CSide m B)) := by
  -- grading
  let N := CSide m B; let D := grading; let V := finger m B i
  rw [dim_cut, plane_diag,raising, show spin (CSide m B) Slot ((1/2:ℂ) • (1+D)) = (1/2:ℂ) • (1+spin N Slot D) by
    unfold spin
    have he : ∀ A A':Op SpinIdx, spin N Slot (A+A')=spin N Slot A+spin N Slot A' := by
      intro A A'; unfold spin; rw [←jump_add]; congr 1; funext x; ext x y; simp [add_mul]
    have hr (A:Op SpinIdx) (c:ℂ) : spin N Slot (c • A)=c • spin N Slot A := by
      unfold spin; rw [←jump_smul]; congr 1; funext x; ext p q; simp [mul_assoc]
    change spin N Slot _=_; rw [hr,he,spin_one]; rfl]
  rw [map_sub,map_one,twist_scalar,map_add,map_one, show twist (finger m B i) (spin N Slot grading)= -spin N Slot grading by
    change twist (pinM N i*siteM _) _=_; rw [Fock.twin,siteSpin,pin_grades]]; rw [smul_add,smul_add,smul_neg]; module -- tune
lemma det_of_plus (t : Site N → E) : quant (conjG matter t).val (upperP N) (upperP N)=1 := by
  rw [Fock.principal]; unfold padded; rw [plane_diag];
  let S := cutM plusHalf; let A := S ⊗ₖ (1 : Op Slot)
  let B (x : Site N) := S ⊗ₖ (matter (t x)).val
  have hk : spin N Slot S*(conjG matter t).val* spin N Slot S=jump (Equiv.refl _) B := by
    simp only [conjG,spin,jump_mul,color,Equiv.refl_trans,Equiv.refl_apply,op_kron_mul,one_mul,mul_one,
      show S*S=S from (cutM_idp _).1]
    rfl
  let X := fun x:Site N=> B x+ (1-A)
  rw [hk, ←jump_id (X:=Site N) (n:=SpinIdx × Slot)]; change (jump _ _ + (_-jump _ (fun _=>A))).det=_; rw [←jump_sub, ←jump_add,jump_det]
  apply prod_eq_one; intro x _; change (X x).det=1
  let C (i : SpinIdx) := if i∈plusHalf then (matter (t x)).val else (1:Op Slot)
  rw [show X x=jump (Equiv.refl _) C by
    unfold X B A S; ext p q; by_cases h : p=q
    · subst q; by_cases g:p.1∈plusHalf <;> simp [C,cutM,jump_apply,g]
    by_cases g:p.1=q.1
    · have hx : p.2≠q.2 := fun e=> h (Prod.ext g e); by_cases u:p.1∈plusHalf
      · have hu : q.1∈plusHalf := g ▸ u; simp [C,cutM,g,h,hu,hx,jump_apply]
      have hu : q.1∉plusHalf := g ▸ u; simp [C,cutM,g,h,hu,hx,jump_apply]
    simp [g,h,jump_apply,cutM], jump_det]
  apply prod_eq_one; intro i _; unfold C; split; exact triple_det (t x); exact Matrix.det_one -- tune
lemma pf_p (x : Site N → Vect) (t : Site N → E) : pf (Cfield (turnX t x)) (upperP N)=pf (Cfield x) (upperP N) := by
  rw [Cfield,Cfield] -- tune
  change pf (Cfield (fun i=>turn _ _)) _=_
  rw [C_gauge,pf_frame (turn_plus t).symm,det_of_plus,one_mul]; rfl
def uniqueR (N : Side) (x : Site N) : Vect := basisKet 0
lemma unique_r (N x) : ‖uniqueR N x‖=1 := by simp [uniqueR,basisKet]
def unitV (N : Side) := pf (Cfield (uniqueR N)) (upperP N)
lemma unit_phase (N : Side) : ‖unitV N‖=1 := pf_unit (upperP N) ⟨_,C_unit _ (unique_r N)⟩ (C_skew _ (unique_r N)) (onsite_ref _)
lemma pf_free (x : Site N → Vect) (h : ∀ i, ‖x i‖=1) : pf (Cfield x) (upperP N)=unitV N := by
  choose a p using fun i=> SU.Pair.reachable (x i) (h i)
  have hx : turnX a (uniqueR N)=x := by funext i; apply PiLp.ext; intro j; exact congr_fun (p i) j
  rw [←hx,pf_p]; rfl
-- state bra
def linearB (N : Side) := unitV N • basisKet (upperP N)
lemma ref_frame (t : Site N→E) : turnW t (linearB N)=linearB N := by
  unfold turnW linearB; rw [map_smul]; congr 1; apply PiLp.ext; intro i; rw [basis_act]; let V := (conjG matter t).val
  change quant (n:=Model N) V i (upperP N)= _; by_cases g:i=upperP N; subst i; simp [det_of_plus,V]
  rw [col_unique (turn_plus t).symm _ (Ne.symm g),basis_apply,if_neg g]
lemma harvest (x : Site N→Vect) (h : ∀ i, ‖x i‖=1) : pairWave (n:=Model N) (Cfield x)=acts (exp (seedR (upperP N) (Cfield x))) (linearB N) := by rw [linearB,←pf_free x h]; exact ripe (upperP N) ⟨_,C_unit x h⟩ (C_skew x h) (onsite_ref x)
lemma bra_fix (A : FC (Model N)) : inner ℂ (linearB N) (acts A (linearB N))= A (upperP N) (upperP N) := by
  unfold linearB; rw [map_smul,inner_smul_left,inner_smul_right]; change star (unitV N)*(unitV N*_)=_; rw [←mul_assoc,scale_unit_self (unit_phase N),one_mul,basis_inner,basis_act]
end YM.CF.Lat
