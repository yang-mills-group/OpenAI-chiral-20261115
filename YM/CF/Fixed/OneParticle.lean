import YM.CF.Fixed.Geometry
import YM.CF.Spire.Stand

/-!
The lifts of time reflection to use in FiniteGaugeData. Be careful with changing the anticut!
This convention uses the literal unrelocated anticut, even on the negative side.
-/

set_option autoImplicit false
noncomputable section

namespace YM.CF.Fixed
open Function Fock NormedSpace SU Lat Lattice Cube Finset Scroll Tulip Dial
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker
attribute [local instance] opCStarAlgebra

variable (N : Side) (i : Axis)

/-- This is literally the `Emu.halfS`. -/
def upperIndices : Finset (Single N) := univ.filter fun x => x.1.2 ∈ plusHalf

abbrev pinSpin : UNI SpinIdx := ⟨Mir.pin i, Mir.pin_U i⟩
/-- Reflection (includes the sign due to the seam). This is a *lift of
reflection*, not the adjoint on the spin at a site. -/
abbrev reflectP := prepU (reflShape i) (pinSpin i) inert N
/-- Same spin at a site, without the spacetime map or any seam. -/
abbrev adjSpin : UNI (Single N) :=
  ⟨love N (Mir.pinM N i).val, by
    apply Matrix.mem_unitaryGroup_iff.mpr
    rw [←map_star,←map_mul,(Mir.pinM N i).property.2,map_one]⟩

lemma Tset_upperIndices : Spire.Tset N=upperIndices N := by
  ext x
  rcases x with ⟨⟨x,r⟩,y⟩
  simp [upperIndices,Spire.Tset,helix,upperP]

lemma tickA_upper : tickA N = cutM (upperIndices N) :=
  (Spire.touchP N).trans (congrArg _ (Tset_upperIndices N))

lemma mirror_payA (x : Site N) : Shape.payA (reflShape i) x= -1 := by
  have h (j:Axis) : (reflShape i).rent x j = if i=j then -1 else 0 := by
    change Rush.periods N ((reflShape i).flee _) j = _
    rw [mirror_flee]; unfold Rush.periods
    have p : 0 < (N.val : ℤ) := by exact_mod_cast N.property
    have hx:= ZMod.val_lt (x j)
    simp only [Pi.sub_apply, Signed.act, Signed.mirror, Equiv.refl_symm,
      Equiv.refl_apply, step_apply, Rush.natural]
    by_cases g:i=j
    · simp only [g, decide_true, ite_true]
      subst j
      apply le_antisymm
      · apply (Int.ediv_le_iff_le_mul p).mpr; rw [neg_one_mul]; omega
      apply (Int.le_ediv_iff_mul_le p).mpr; rw [neg_one_mul]; omega
    simp only [g, Ne.symm g, decide_false, Bool.false_eq_true, ite_false, sub_zero];
    exact Int.ediv_eq_zero_of_lt (by omega) (by omega)
  unfold Shape.payA Rush.fee
  rw [Finset.prod_eq_single i]
  · simp [h]
  · intro b _ g; simp [h, Ne.symm g]
  simp

lemma reflect_readout :
    (reflectP N i).val = love N (jump (Tofu (reflShape i) N)
        (fun _=> -(Mir.pin i ⊗ₖ (1:Op Slot)))) := by
  change love N (jump _ fun z => (milU (reflShape i) (pinSpin i) inert z).val)=_
  simp only [mirror_payA, neg_one_smul]
  rfl

lemma reflectP_square : (reflectP N i).val*(reflectP N i).val = -1 := by
  -- two pin matrices, also two antiperiodic signs
  rw [reflect_readout,←map_mul,jump_mul];
  rw [show (Tofu (reflShape i) N).trans (Tofu (reflShape i) N)=Equiv.refl _ from
      Equiv.ext fun x=> square_partnerSite N i x]
  simp only [neg_mul_neg,op_kron_mul,Mir.pin_square,one_mul,op_kron_neg,
    Matrix.one_kronecker_one]
  rw [jump_neg,jump_id,map_neg,map_one]

lemma adjSpin_square : (adjSpin N i).val*(adjSpin N i).val = -1 := by
  change love N (spin N Slot (Mir.pin i))*love N (spin N Slot (Mir.pin i))= _
  rw [←map_mul, Lat.spin_mul, Mir.pin_square, Lat.spin_neg, Lat.spin_one, map_neg,map_one]

lemma reflectP_upper : twist (reflectP N i) (cutM (upperIndices N)ᶜ) =
    cutM (upperIndices N) := by
  rw [← Tset_upperIndices];
  have he : twist (reflectP N i) (cutM (Spire.Tset N)) = 1 - cutM (Spire.Tset N) :=
    Spire.tickR (reflShape i) inert (pinSpin i) (mirrorX i) N
  rw [dim_cut,map_sub,map_one,he]; abel

lemma adjSpin_upper : twist (adjSpin N i) (cutM (upperIndices N)ᶜ) =
    cutM (upperIndices N) := by
  have he (z : ℂ) (A : Op SpinIdx) : spin N Slot (z • A)=z • spin N Slot A := by
    unfold spin; rw [←jump_smul]; congr 1; funext i; ext p q; simp [mul_assoc]
  have hp (A B : Op SpinIdx) : spin N Slot (A+B)=spin N Slot A+spin N Slot B := by
    unfold spin; rw [←jump_add]; congr 1; funext i; ext p q; simp [add_mul]
  have hz : twist (Mir.pinM N i) (1 - cutM (upperP N)) = cutM (upperP N) := by
    rw [map_sub, map_one,plane_diag,raising,he,hp,spin_one, twist_scalar,
      map_add, map_one, Mir.pin_grades]; rw [smul_add,smul_add,smul_neg]; module
  rw [dim_cut,←tickA_upper]
  rw [show tickA N=love N (cutM (upperP N)) from rfl]
  rw [twist_formula] at hz ⊢
  exact (show _ by simpa only [map_mul, map_star, map_sub, map_one] using congrArg (love N) hz)

/-- Allowed fermion indices for this set of gauge sites, using the actual node
map from the FiniteGaugeData regulator. -/
def matterRegion (X : Support (More N)) : Finset (Single N) :=
  univ.filter fun u => node u.1.1 ∈ X

@[simp] lemma mem_matterRegion (u : Single N) (X : Support (More N)) :
    u ∈ matterRegion N X ↔ node u.1.1 ∈ X := by simp [matterRegion]

lemma reflectP_region (X : Support (More N)) :
    twist (reflectP N i) (cutM (matterRegion N X)) = cutM (matterRegion N (reflRegion N i X)) := by
  apply Mir.twist_comm; ext u v
  rw [reflect_readout, cutM, cutM, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [loveAt]
  simp only [unityP, Matrix.submatrix_apply, jump_apply]
  by_cases h : partnerSite N i u.1.1=v.1.1
  · rw [if_pos (show Tofu (reflShape i) N ((helix N u).1)=(helix N v).1 from h)]
    have hg: v∈matterRegion N X ↔ u∈matterRegion N (reflRegion N i X) := by
      rw [mem_matterRegion, mem_matterRegion, ←h, node_partner, mem_reflRegion]
    split_ifs <;> simp_all
  rw [if_neg (show ¬ Tofu (reflShape i) N ((helix N u).1)=(helix N v).1 from h)]
  rw [zero_mul,mul_zero]

lemma adjSpin_region (X : Support (More N)) :
    twist (adjSpin N i) (cutM (matterRegion N X)) = cutM (matterRegion N X) := by
  apply Mir.twist_comm; ext u v
  rw [cutM, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Mir.pinM, loveAt, unityP, Matrix.submatrix_apply, spin, jump_apply]
  by_cases h : u.1.1=v.1.1
  · rw [if_pos (show (Equiv.refl _) ((helix N u).1)=(helix N v).1 from h)]
    have he : u∈matterRegion N X ↔ v∈matterRegion N X := by simp only [mem_matterRegion,h]
    split_ifs <;> simp_all
  rw [if_neg (show ¬ (Equiv.refl _) ((helix N u).1)=(helix N v).1 from h)]
  rw [zero_mul,mul_zero]

lemma tradew_as_jump (g: Site (More N) → SU.E) :
    (tradew N g).val = love N (jump (Equiv.refl _) (fun x: Site N =>
      (1:Op SpinIdx) ⊗ₖ (SU.matter (g (node x))).val)) := by
  -- cf Cascade/Linen.twine
  rw [loveAt]; ext ⟨⟨x,r⟩,q⟩ ⟨⟨y,t⟩,v⟩
  by_cases h:x=y <;> by_cases g':r=t <;> simp [h,g',unityP,helix,tradew,jump_apply]

lemma adjSpin_gauge (g: Site (More N) → SU.E) :
    (adjSpin N i).val * (tradew N g).val = (tradew N g).val * (adjSpin N i).val := by
  rw [tradew_as_jump]
  change love N (spin N Slot (Mir.pin i))*love N _=love N _*love N (spin N Slot (Mir.pin i))
  rw [←map_mul,←map_mul]; unfold spin; simp [jump_mul,op_kron_mul]

lemma reflectP_gauge (g: Site (More N) → SU.E) :
    (reflectP N i).val * (tradew N (reflectedGauge N i g)).val = (tradew N g).val * (reflectP N i).val := by
  rw [tradew_as_jump, tradew_as_jump, reflect_readout, ←map_mul, ←map_mul, jump_mul,jump_mul];
  simp only [Equiv.trans_refl,Equiv.refl_trans, neg_mul,mul_neg,
    op_kron_mul,mul_one,one_mul];
  congr 2
  funext x; rw [show Tofu (reflShape i) N x=partnerSite N i x from rfl, node_partner]; unfold reflectedGauge;
  rw [show (Signed.mirror i).act ((Signed.mirror i).act (node x))=node x from (Signed.mirror i).act_inv _]

end YM.CF.Fixed
