import YM.CF.Reflect.Beam
import YM.CF.Reflect.Paint

/-! Coefficient-level hopping and sector. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.RP
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Kronecker
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant Phase Mir Mir.Trip MeasureTheory Finset
attribute [local instance] opCStarAlgebra
variable {m B : Side} (i : Axis) (U : Skin m B) (v : Pack m B)
lemma term_off (c) (j : Axis) (e:i≠j) : let P := Ledge m B i; let Q := Tedge m B i; let X := Vplus c (links U) j;
    P*X*Q=0 ∧ Q*X*P=0 := by
  intro P Q X
  have he (x y:Foot m B) (h:advance j x=y) : x∈posY m B i↔ y∈posY m B i := by rw [← h]; simp [advance,posY,e]
  constructor <;> (ext x y; unfold P Q Ledge Tedge; rw [pinch,show X=Vplus c _ j from rfl,plus_block]; simp only [Matrix.zero_apply, mem_compl,colony_at,jump_apply])
  · split_ifs with g h; exact (g.2 ((he _ _ h).mp g.1)).elim; rfl; rfl
  split_ifs with g h; exact (g.1 ((he _ _ h).mpr g.2)).elim; rfl; rfl
lemma onsite_off : Tedge m B i*spin (CSide m B) Slot grading*Ledge m B i=0 := by
  ext x y; rw [Ledge,Tedge,pinch,spin]; simp only [Matrix.zero_apply,mem_compl,colony_at,jump_apply,Equiv.refl_apply]; split_ifs with h k; exact (h.1 (k ▸ h.2)).elim; rfl; rfl
lemma acrossM c : Tedge m B i*wiel m B (axisCut m B i c) U *Ledge m B i= -bendK i U (enter m B i)+ -bendK i U (exitK m B i) := by
  let P := Ledge m B i; let Q := Tedge m B i; let A := axisCut m B i c; let V j := Vplus A (links U) j
  rw [wiel,supportH]; change Q*(_+∑ j:Axis,(V j+star (V j)))*P=_
  rw [mul_add,add_mul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, onsite_off i, smul_zero,zero_add, mul_sum,sum_mul,sum_eq_single_of_mem _ (mem_univ i)]; rw [mul_add, add_mul]; exact congrArg₂ (·+·) (entryH i U c) (exitH i U c)
  intro j _ l; have he := term_off i U A j (Ne.symm l); rw [mul_add,add_mul, he.2,zero_add];
  have hk := congrArg star (show P*V j*Q=0 from he.1); rw [star_zero,star_mul, star_mul,show star Q=Q from (cutM_idp _).2,show star P=P from (cutM_idp _).2,←mul_assoc] at hk; exact hk
lemma inc_area {U w : Pack m B} (h : NorthOf m B i U w) c j : Ledge m B i*Vplus c (links U.1) j*Ledge m B i=Ledge m B i*Vplus c (links w.1) j*Ledge m B i := by
  ext x y; rw [Ledge,pinch,pinch]; split_ifs with g; simp only [colony_at] at g; rw [plus_block,plus_block]; simp only [jump_apply]; split_ifs with l; unfold hop; rw [upward i U w h _ g.1 g.2 (show x.1+step j=y.1 from l)]; rfl; rfl
lemma sup_area {U w : Pack m B} (h : NorthOf m B i U w) c : Ledge m B i*wiel m B c U.1 * Ledge m B i=Ledge m B i*wiel m B c w.1*Ledge m B i := by
  unfold wiel; rw [supportH,supportH]; simp only [mul_add,mul_sum,add_mul,sum_mul,inc_area i h]
  let P := Ledge m B i
  have he j : P*star (Vplus c (links U.1) j)*P=P * star (Vplus c (links w.1) j)*P := by
    have H := congrArg star (inc_area i h c j); simp only [star_mul, show star (Ledge m B i)=Ledge m B i from (cutM_idp _).2, ←mul_assoc] at H; exact H
  -- simp_rw explicit
  simp_rw [show ∀ j, Ledge m B i*star (Vplus c (links U.1) j)*Ledge m B i=_ from he]
  rfl
lemma enter_area {U w : Pack m B} (h : NorthOf m B i U w) : enter m B i U.1=enter m B i w.1 := by
  unfold enter; apply congrArg; funext z; unfold lower; split <;> try rfl
  rename_i f; have he := back_mid i f; rw [show U.1 _=w.1 (node z-step i,i) from h.gaugeS (node z-step i,i) he (show node z-step i+step i∈ _ by rw [sub_add_cancel]; exact (holder i z).mp (begin_pos i z f))]
lemma exit_area {U w : Pack m B} (h : NorthOf m B i U w) : exitK m B i U.1=exitK m B i w.1 := by
  unfold exitK; apply congrArg; funext z; unfold upper; split <;> try rfl
  rename_i f; have he := finis_pos i z f; rw [show U.1 _= w.1 (node z,i) from h.gaugeS _ ((holder i z).mp he) (link_mid i he i)]
lemma enter_pos : Ledge m B i * enter m B i U=enter m B i U := by
  unfold Ledge; ext x y; rw [cutM, Matrix.diagonal_mul]; by_cases h:x∈colony m B i; rw [if_pos h,one_mul]
  have he : ¬Begin (m:=m) (B:=B) x.1 i := fun g=>h ((colony_at x i).mpr (begin_pos i _ g)); simp [h,enter,jump_apply,lower,he]
lemma exit_pos : Ledge m B i * exitK m B i U=exitK m B i U := by
  unfold Ledge; ext x y; rw [cutM, Matrix.diagonal_mul]; by_cases h:x∈colony m B i; rw [if_pos h,one_mul]
  have he : ¬Finis (m:=m) (B:=B) x.1 i := fun g=>h ((colony_at x i).mpr (finis_pos i _ g)); simp [h,exitK,jump_apply,upper,he]
lemma enter_cont : Continuous (enter m B i) := by
  apply Continuous.comp (jump_cont _) -- tune
  apply continuous_pi; intro x; unfold lower; split <;> try exact continuous_const
  have hx := matter_cont.comp ((continuous_apply (node x-step i,i) : Continuous (fun U:Skin m B=>U _)).inv)
  apply continuous_matrix; rintro ⟨j,l⟩ ⟨k,y⟩; exact continuous_const.mul (hx.matrix_elem l y)
lemma exit_cont : Continuous (exitK m B i) := by
  apply Continuous.comp (jump_cont _) -- tune
  apply continuous_pi; intro x; unfold upper; split <;> try exact continuous_const
  have hx := matter_cont.comp (continuous_apply (node x,i) : Continuous (fun U:Skin m B=>U _))
  apply continuous_matrix; rintro ⟨j,l⟩ ⟨k,y⟩; exact continuous_const.mul (hx.matrix_elem l y)
lemma wiel_cont (c) : Continuous (wiel m B c) := (H_cont matter c matter_cont).comp links_cont
lemma self_wiel (m B c U) : IsSelfAdjoint (wiel m B c U) := WilsonFrame.selfadjoint _
end YM.CF.RP
