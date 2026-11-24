import YM.CF.Reflect.Hamilton

/-! Nearest transfer across plane uses two half-links. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.RP
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Kronecker
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant Phase Mir Mir.Trip MeasureTheory Finset
attribute [local instance] opCStarAlgebra
variable {m B : Side} (i : Axis) (U : Skin m B)

def lower (m B : Side) (i : Axis) (U : Skin m B) (x : Foot m B) : Op (SpinIdx × Slot) := if Begin x i then (lowB i) ⊗ₖ (matter (U (node x-step i,i))⁻¹).val else 0
def upper (m B : Side) (i : Axis) (U : Skin m B) (x : Foot m B) : Op (SpinIdx × Slot) := if Finis x i then (highB i) ⊗ₖ (matter (U (node x,i))).val else 0
def enter (m B : Side) (i : Axis) (U : Skin m B) := jump (Equiv.refl _) (lower m B i U)
def exitK (m B : Side) (i : Axis) (U : Skin m B) := jump (Equiv.refl _) (upper m B i U)
-- products
lemma pinch (p q : Finset (Model (CSide m B))) (A : Op (Model (CSide m B))) (x y) : (cutM p*A*cutM q) x y=if x∈p ∧ y∈q then A x y else 0 := by
  unfold cutM; rw [Matrix.mul_diagonal,Matrix.diagonal_mul]; by_cases h:x∈p <;> by_cases g:y∈q <;> simp [h,g]
def bendK (U : Skin m B) (T : Skin m B→Op (Xmind m B)) := (finger m B i).val * T (rayUK m B i U)*star (T U) -- tune syntax
lemma begin_back {x y:Foot m B} (g : Begin y i) (h : advance i x=y) : rayUK m B i U (node y-step i,i)=(U (node x,i))⁻¹ := by
  rw [reflect_E]; simp only [ite_true,rayE];
  have hp : revX m B i (node y-step i)= revX m B i (node y)+step i := rev_minus ..
  have he : revX m B i (node y)=node x := by rw [←tiltR,twist_beg i y g,←show x+step i=y from h,add_sub_cancel_right]
  rw [hp,he,add_sub_cancel_right]
lemma end_back {x y:Foot m B} (g : Finis x i) : rayUK m B i U (node x,i)=(U (node x+step i,i))⁻¹ := by
  rw [reflect_E]; simp only [ite_true,rayE]; rw [←tiltR, twist_end i x g, after, add_sub_cancel_right]
lemma begin_energy {x y:Foot m B} (h : advance i x=y) (g : Begin y i) (c) :
    ((pin i) ⊗ₖ 1)*lower m B i (rayUK m B i U) y*star (lower m B i U y)= (grading*lowB i) ⊗ₖ 1 * hop matter (links U) (axisCut m B i c) i x := by
  let z := (node y-step i,i); let V := matter (U (node x,i)); let T := matter (U z); have hP : node y=node x+step i+step i := by rw [←show x+step i=y from h,after]
  rw [lower,lower,if_pos g,if_pos g,begin_back i U g h, inv_inv, hop,seam_bottom i (show x+step i=y from h) g c, one_smul]
  have ht : matter (links U (x,i))=V*T := by unfold V T z; rw [hP, add_sub_cancel_right]; exact map_mul .. 
  simp only [op_star_kron,op_kron_mul, color,ht,map_inv,flatL,Pinlow]
  change ((grading*lowB i)*lowB i) ⊗ₖ (1*V.val*star (star T.val))= ((grading*lowB i)*1) ⊗ₖ (1 * (V*T).val); rw [star_star,one_mul,mul_one, mul_assoc,twol i, one_mul]; rfl
lemma end_energy {x : Foot m B} (g : Finis x i) (c) :
    ((pin i) ⊗ₖ 1)*upper m B i (rayUK m B i U) x*star (upper m B i U x)=star (((grading*lowB i) ⊗ₖ 1) * hop matter (links U) (axisCut m B i c) i x) := by
  let V := matter (U (node x,i)); let T := matter (U (node x+step i,i));
  rw [upper,upper,if_pos g,if_pos g,end_back (y:=x) i U g,hop,seam_top i g c]; simp only [neg_smul,one_smul,map_inv]
  have ht : matter (links U (x,i))=V*T := map_mul ..
  rw [color,op_kron_mul,op_star_kron, op_kron_mul,Pinhigh,neg_mul,mul_assoc grading,flatR,twor,op_kron_neg]; -- check
  rw [mul_neg,op_kron_mul,mul_one,one_mul,one_mul,star_neg,op_star_kron,star_mul,flatL,gradingAdj,flipCl,ht]; congr 2; exact (star_mul ..).symm
lemma zig (f k : Foot m B→Op (SpinIdx × Slot)) : (finger m B i).val*jump (Equiv.refl _) f * star (jump (Equiv.refl _) k)=
    jump (tiltM m B i) (fun x=> (pin i) ⊗ₖ 1 * f (tiltM m B i x)*star (k (tiltM m B i x))) := by
  simp only [seen,jump_mul,jump_star,Equiv.trans_refl,Equiv.refl_symm,Equiv.refl_apply]
lemma entryH c : Tedge m B i*Vplus (axisCut m B i c) (links U) i *Ledge m B i= -bendK i U (enter m B i) := by
  ext x y; let S := posY m B i
  rw [Ledge,Tedge,pinch,plus_block,bendK,enter,enter,zig, Matrix.neg_apply]
  simp only [mem_compl,colony_at, jump_apply]
  by_cases h : tiltM m B i x.1=y.1
  · rw [if_pos h,h]; by_cases t:Begin y.1 i
    · have e : y.1 ∈ posY m B i := begin_pos i y.1 t
      have hx : x.1∉posY m B i := (tiltSide ..).mp (h.symm ▸ e); have he := (slide_begin i hx e).mpr ⟨h,t⟩
      rw [if_pos ⟨hx,e⟩,if_pos he, begin_energy i U he t c]; rfl
    rw [show lower m B i U y.1=0 from if_neg t,star_zero,mul_zero]; simp only [Matrix.zero_apply,neg_zero]; split_ifs with g e <;> (first | rfl | exact (t (((slide_begin i g.1 g.2).mp e).2)).elim)
  rw [if_neg h,neg_zero]; split_ifs with g e <;> first | rfl | exact (h ((slide_begin i g.1 g.2).mp e).1).elim
lemma exitH c : Tedge m B i * star (Vplus (axisCut m B i c) (links U) i) * Ledge m B i= -bendK i U (exitK m B i) := by
  ext x y
  rw [Ledge,Tedge,pinch,plus_block, bendK,exitK,exitK,zig,Matrix.neg_apply]; simp only [mem_compl,colony_at, Matrix.star_apply, jump_apply]
  by_cases h:tiltM m B i x.1=y.1
  · have h':tiltM m B i y.1=x.1 := by rw [←h,tiltBack]
    rw [if_pos h,h]; by_cases t:Finis y.1 i
    · have e := finis_pos i y.1 t; have hx : x.1∉posY m B i := (tiltSide ..).mp (h.symm ▸ e)
      rw [if_pos ⟨hx,e⟩,if_pos ((slide_end i e hx).mpr ⟨h',t⟩),end_energy i U t c]; change star (-_) = -star _; rw [star_neg]; rfl
    rw [show upper m B i U y.1=0 from if_neg t,star_zero,mul_zero]; simp only [Matrix.zero_apply,neg_zero]; split_ifs with g e <;> first | exact (t (((slide_end i g.2 g.1).mp e).2)).elim | simp
  rw [if_neg h, neg_zero]; split_ifs with g e
  · have he := ((slide_end i g.2 g.1).mp e).1; exact (h (by rw [←he, tiltBack])).elim
  · rw [star_zero]
  rfl
end YM.CF.RP
