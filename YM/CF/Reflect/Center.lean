import YM.CF.Reflect.Edges
import YM.CF.Fock.Reap

/-! Fermion sectors. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.RP
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Kronecker
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant Phase Mir Mir.Trip MeasureTheory Finset
attribute [local instance] opCStarAlgebra
variable {N m B : Side}
def oddSize (m B : Side) := m.val * B.val
lemma oddP : 0<oddSize m B := Nat.mul_pos m.property B.property
abbrev Foot (m B : Side) := Site (CSide m B)
lemma val_node (x : Site N) (i : Axis) : (node x i).val=2*(x i).val+1 := by
  let k (i:Axis) : ℤ := (x i).val; have hx : x=wrap N k := by funext i; unfold k; rw [wrap_here, Int.cast_natCast,ZMod.natCast_zmod_val]
  have hm : node x i=(((2*(x i).val+1:ℕ)):Per (More N)) := by
    unfold node; nth_rw 1 [Ratio.root_embed,hx]; rw [Ratio.embed_wrap];
    change wrap (More N) (2 • k) i+1=_; rw [wrap_here]; unfold k; push_cast; simp
  rw [hm,ZMod.val_natCast_of_lt]; have ht := ZMod.val_lt (x i); rw [natM]; omega

def posY (m B : Side) (i : Axis) := (univ: Finset (Foot m B)).filter fun x=>(x i).val< oddSize m B
lemma holder (i) (x : Foot m B) : x∈posY m B i ↔ node x ∈ upField m B i := by
  rw [posY,mem_filter,north_mem]; unfold nextPlane; rw [val_node]; have ht : (CSide m B).val=2*oddSize m B := suff m B; simp only [mem_univ,true_and]; omega
lemma no_fence (x:Foot m B) (i) : node x∈downField m B i ↔ x∉posY m B i := by
  rw [holder,north_mem,south_mem]; unfold nextPlane backPlane; rw [val_node]; have ht := suff m B; omega
abbrev tiltM (m B : Side) (i) := fperm m B (slideM m i)
@[simp] lemma tiltR (i) (x) : node (tiltM m B i x)=revX m B i (node x) := track ..
@[simp] lemma tiltBack (i) (x) : tiltM m B i (tiltM m B i x)=x := by apply needle; rw [tiltR,tiltR,rev_back]
lemma tiltSide i (x) : tiltM m B i x∈posY m B i ↔ x∉posY m B i := by rw [holder,tiltR,return_north,no_fence]
lemma fpos (i) (x) : tiltM m B i x=(Signed.mirror i).act x-step i := by
  unfold tiltM; change _ = _; unfold fperm; dsimp only [motion,fermShift,affine,Equiv.coe_fn_mk]
  rw [show (slideM m i).move=0 from rfl,map_zero]; unfold ankle; simp only [zero_add]
  rw [sub_eq_add_neg]; congr 1; funext j; rw [slideM]; simp only [Pi.neg_apply,step_apply]; by_cases e:j=i; subst j; simp; simp [e,Ne.symm e]
lemma tm (i) (x) : tiltM m B i x i= -x i-1 := by rw [fpos,Pi.sub_apply]; simp [Signed.act,Signed.mirror]
lemma ty (i) (x j) (g : i≠j) : tiltM m B i x j=x j := by rw [fpos,Pi.sub_apply]; simp [Signed.act,Signed.mirror,g,Ne.symm g]

-- cut: positive hop at d_i= oddSize-1 seam

def axisCut (m B : Side) (i : Axis) (c : Foot m B) := update c i (↑(oddSize m B)-1)
lemma cbase (m B : Side) i c : (axisCut m B i c) i= ↑(oddSize m B)-1 := by simp [axisCut]
lemma cval (m B : Side) i c : ((axisCut m B i c) i).val+1=oddSize m B := by
  let n := oddSize m B; have hp : 0<n := oddP; have he : (CSide m B).val=2*n := suff m B
  rw [cbase,show ↑(oddSize m B)- (1:Per (CSide m B))=↑(oddSize m B-1) from by rw [Nat.cast_sub hp]; simp [n],ZMod.val_natCast_of_lt] <;> change _ <;> omega -- tune
lemma seam_shift (m B : Side) (i) (p : Foot m B) : far B (slideM m i) (axisCut m B i p)=axisCut m B i p := by
  let n := oddSize m B; have he := suff m B
  have ht : 2*(↑n:Per (CSide m B))=0 := by rw [← Nat.cast_ofNat, ← Nat.cast_mul, show 2*n=_ from he.symm, ZMod.natCast_self]
  funext j
  rw [far]; by_cases h:i=j
  · subst j; rw [if_pos ((slide_glare ..).mpr rfl),cbase]
    unfold fermShift; rw [show (slideM m i).move=0 from rfl,map_zero,zero_add]; unfold ankle; rw [if_pos ((slide_glare ..).mpr rfl)]
    rw [two_mul] at ht; change -1-1-(↑n-1)= (n:Per _)-1; nth_rw 1 [←zero_add (-1),←ht]; abel
  rw [if_neg (fun k=>h ((slide_glare ..).mp k))]; unfold fermShift; rw [show (slideM m i).move=0 from rfl,map_zero,zero_add]; unfold ankle; rw [if_neg (fun k=>h ((slide_glare ..).mp k)),sub_zero] -- zero-sub?? -1-c only true branch tangent c-shift

def colony (m B : Side) (i : Axis) : Finset (Model (CSide m B)) := univ.filter fun x=> x.1 ∈ posY m B i
lemma colony_at (x : Model (CSide m B)) (i) : x∈colony m B i↔x.1∈posY m B i := by simp [colony]
abbrev Xmind (m B : Side) := Model (CSide m B)
def finger (m B : Side) (i : Axis) : UNI (Xmind m B) := pinTrip (slideM m i) i B
-- star spin flip relative conjugation
lemma seen (m B i) : (finger m B i).val= jump (tiltM m B i) (fun _=> pin i ⊗ₖ (1:Op Slot)) := by
  change (jump (Equiv.refl _) (fun _=> pin i ⊗ₖ (1:Op Slot))) * jump (tiltM m B i) (fun _=>1)= _; rw [jump_mul]; simp
lemma straight2 (m B i) : (finger m B i).val*(finger m B i).val= -1 := by
  rw [seen,jump_mul, show (tiltM m B i).trans (tiltM m B i)=Equiv.refl _ by ext x : 1; exact tiltBack ..]
  simp_rw [op_kron_mul,pin_square,one_mul,op_kron_neg, Matrix.one_kronecker_one]; rw [jump_neg, jump_id]
lemma movedCol (m B i) : twist (finger m B i) (cutM (colony m B i))=cutM (colony m B i)ᶜ := by
  apply twist_comm; rw [seen]; ext x y; unfold cutM; rw [Matrix.mul_diagonal, Matrix.diagonal_mul]; by_cases h : tiltM m B i x.1=y.1
  · have ht : y∈colony m B i↔x∈(colony m B i)ᶜ := by rw [mem_compl,colony_at,colony_at, ←h, tiltSide]
    split_ifs <;> first | tauto | simp
  rw [jump_apply, if_neg h]; simp
lemma reflected_H (m B i) (U : Skin m B) (c) : twist (finger m B i) (wiel m B (axisCut m B i c) U) = -wiel m B (axisCut m B i c) (rayUK m B i U) := by
  unfold finger rayUK; rw [seaH (slideM m i),seam_shift]; intro; rw [slide_glare,eq_comm]
end YM.CF.RP
