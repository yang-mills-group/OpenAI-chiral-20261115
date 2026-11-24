import YM.CF.Fock.Compressed

/-! Top volume transforms by the determinant. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
open Finset
attribute [local instance] opCStarAlgebra
variable {n : Type*} [LinearOrder n] [Fintype n]
open Function
def bindC (f : n → (n→ℂ)) : Op n := (Matrix.of f)ᵀ
lemma col_read (f : n → n → ℂ) (i : n) : acts (bindC f) (basisKet i)=WithLp.toLp 2 (f i) := by
  apply PiLp.ext; intro j; rw [basis_act]; rfl
lemma col_same (f g : n → n → ℂ) (s : Finset n) (h : ∀ i∈s, f i=g i) : wedge (bindC f) s=wedge (bindC g) s := by
  induction s using Finset.induction_on with
  | empty => simp only [wedge_empty]
  | @insert i s e ih => rw [wedge_any _ _ _ e,wedge_any _ _ _ e,col_read,col_read,h i (by simp),ih (fun j hj=>h _ (mem_insert_of_mem hj))]
lemma col_adj (f : n → n → ℂ) (i : n) (p : n → ℂ) :
    wedge (bindC (update f i p)) univ=parity i (univ.erase i) • acts (create (WithLp.toLp 2 p)) (wedge (bindC f) (univ.erase i)) := by
  nth_rw 1 [← insert_erase (mem_univ i)]; rw [wedge_any _ _ _ (notMem_erase i univ),col_read,update_self,col_same _ f _ (fun j hj=>update_of_ne (mem_erase.mp hj).1 ..)]
def colVol : (n → ℂ) [⋀^n]→ₗ[ℂ] ℂ where
  toMultilinearMap := MultilinearMap.mk' (fun f => (wedge (bindC f) univ).ofLp univ)
    (fun f i x y=> by rw [col_adj,col_adj,col_adj,WithLp.toLp_add,map_add,act_add]; simp only [smul_add,WithLp.ofLp_add, Pi.add_apply])
    (fun f i q x=> by rw [col_adj,col_adj,WithLp.toLp_smul,map_smul,act_smul,smul_comm]; rfl)
  map_eq_zero_of_eq' v i j h g := by
    let s := @univ n _; let e := s.erase i
    have hj : j∈e := mem_erase.mpr ⟨g.symm,mem_univ j⟩
    suffices hx : wedge (bindC v) s=0 by change (wedge _ s).ofLp s=_; rw [hx]; rfl
    rw [←insert_erase (show i∈s from mem_univ i), wedge_any _ _ _ (by simp)]; change _ • acts _ (wedge _ e)=_
    rw [← insert_erase hj,wedge_any _ _ _ (by simp), col_read,col_read,h,map_smul,←act_mul,create_sq,act_zero,smul_zero,smul_zero]
lemma volume (A : Op n) : quant A univ univ=A.det := by
  let f := colVol (n:=n); let e := Pi.basisFun ℂ n
  have he : bindC e=1 := by
    ext i j; simp only [bindC,e,Matrix.one_apply,Matrix.transpose_apply,Pi.basisFun_apply,Matrix.of_apply]; rw [Pi.single_apply]
  have hu : f e=1 := by change (wedge (bindC _) _).ofLp _=1; rw [he,←quant_column,quant_one,act_one,basis_apply,if_pos rfl]
  have hx : quant A univ univ=f (fun i j=>A j i) := rfl
  rw [hx, f.eq_smul_basis_det e,hu,one_smul,Module.Basis.det_apply]; congr 1

def padded (s : Finset n) (A : Op n) := cutM s*A*cutM s+(1-cutM s)
lemma padded_col (s : Finset n) (A : Op n) (i : n) (e : i∈s) : acts (padded s A) (basisKet i)=acts (cutM s) (acts A (basisKet i)) := by
  unfold padded; rw [act_add,act_mul,act_sub,act_one,cut_basis,if_pos e,sub_self,add_zero,act_mul]
lemma padded_extra (s : Finset n) (A : Op n) (i : n) (e : i∉s) : acts (padded s A) (basisKet i)=basisKet i := by
  unfold padded; rw [act_add,act_mul,act_sub,act_one,cut_basis,if_neg e,sub_zero,map_zero,zero_add]
lemma padded_quant (s : Finset n) (A : Op n) : quant (padded s A) s s=quant A s s := by
  have he : ∀ t ⊆ s, wedge (padded s A) t=wedge (cutM s*A) t := by
    intro t h
    induction t using Finset.induction_on with
    | empty => simp [wedge_empty]
    | @insert i t e ih => rw [wedge_any _ _ _ e,wedge_any _ _ _ e,padded_col s A i (h (by simp)),act_mul,ih ((subset_insert _ _).trans h)]
  change (wedge _ _).ofLp _=_; rw [he s (subset_refl _),←quant_column,quant_mul,act_mul,quantCut,cut_apply]
  simp
lemma extra_diag (s t : Finset n) (A : Op n) (i : n) (e : i∉s) (g : i∉t) : quant (padded s A) (insert i t) (insert i t)=quant (padded s A) t t := by
  change (wedge _ _).ofLp _=_
  rw [wedge_any _ _ _ g,padded_extra _ _ _ e,create_put,WithLp.ofLp_smul,Pi.smul_apply,smul_eq_mul,put_row,
    if_pos (mem_insert_self ..),erase_insert g,parity_hi _ _ _ le_rfl,←mul_assoc,parity_sq,one_mul]; rfl
lemma principal (A : Op n) (s : Finset n) : quant A s s = (padded s A).det := by
  rw [←volume,←padded_quant]; symm
  suffices H : ∀ t : Finset n, Disjoint t s → quant (padded s A) (t∪s) (t∪s)=quant (padded s A) s s by
    simpa [show sᶜ∪s=univ by ext; simp; tauto] using H sᶜ (disjoint_compl_left)
  intro t ht
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t e ih => rw [insert_union,extra_diag _ _ _ _ (show i∉s from fun g=>disjoint_left.mp ht (mem_insert_self ..) g) (fun h=>(mem_union.mp h).elim e (disjoint_left.mp ht (mem_insert_self ..))), ih (Disjoint.mono_left (subset_insert _ _) ht)]
end YM.CF.Fock
