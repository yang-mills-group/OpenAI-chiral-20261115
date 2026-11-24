import YM.CF.Reflect.Center
import YM.CF.Reflect.Paste

/-! Open slab geometry. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.RP
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant Phase Mir Mir.Trip MeasureTheory Finset
attribute [local instance] opCStarAlgebra
variable {m B : Side} (i : Axis)

def Begin (x : Foot m B) (i) := (x i).val=0 -- specify ?
def Finis (x : Foot m B) (i : Axis) := (x i).val+1=oddSize m B
instance beginD (x:Foot m B) : Decidable (Begin x i) := by unfold Begin; infer_instance
instance finisD (x:Foot m B) : Decidable (Finis x i) := by unfold Finis; infer_instance
lemma begin_pos (x:Foot m B) (h:Begin x i) : x∈posY m B i := mem_filter.mpr ⟨mem_univ _,h.symm ▸ oddP⟩
lemma finis_pos (x:Foot m B) (h:Finis x i) : x∈posY m B i := by apply mem_filter.mpr; exact ⟨mem_univ _,Nat.lt_of_succ_le h.le⟩ -- Finis implies by omega
lemma ax_st (x : Foot m B) : (x+step i : Foot m B) i=x i+1 := by simp
lemma br_a {x y:Foot m B} (g : x+step i=y) : (y i).val=(if (x i).val+1=(CSide m B).val then 0 else (x i).val+1) := by rw [←g,ax_st,vnext]
lemma decisive (x : Foot m B) (e : x∈posY m B i) : x+step i ∉ posY m B i ↔ Finis x i := by
  let n := oddSize m B; have hx : (x i).val<n := (mem_filter.mp e).2; have he : (CSide m B).val=2*n := suff m B
  rw [posY, mem_filter]; simp only [mem_univ,true_and,not_lt]; rw [br_a i rfl]; split <;> unfold Finis <;> omega
lemma decisive2 (x : Foot m B) (e : x∉posY m B i) : x+step i ∈posY m B i ↔ Begin (m:=m) (B:=B) (x+step i) i := by
  let n := oddSize m B; have he := oddP (m:=m) (B:=B); have hx : n ≤ (x i).val := le_of_not_gt (fun l=> e (mem_filter.mpr ⟨mem_univ _,l⟩)); rw [posY,mem_filter,Begin]; simp only [mem_univ,true_and,br_a i (y:=x+step i) rfl]; split <;> omega
lemma twist_beg (x:Foot m B) (h:Begin x i) : tiltM m B i x=x-step i := by
  ext j; by_cases g:i=j
  · subst j; rw [tm,Pi.sub_apply]; simp only [step_apply,ite_true]; rw [(ZMod.val_eq_zero _).mp h,neg_zero]
  rw [ty i x j g]; simp [g,Ne.symm g]
lemma twist_end (x:Foot m B) (h:Finis x i) : tiltM m B i x=x+step i := by
  ext j; by_cases g:i=j
  · subst j; rw [tm,Pi.add_apply,step_apply,if_pos rfl]
    have hk : x i=(axisCut m B i x) i := ZMod.val_injective _ (Nat.succ_inj.mp (h.trans (cval m B i x).symm))
    have ht : 2*((oddSize m B:ℕ):Per (CSide m B))=0 := by rw [← Nat.cast_ofNat,← Nat.cast_mul,show 2*oddSize m B=(CSide m B).val from (suff ..).symm,ZMod.natCast_self]
    rw [hk,cbase,sub_add_cancel]; rw [neg_sub]; rw [two_mul] at ht; have hp := eq_neg_of_add_eq_zero_left ht; abel_nf at *; exact hp.symm
  rw [ty i x j g]; simp [g,Ne.symm g]
lemma slide_begin {x y:Foot m B} (h:x∉posY m B i) (g:y∈posY m B i) : advance i x=y↔ tiltM m B i x=y ∧ Begin y i := by
  constructor
  · intro e; have hk := (decisive2 i x h).mp (show x+step i∈_ from (show x+step i=y from e).symm ▸ g)
    have hp : x+step i=y := e
    rw [hp] at hk; refine ⟨?_,hk⟩; have he : tiltM m B i y=x := by rw [twist_beg i y hk,←hp,add_sub_cancel_right]
    rw [←he,tiltBack]
  intro p; have he : x=y-step i := by rw [←twist_beg i y p.2,←p.1,tiltBack]
  change x+step i=y; rw [he,sub_add_cancel]
lemma slide_end {x y:Foot m B} (h:x∈posY m B i) (g:y∉posY m B i) : advance i x=y ↔ tiltM m B i x=y ∧ Finis x i := by
  constructor
  · intro e; have hk := (decisive i x h).mp (show x+step i ∉ _ from by rw [show x+step i=y from e]; exact g); rw [twist_end i x hk]; exact ⟨e,hk⟩
  intro p; change x+step i=y; rw [←twist_end i x p.2,p.1]
-- reaching gauge plane
lemma link_mid {x:Foot m B} (p:x∈posY m B i) : ∀ j, node x + step j ∈ upField m B i := by
  intro j; by_cases e:i=j
  · subst j; rw [north_mem]; unfold nextPlane; rw [Pi.add_apply,step_apply,if_pos rfl,vnext,val_node]; have ht : (x i).val<oddSize m B := (mem_filter.mp p).2; have he := suff m B; unfold oddSize at ht; split <;> omega
  have hk := (holder i x).mp p; rw [north_mem] at hk ⊢; simpa [e] using hk
lemma back_mid {x:Foot m B} (h:Begin x i) : node x-step i ∈ upField m B i := by
  have he := val_node x i; change _ = 2*(x i).val+1 at he; rw [show (x i).val=0 from h] at he
  have hx : node x i=1 := by rw [←ZMod.natCast_zmod_val (node x i),he]; simp; exact Nat.cast_one
  rw [north_mem]; unfold nextPlane; rw [Pi.sub_apply,hx,step_apply,if_pos rfl,sub_self,ZMod.val_zero]; omega
lemma upward (u v : Pack m B) (c : NorthOf m B i u v) {x y} (a) (h : x∈posY m B i) (g:y∈posY m B i) (e : x+step a = y) : links u.1 (x,a)=links v.1 (x,a) := by
  have hp := (holder i _).mp h; have ht := (holder i _).mp g
  have he := link_mid i h a; rw [links,links]; exact congrArg₂ ((·*·):E→ E→ E) (c.gaugeS _ hp he) (c.gaugeS _ he (show node x+step a+step a ∈ _ by rw [←after,e]; exact ht))
lemma seam_bottom {x y:Foot m B} (h:x+step i=y) (e:Begin y i) c : seam (axisCut m B i c) x i=1 := by
  have hp := cval m B i c
  have hq := br_a i h; unfold Begin at e
  unfold seam; split <;> rename_i l
  · rw [l,hp] at hq; have he : (CSide m B).val=2*oddSize m B := suff m B; split_ifs at hq <;> have he':=oddP (m:=m) (B:=B) <;> omega
  rfl
lemma seam_top {x:Foot m B} (h:Finis x i) c : seam (axisCut m B i c) x i= -1 := by unfold seam; rw [if_pos]; exact ZMod.val_injective _ (Nat.succ_inj.mp (h.trans (cval m B i c).symm))
end YM.CF.RP
