import YM.CF.DPress.FD.Law.Direct
import YM.Lattice.Box
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.DPress.FD
open Function Filter Lattice Finset Cash
open scoped Topology BigOperators ENNReal NNReal Classical
variable {n:Side} {r k:ℕ}
abbrev Window(r:ℕ):= (box r).erase 0
abbrev Bifold(r:ℕ):=↥(Window r)
namespace Bifold
variable (v:Bifold r) (m:2*r< n.val)
include m in
lemma pin : lift (wrap n v.val)=v.val:=lift_eq_iff.mpr ⟨rfl,fun i=> by obtain ⟨p,h⟩:= box_test.mp (mem_erase.mp v.property).2; have hz:= p i; have he:=h i; omega⟩
def jog (n:Side)(v:Bifold r): Equiv.Perm (Site n):= Equiv.addRight (wrap n v.val)
include m
lemma stepP(i:Site n): jog n v i ≠ i := by
 intro t; have ht:wrap n v.val=0:= add_eq_left.mp t; have hf:= pin v m; rw [ht] at hf; apply (mem_erase.mp v.property).1; rw [←hf]; simp [Lattice.lift, funext_iff]
lemma stepR(i:Site n):separation i (jog n v i)≤r:=by
 rw [separation_comm]; unfold separation jog; change pdist (i+wrap n v.val-i)≤_; rw [add_sub_cancel_left]; unfold pdist; apply Finset.sup_le; intro j _; rw [pin v m]; obtain ⟨p,h⟩:= box_test.mp (mem_erase.mp v.property).2; have hz:= p j; have hf:= h j; omega
lemma event (i j:Site n)(p:i≠j)(h:separation i j≤r) :∃ v:Bifold r, j=jog n v i:=by
 rw [separation_comm] at h; let a:= j-i; let v:= lift a; have hv: v ∈ Window r:=by
    refine mem_erase.mpr ⟨?_,box_test.mpr ?_⟩; · intro e; apply p; have hq:=congrArg (wrap n) e; unfold v a at hq; rw [wrap_lift,map_zero] at hq; exact (sub_eq_zero.mp hq).symm
    have he(i): (v i).natAbs≤r:=(component_le ..).trans h; constructor<;> intro i <;> have hx:= he i <;> omega
 refine ⟨⟨v,hv⟩,?_⟩; change j = i + wrap n v; unfold v; rw [wrap_lift]; unfold a; abel
omit m
-- Motion and colors. signed action only; equiv under full affine (incl Shelf sweeps). orientation preserving for each displacement index.
lemma pole (s:Signed)(v:Bifold r) : s.act v.val∈ Window r:=by
 let e:=mem_erase.mp v.property; apply mem_erase.mpr; refine ⟨fun i=>e.1 (?_),?_⟩; · exact (s.actEquiv.injective (i.trans ((show (s.actEquiv (0:Cover))=0 from map_zero (s.actEquiv)).symm)))
 rw [←box_covariant r s]; exact mem_image_of_mem _ e.2
def frame (s:Signed):Equiv.Perm (Bifold r):=⟨fun i=>⟨s.act i.val,pole s i⟩,fun i=>⟨s⁻¹.act i.val,pole _ i⟩,fun i=>Subtype.ext (s.inv_act _),fun i=>Subtype.ext (s.act_inv _)⟩
def aura (s:Signed) (x:Site n):Equiv.Perm (Site n):= (s.actEquiv.toEquiv).trans (Equiv.addRight x)
lemma theme (s:Signed)(x:Site n)(v:Bifold r):Semiconj (aura s x) (jog n v) (jog n (frame s v)):=by
 intro i; change s.act (i+wrap n v.val)+x=s.act i+x+wrap n (s.act v.val); rw [Signed.act_add,wrap_signed]; abel
end Bifold
end YM.CF.DPress.FD
