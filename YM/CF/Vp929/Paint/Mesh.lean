import YM.CF.Vp929.Paint.Swift
import YM.Lattice.Subdivision
import YM.Work.E01
set_option autoImplicit false
set_option maxHeartbeats 540000
noncomputable section
namespace YM.CF.VolumeCape
open Finset Function Rooms Lattice Atlas
open scoped Classical
variable {r:ℕ}(n:Side)(s:March)
namespace Mesh
lemma scope_box (x:Cover): x∈box r ↔ Scope r x := by
 unfold Scope Range; simp only [box_test,Pi.zero_apply]; constructor; intro p i; obtain ⟨v,k⟩:= @And.intro _ _ (p.1 i) (p.2 i); omega
 intro u; constructor <;> intro i <;> have h:=u i <;> omega
lemma warp (x:Cover)(p:Scope r x): pdist (wrap n x)≤ r:= Work.E01.pdist_wrap_le ((scope_box x).2 p)
lemma warp_sep(x y:Cover)(p:Range r x y): separation (wrap n x) (wrap n y)≤r:=by unfold separation; rw [← map_sub]; exact warp n _ ((art ..).2 p.symm)
lemma lift_back(x:Site n)(p:pdist x ≤ r):Scope r (Lattice.lift x):=fun i=>by have h:=(component_le x i).trans p; simpa using h
lemma warp_unique(x:Cover)(h:2*r < n.val)(p:Scope r x): Lattice.lift (wrap n x)= x:= lift_eq_iff.mpr ⟨rfl,fun i=>by have g:=p i; simp at g; omega⟩
def grid(n:Side)(s:March) : Equiv.Perm (Site n):= (Signed.actEquiv (R:= Per n) s.step).toEquiv.trans (Equiv.addRight (wrap n s.endpt))
lemma grid_sl (x:Site n): grid n s x=s.step.act x+wrap n s.endpt:= rfl
lemma grid_wrap (x:Cover): grid n s (wrap n x)= wrap n (s.slide x):=by simp [grid_sl,March.slide]
lemma grid_rev (x:Site n): grid n s⁻¹ x=(grid n s).symm x:=by apply (grid n s).injective; rw [Equiv.apply_symm_apply]; nth_rw 1 [← wrap_lift x]; rw [grid_wrap,grid_wrap,s.right,wrap_lift]
lemma grid_mt(s t:March) (x:Site n): grid n (s*t) x= grid n s (grid n t x):=by nth_rw 1 2 [← wrap_lift x]; rw [grid_wrap,grid_wrap,grid_wrap,March.trans]
local notation "N"=> spanR
@[irreducible] def fresh(n:Side):Side:=⟨n.val*N,mul_pos n.property span_pos⟩
abbrev netA (n:Side): Ratio n (fresh n):= ⟨⟨N,span_pos⟩,by unfold fresh; rfl⟩
lemma near_embed(a b:Site n)(h:separation ((netA n).embed a) ((netA n).embed b)≤ N*r): separation a b≤ r:=by
 unfold separation at *; change pdist ((netA n).root a-(netA n).root b) ≤ _ at h; rw [← map_sub, Ratio.root_embed] at h; apply Finset.sup_le (s:=Finset.univ) (f:=fun i:Axis=> (Lattice.lift (a-b) i).natAbs)
 intro i _; let E:= (component_le _ i).trans h; simp [Ratio.lift_embed (netA n), Int.natAbs_mul] at E; exact Nat.le_of_mul_le_mul_left E span_pos
lemma wrapped(a:Cover):(netA n).embed (wrap n a)=wrap (fresh n) (N • a):= Ratio.embed_wrap _ _
abbrev Dye(n:Side)(r:ℕ):=(Jux r → Site n → Fin 4) × (Site (fresh n)→Arm)
variable (a:Dye n r)
def scene(a:Dye n r): Scene r:=⟨fun d v=>a.1 d (wrap n v),fun v=>a.2 (wrap (fresh n) v)⟩
def cloth(a:Dye n r)(v:Site n):Patch r := (fun i x=>a.1 i (v+wrap n x.val),fun i=> a.2 ((netA n).embed v + wrap (fresh n) i.val))
theorem woven(v:Cover):survey (scene n a) v=cloth n a (wrap n v):= by simp only [map_add,survey, cloth,scene,Mesh.wrapped]
abbrev Mark(r:ℕ):= Fin (height r)×Arm
def marked(a:Dye n r)(v:Site n): Mark r:= (code (cloth n a v), a.2 ((netA n).embed v))
lemma marked_cover(v:Cover) : marked n a (wrap n v)=(code (survey (scene n a) v), (scene n a).flag (N • v)):=by rw [woven]; simp only [marked,scene,wrapped]
def Follows (x y:Site n→Mark r)(s:March) :Prop:=∀i:Site n,(y (grid n s i)).1=(x i).1∧ (y (grid n s i)).2= star s*(x i).2
lemma reeling(d:Jux r) : wrap n (wr s.step r d).val.val=s.step.act (wrap n d.val.val):=by apply Eq.symm; exact wrap_signed ..
def billow : Equiv.Perm (Dye n r):= Equiv.prodCongr (((Equiv.arrowCongr (wr s.step r).symm (Equiv.refl _))).trans (Equiv.arrowCongr (Equiv.refl _) (Equiv.arrowCongr (grid n s).symm (Equiv.refl _)))) (Equiv.arrowCongr (grid (fresh n) (rise s)).symm (Equiv.mulLeft (star s)⁻¹))
lemma storm(d:Jux r)(i:Site n):(billow n s a).1 d i=a.1 (wr s.step r d) (grid n s i):= rfl
lemma storming(i:Site (fresh n)): (billow n s a).2 i=(star s)⁻¹*a.2 (grid (fresh n) (rise s) i):= rfl
protected lemma Flow : Atlas.Flow (scene n (billow n s a)) (scene n a) s:=by
 constructor <;> intro i; intro v; unfold scene; dsimp; rw [storm,grid_wrap]; change a.2 _=star s*(billow n s a).2 _; rw [storming,grid_wrap,mul_inv_cancel_left]
lemma followers: Follows n (marked n (billow n s a)) (marked n a) s := by
 intro i; obtain ⟨x,e⟩:= (show ∃x:Cover,wrap n x=i from ⟨_,wrap_lift i⟩); rw [←e, grid_wrap, marked_cover,marked_cover]; refine ⟨(meetsM _ _ _ _ (Mesh.Flow n s a)).symm,?_⟩
 change (scene n a).flag _=_; rw [← rs]; exact (Mesh.Flow n s a).2 _
end Mesh
end YM.CF.VolumeCape
