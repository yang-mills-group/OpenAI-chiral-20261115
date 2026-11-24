/- Adapted cover test from YM.SU5.Thin.Azur.Post (not imported). -/
import Gingham.Ruff.Thimble
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 500000
set_option maxRecDepth 4000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Gingham.Ruff
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Buffered Afterglow Satin Tapestry
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
attribute [local instance] opCStarAlgebra
open Pastry

variable {N:Side}
abbrev ore(n:ℕ)(o:Cover): Finset Cover:= Satin.liner {o} n
lemma ore_mem {x o:Cover}{w:ℕ}: x ∈ ore w o ↔ x-o∈ Lattice.box w:=by
 constructor
 · intro p; obtain ⟨k,hK,p⟩:= mem_biUnion.mp p; obtain ⟨u,e,rfl⟩:= mem_image.mp p; rwa [mem_singleton.mp hK,add_sub_cancel_right]
 exact fun p=> mem_biUnion.mpr ⟨_,mem_singleton_self _,mem_image.mpr ⟨_,p,sub_add_cancel _ _⟩⟩
lemma ore_up {x o:Cover}{w v:ℕ}(p:x∈ore w o)(h:w≤v): x∈ ore v o:=by apply ore_mem.mpr; have ht:=box_test.mp (ore_mem.mp p); refine box_test.mpr ⟨fun i=>?_,fun i=>?_⟩; have g:=ht.1 i; omega; have g:=ht.2 i; omega -- have semis
lemma ore_same (o:Cover) (b:ℕ): Satin.region (ore b o) N=Lattice.halo b {wrap (More N) o}:=by
 apply Subset.antisymm
 · intro k p; obtain ⟨v,L,rfl⟩:= mem_image.mp p
   apply halo_spec.mpr; refine ⟨_,mem_singleton_self _,?_⟩; -- line
   apply (Eq.le ?_).trans (Work.E08.separation_box_add (wrap (More N) o) (ore_mem.mp L)); rw [map_sub,sub_add_cancel]
 intro k p; exact linen_contains _ _ _ ((show region {o} N= _ from Finset.image_singleton ..).symm ▸ p) -- tune
lemma ore_visit (w:Walk)(x:Cover)(z:Cover)(u:ℕ)(p:x∈ore u z):∀ y∈ visits x w,y∈ore (u+w.length) z:=by
 induction w generalizing x u with
 | nil=> exact fun y v=> (List.mem_singleton.mp v).symm ▸ p -- tune
 | cons d w ih=>
   have ht:x+d.vec ∈ ore (u+1) z:=by
      rw [ore_mem] at *; rw [box_test] at *; have hh(i:Axis) : -1 ≤ (d.vec:Cover) i ∧ (d.vec:Cover) i≤1:=by unfold Step.vec; split <;> simp only [Pi.neg_apply, step_apply]<;> split<;> decide
      constructor <;> intro i <;> specialize hh i; · have he:=p.1 i; simp only [Pi.sub_apply,Pi.add_apply] at *; omega
      have he:=p.2 i; simp only [Pi.sub_apply,Pi.add_apply] at *; omega
   intro y Yx; rcases List.mem_cons.mp Yx with r|r; · subst y; exact ore_up p (by omega)
   refine ore_up (ih _ _ ht _ r) (by simp; omega)
def toe_l (x:Face ℤ): Finset Cover:= (visits x.1 (square x.2.val.1 x.2.val.2)).toFinset
lemma toe_now (j:PlaqAxes)(x y:Cover): toe_l (x+y,j)=(toe_l (x,j)).image fun v=> v+y:=by
 unfold toe_l; simp only [square_corners]; ext v; simp [add_right_comm x y, add_right_comm (x+step j.val.1) y] -- align p
abbrev perΦ (N:Side)(v:Face ℤ):Face (Per (More N)) :=(wrap (More N) v.1,v.2)
lemma toeΦ (N:Side)(x:Face ℤ): touched (perΦ N x)= (toe_l x).image (wrap (More N)):=by
 unfold perΦ touched toe_l; simp only [square_corners]; ext i; simp
lemma toe_up (b:ℕ)(o:Cover)(x:Face ℤ)(h:x.1 ∈ ore b o): toe_l x ⊆ ore (b+4) o :=by
 intro j p; exact ore_visit (square x.2.val.1 x.2.val.2) _ _ b h _ (List.mem_toFinset.mp p)
lemma toe_back (b:ℕ)(o:Cover)(x:Face ℤ)(h: ¬Disjoint (toe_l x) (ore b o)): x.1∈ ore (b+4) o:=by
 obtain ⟨i,p,v⟩:= Finset.not_disjoint_iff.mp h; have hx: x.1∈ ore 0 x.1:=(liner_here ..) (mem_singleton_self _); have ht:= toe_up 0 x.1 x hx p
 obtain ⟨hp,hg⟩:= box_test.mp (ore_mem.mp ht); obtain ⟨h,h₀⟩:= box_test.mp (ore_mem.mp v); apply ore_mem.mpr; rw [box_test]; constructor<;> intro i<;> (specialize hp i; specialize hg i; specialize h i; specialize h₀ i; simp only [Pi.sub_apply] at *; omega)
variable (o:Cover)
-- Excluding ties of probes at all, including small
abbrev pingC (b:ℕ)(o:Cover)(Y:BudgetPoint)(U:LinksC):Prop:= ∀ x:Face ℤ, ¬Disjoint (toe_l x) (ore b o) → SU.group.chord (faceValue U x)<Y.threshold
lemma ping_lift (N:Side)(b:ℕ)(P:BudgetPoint)(U:Pane N): pingC b o P (Lifted.onC N U) ↔ pingS P.threshold (halo b {wrap (More N) o}) U:=by
 let t:= wrap (More N)
 have ht(x:Face ℤ): faceValue (Lifted.onC N U) x=faceValue U (perΦ N x):=by unfold Lifted.onC perΦ faceValue; rw [travel_at,add_zero]
 constructor
 · intro H x u
   rw [←ore_same] at u; obtain ⟨y,v,p⟩:= not_disjoint_iff.mp u; obtain ⟨i,e,rfl⟩:= mem_image.mp v; let z:Face ℤ:=(Lattice.lift x.1,x.2); have he:perΦ N z=x:=by simp [perΦ,z]
   rw [←he,toeΦ] at p; obtain ⟨y,g,s⟩:= mem_image.mp p
   let V:Face ℤ:= (z.1+(i-y),z.2)
   have hv:perΦ N V=x:=by rw [←he]; unfold V perΦ; congr 1; rw [map_add,map_sub,s,sub_self,add_zero]
   rw [←hv, ←ht]; apply H; refine not_disjoint_iff.mpr ⟨i,?_,e⟩; unfold V; rw [toe_now]; exact mem_image.mpr ⟨_,g,by abel⟩
 intro p x h; obtain ⟨i,b',v⟩:= not_disjoint_iff.mp h; rw [ht]; refine p (perΦ N x) (not_disjoint_iff.mpr ⟨t i,?_,?_⟩); · rw [←ore_same]; exact mem_image_of_mem _ v
 rw [toeΦ]; exact mem_image_of_mem _ b'

