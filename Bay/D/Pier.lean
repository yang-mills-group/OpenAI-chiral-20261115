import Bay.Porch
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

namespace D
open Buffered Lifted
-- Unwrapped masks and gathering. Pavilion, through voyage_local, adapted
-- from project/YM/SU5/Silk/Span/Rapt.
def pavilion (X:Cover)(r:ℕ):Finset Cover := (Lattice.box r).image (·+X)
lemma pav_v (X Y:Cover)(r:ℕ): Y∈ pavilion X r ↔ ∀ i:Axis, X i - r ≤ Y i ∧ Y i ≤ X i + r:=by
 constructor
 · rintro p; obtain ⟨v,u,rfl⟩:= mem_image.mp p
   intro i; have ht:=(box_test.mp u).1 i; have hp:=(box_test.mp u).2 i
   change X i- r ≤ v i + X i ∧ v i + X i ≤ X i + r; omega
 intro p; refine mem_image.mpr ⟨Y-X,box_test.mpr ⟨fun i=> ?_,fun i=> ?_⟩,sub_add_cancel ..⟩
 all_goals specialize p i; simp only [Pi.sub_apply]; omega
lemma walk_pav (x y:Cover)(w:Walk)(h:y∈visits x w):y∈ pavilion x w.length:=by
 have he:= Extra.Iteration.along_size x y w h; rw [pav_v]; intro i
 have hp: (y i-x i).natAbs≤ w.length := (single_le_sum (s:=univ) (f:=fun k:Axis=>(y k-x k).natAbs) (fun j _=> Nat.zero_le _) (mem_univ i)).trans he; omega
lemma span_walk (x o u:Cover)(r:ℕ)(w:Walk)(p:x∈ pavilion o r)(t:u∈ visits x w):u ∈ pavilion o (r+w.length):=by rw [pav_v]; intro i; have hp:=(pav_v ..).1 (walk_pav x u w t) i; have ht:=(pav_v ..).1 p i; omega
lemma wrap_pav (N:Side)(X:Cover)(r:ℕ): (pavilion X r).image (wrap N)= halo r {wrap N X}:=by
 ext x; rw [mem_image, halo_spec]; constructor
 · rintro ⟨y,h,rfl⟩; obtain ⟨y,v,rfl⟩:= mem_image.mp h; refine ⟨_,mem_singleton_self _,?_⟩; rw [map_add,separation_comm,separation,add_sub_cancel_right]; exact Work.E01.pdist_wrap_le v
 rintro ⟨y,p,u⟩; rw [mem_singleton.mp p,separation_comm] at u; let z:=wrap N X; let a:= Lattice.lift (x-z)
 have ht(i):-(r:ℤ) ≤ a i ∧ a i ≤ r:=by have hx:(a i).natAbs ≤ r:=(component_le _ i).trans u; omega
 exact ⟨a+X,mem_image_of_mem _ (box_test.mpr ⟨fun i=>(ht i).1,fun i=>(ht i).2⟩), by unfold a; rw [map_add,Lattice.wrap_lift]; exact sub_add_cancel ..⟩
lemma tours_paid (x:Cover)(w:Walk)(n:Side): (visits x w).map (wrap n)=visits (wrap n x) w:=by induction w generalizing x with|nil=>simp [visits]|cons s w p=>simp [visits,p,map_add,wrap_vec]
lemma stroll (x v:Cover)(w:Walk):visits (x+v) w=(visits x w).map (· + v):=by induction w generalizing x with|nil=>simp [visits]|cons i w ih=> simp only [visits,List.map_cons]; congr 1; rw [add_right_comm,ih]

-- compact receipts for all incident squares in the unwrapped mesh
def visa (p:Face ℤ):Finset Cover := (visits p.1 (square p.2.val.1 p.2.val.2)).toFinset
def voyageD (r:ℕ)(X: Cover):Finset (Face ℤ) := ((pavilion X (r+4)) ×ˢ (univ:Finset PlaqAxes)).filter (fun p=> ¬ Disjoint (pavilion X r) (visa p))
lemma voy{r:ℕ} (X:Cover)(p:Face ℤ) : p∈ voyageD r X ↔ ¬ Disjoint (pavilion X r) (visa p):=by
 let P:=pavilion X r; let T:=visa p; let U:=pavilion X (r+4)
 unfold voyageD; rw [mem_filter]; constructor; exact And.right
 intro y; refine ⟨mem_product.mpr ?_,y⟩; change ¬Disjoint P T at y
 obtain ⟨i,h,t⟩:=not_disjoint_iff.mp y; change p.1∈U ∧ p.2∈(univ:Finset PlaqAxes); refine ⟨(pav_v ..).2 fun a=> ?_,mem_univ _⟩
 have hp:=(pav_v ..).1 h a
 have hx:i∈pavilion p.1 4:= walk_pav p.1 i (square p.2.val.1 p.2.val.2) (List.mem_toFinset.mp t)
 have hv:=(pav_v ..).1 hx a; omega
lemma voy_sites {r:ℕ}(X:Cover)(p:Face ℤ)(h:p∈ voyageD r X): visa p ⊆ pavilion X (r+4+4):= fun y hy=> span_walk p.1 X y (r+4) (square p.2.val.1 p.2.val.2) (show p.1∈ pavilion X (r+4) from (mem_product.mp (mem_filter.mp h).1).1) (List.mem_toFinset.mp hy)
lemma visa_wrap (p:Face ℤ)(n:Side): (visa p).image (wrap n)=touched ((wrap n) p.1,p.2):=by unfold visa touched; rw [← tours_paid]; ext x; simp
lemma stamp_wrap (r:ℕ)(X:Cover)(n:Side)(p:Face (Per n)): (∃ i∈ voyageD r X, (wrap n i.1,i.2)=p) ↔ ¬ Disjoint (halo r {wrap n X}) (touched p):=by
 constructor
 · rintro ⟨i,h,rfl⟩; have hd:= (voy (r:=r) X i).1 h; let P:=pavilion X r; let Vx:=visa i; change ¬Disjoint P Vx at hd
   obtain ⟨x,u,v⟩:= not_disjoint_iff.mp hd; rw [←visa_wrap i,←wrap_pav]; exact not_disjoint_iff.mpr ⟨wrap n x,mem_image_of_mem _ u, mem_image_of_mem _ v⟩
 rw [← wrap_pav]; intro g; obtain ⟨x,h,t⟩:=not_disjoint_iff.mp g; obtain ⟨x,u,rfl⟩:=mem_image.mp h
 let y:=Lattice.lift p.1; have hp: (wrap n y,p.2)=p:=Prod.ext (wrap_lift _) rfl
 let P:Face ℤ:= (y,p.2); have ht:wrap n x∈ (visa P).image (wrap n):=by rw [visa_wrap,show (wrap n P.1,P.2)=p from hp]; exact t
 obtain ⟨v,w,r0⟩:=mem_image.mp ht
 let L:Face ℤ := (y+(x-v),p.2); have hr:wrap n (x-v)= 0 := by rw [map_sub,r0,sub_self]
 refine ⟨L,(voy (r:=r) X L).2 ?_,?_⟩
 · let P:=pavilion X r; let Vx:=visa L; change ¬ Disjoint P Vx; apply Finset.not_disjoint_iff.mpr; refine ⟨x,u,?_⟩
   change x∈ (visits (y+(x-v)) (square _ _)).toFinset; rw [stroll,List.mem_toFinset]; exact List.mem_map.mpr ⟨v,List.mem_toFinset.mp w,by change v+(x-v)=x; abel⟩
 unfold L; simp only [map_add,hr,add_zero]; exact hp

def landingC (r:ℕ)(x: Cover)(T:ℝ)(U:LinksC):Prop:=∀ i∈ voyageD r x,SU.group.chord (faceValue U i)<T
lemma land_wrap (r:ℕ)(n:Side)(U:Pane n)(x:Cover)(T:ℝ): landingC r x T (onC _ U)↔ pingS T (halo r {wrap (More n) x}) U:=by
 let v:=wrap (More n)
 have hp(i:Face ℤ) : faceValue (onC _ U) i=faceValue U (v i.1,i.2):=by unfold onC faceValue; rw [travel_at]; simp [v]
 constructor
 · intro t p h; obtain ⟨p,u,rfl⟩:= (stamp_wrap r x (More n) p).2 h; rw [← (hp p)]; apply t p; exact u
 intro t p h; rw [hp]; exact t _ ((stamp_wrap ..).1 ⟨p,h,rfl⟩)

lemma voyage_local {r:ℕ}(p:Cover)(T:ℝ)(x y:LinksC)(h:Agrees (pavilion p (r+4+4)) x y):landingC r p T x↔ landingC r p T y:=by
 unfold landingC; apply forall_congr'; intro a; apply forall_congr'; intro k
 have hx:faceValue x a=faceValue y a:= travel_local _ _ _ _ fun i v w=>h i (voy_sites _ a k (List.mem_toFinset.mpr v)) (voy_sites _ a k (List.mem_toFinset.mpr w)); rw [hx]
