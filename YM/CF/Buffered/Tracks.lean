import YM.CF.Buffered.Elysium
/-!
# Slice arbitrary among four axes. Counting seam variables along crossing.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 22000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 440000
noncomputable section
namespace YM.CF.Buffered.Region
open Function Filter NormedSpace SU Lat Lattice Cube Finset Mir Mir.Trip Phase RP MeasureTheory Roost Rails Mil RG WilsonStartup Spark Nova Fock Gloss Scroll Push.SectorMeasure Ordered Cin Stripe Tile
open Installed (point)
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder Fin.NatCast
attribute [local instance] opCStarAlgebra
variable {m v p B:Side}{δ:Axis→Side}

abbrev Off (i:Axis) := {j:Axis//j≠i}
abbrev TStem (i:Axis):= Off i→Side
abbrev Car {i:Axis}(ζ:TStem i):= (j:Off i)→Fin (ζ j).val
variable {n:Side} {i:Axis}{ζ:TStem i}

structure Traversed (ζ:TStem i)(δ:Axis→Side)(n:Side):Prop where
 own : n=δ i
 others (j:Off i): ζ j=δ j.val

def away (i:Axis)(δ:Axis→Side): TStem i:= fun j=>δ j.val
def Taxi (u:Car ζ)(j:Off i): Car ζ:= u+Pi.single j 1
def tint (u:Car ζ): Finset Axis:= (univ.filter (fun j=> (u j).val%2=1)).map (Function.Embedding.subtype _)
def endC (u:Car ζ)(j:Off i): Bool:= decide ((u j).val+1=(ζ j).val)
def tip (u:Car ζ)(j:Off i):ℝ:= if endC u j then -1 else 1
private lemma franco (u: Fin n.val)(e:n=m): Fin.cast (show n.val=m.val from congrArg Subtype.val e) (u+1)=(Fin.cast (show n.val=m.val from congrArg Subtype.val e) u)+1:=by subst m; rfl
variable (V:Traversed ζ δ n)
namespace Traversed
theorem self (i)(δ) : Traversed (away i δ) δ (δ i):=⟨rfl,fun _=>rfl⟩
def loc (V:Traversed ζ δ n)(t:Fin n.val)(p:Car ζ): Rail δ:= fun j=>if h:j=i then Fin.cast (h ▸ congrArg Subtype.val V.own) t else Fin.cast (congrArg Subtype.val (V.others ⟨j,h⟩)) (p ⟨j,h⟩)
lemma loc_v (t:Fin n.val)(p:Car ζ): loc V t p i=Fin.cast (congrArg Subtype.val V.own) t:= dif_pos rfl
lemma loc_h (t:Fin n.val)(p:Car ζ)(j:Off i): loc V t p j.val=Fin.cast (congrArg Subtype.val (V.others j)) (p j):= dif_neg j.property

def lead (r:Rail δ): Fin n.val := Fin.cast (congrArg Subtype.val V.own.symm) (r i) -- V autoImplicit def issue not result
#print lead
def tail (r:Rail δ): Car ζ:= fun j=> Fin.cast (congrArg Subtype.val (V.others j).symm) (r j.val)
lemma lead_loc (t:Fin n.val)(p:Car ζ): lead V (loc V t p)=t:=by unfold lead; rw [loc_v]; rfl
lemma tail_loc (t:Fin n.val)(p:Car ζ): tail V (loc V t p)=p:=by funext j; unfold tail; rw [loc_h]; rfl
lemma parts (r:Rail δ): loc V (lead V r) (tail V r)=r:=by
 funext j; by_cases e:j=i
 · -- loc opaque
  subst j; rw [loc_v]; rfl
 · rw [show loc V (lead V r) (tail V r) j=_ from loc_h V _ _ ⟨j,e⟩]; rfl

def click : Fin n.val × Car ζ≃ Rail δ:=⟨fun p=>loc V p.1 p.2,fun r=>(lead V r,tail V r),fun _=>Prod.ext (lead_loc ..) (tail_loc ..),parts V⟩
lemma verge (t:Fin n.val)(u:Car ζ) : Region.next i (loc V t u)= loc V (t+1) u:=by
 funext j; by_cases e:j=i; swap; · rw [next_at _ i e,show loc V t u j=_ from loc_h V t u ⟨j,e⟩, show loc V (t+1) u j=_ from loc_h V _ _ ⟨j,e⟩] -- tune
 subst j; rw [next_rail,loc_v,loc_v]; exact (franco t V.own).symm
lemma taxi (t:Fin n.val)(u:Car ζ)(j:Off i): Region.next j.val (loc V t u)=loc V t (Taxi u j):=by
 funext k; by_cases e:k=i; subst k; rw [loc_v,next_at _ _ j.property.symm,loc_v]
 let z:Off i:=⟨k,e⟩; change Region.next j.val _ z.val= loc _ t _ z.val; by_cases h:z=j
 · rw [h,next_rail,loc_h,loc_h,show Taxi u j j=u j+1 from (by simp [Taxi])]; exact (franco (u j) (V.others j)).symm
 rw [next_at _ _ (Subtype.val_injective.ne h),loc_h, loc_h,show Taxi u j z=u z from (by simp [Taxi,h])]
lemma ends_tip (t:Fin n.val)(u:Car ζ)(j:Off i): chordF (loc V t u) j.val= tip u j:= by
 unfold chordF tip endsAt endC; simp only [loc_h,Fin.val_cast,decide_eq_true_eq]; have hp:=V.others j; -- can't rewrite because Fin. use congr
 rw [← hp]

lemma last_tip (t:Fin n.val)(u:Car ζ) : chordF (loc V t u) i= if t.val+1=n.val then -1 else 1:=by unfold chordF endsAt; simp only [loc_v,Fin.val_cast]; rw [← V.own] -- tune
include V in
lemma many_pal (h:Landing δ)(t:Fin n.val)(u:Car ζ)(j:Off i) : Taxi u j ≠ u:= fun v=> next_away (loc V t u) _ h ((taxi ..).trans (congrArg _ v)) -- tune
lemma tint_off (u:Car ζ): i ∉ tint u:=by intro H; obtain ⟨j,y,w⟩:= mem_map.mp H; exact j.property w
lemma pigment (t:Fin n.val)(p: Car ζ): Region.shade (loc V t p) = if t.val%2=1 then insert i (tint p) else tint p:=by
 have hp (t:Car ζ)(j:Axis) (h:j≠i) : j∈tint t↔ (t ⟨j,h⟩).val%2=1:=by simp [tint, Off, h]; -- tune exist
 ext j; by_cases h:j=i; subst j; split_ifs <;> simp_all [Region.shade,loc_v, tint_off p] -- tune
 unfold Region.shade; split_ifs <;> simp [h,show loc V t p j= _ from loc_h V t p ⟨j,h⟩, hp p j h] -- tune
end Traversed
end YM.CF.Buffered.Region
#print axioms YM.CF.Buffered.Region.Traversed.verge
