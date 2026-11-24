import YM.CF.Mir.Kick
import YM.CF.Reflect.Paint

/-! Domain for the site reflection through gauge sites. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.RP
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant Phase Mir Mir.Trip MeasureTheory Finset
attribute [local instance] opCStarAlgebra
variable {N m B : Side}
def nextPlane (x : Per (More N)) : Prop := x.val≤N.val
def backPlane (x : Per (More N)) : Prop := x.val=0 ∨ N.val ≤ x.val
def wedge1 (x : Per (More N)) : Prop := 0<x.val ∧ x.val<N.val
lemma cover_t (x : Per (More N)) : nextPlane x ∨ backPlane x := by unfold nextPlane backPlane; omega
lemma minus_plane (x : Per (More N)) : nextPlane (-x) ↔ backPlane x := by
  unfold nextPlane backPlane
  by_cases h:x=0
  · rw [h,neg_zero,ZMod.val_zero]; omega
  letI : NeZero x:=⟨h⟩
  have hk : x.val≠0 := fun k=>h ((ZMod.val_eq_zero x).mp k)
  have ht := ZMod.val_lt x; have he := natM N
  rw [ZMod.val_neg_of_ne_zero]; omega
lemma wedge_plane (x : Per (More N)) (h : nextPlane x) (g : backPlane x) : -x=x := by
  unfold nextPlane backPlane at *; rcases g with e|e; rw [(ZMod.val_eq_zero x).mp e,neg_zero]
  have he : x.val=N.val := Nat.le_antisymm h e
  letI : NeZero x := ⟨fun p=>by rw [p,ZMod.val_zero] at he; have hx:=N.property; exact Nat.ne_of_lt hx he⟩ -- tune
  apply ZMod.val_injective; rw [ZMod.val_neg_of_ne_zero,he,natM]; omega
lemma vnext (N : Side) (x : Per N) : (x+1).val=if x.val+1=N.val then 0 else x.val+1 := by
  rw [ZMod.val_add,ZMod.val_one_eq_one_mod,Nat.add_mod_mod]; split <;> rename_i h
  · rw [h,Nat.mod_self]
  exact Nat.mod_eq_of_lt (by have ht:= ZMod.val_lt x; omega)
lemma admiss_step (x : Per (More N)) : (nextPlane x∧ nextPlane (x+1)) ∨ (backPlane x ∧ backPlane (x+1)) := by
  unfold nextPlane backPlane; have ht := ZMod.val_lt x; have he:=natM N; rw [vnext]; split <;> omega
lemma shared_step (g : 2 ≤ N.val) (x : Per (More N)) (h : nextPlane x∧ backPlane x) (p : nextPlane (x+1)) : ¬backPlane (x+1) := by
  unfold nextPlane backPlane at *; intro k
  rw [vnext] at p k
  obtain ⟨hz,h|h⟩ := h <;> rcases k with hk|hk <;> split_ifs at * <;> have he := natM N <;> omega
lemma suff (m B : Side) : (CSide m B).val = 2*(m.val*B.val) := by rw [CSide,PNat.mul_coe,natM]; ring
lemma suff_pos (m B : Side) : 2 ≤ (CSide m B).val := by rw [suff]; have hk:= m.property; have he:= B.property; have hp:=Nat.mul_pos hk he; exact Nat.mul_le_mul_left 2 hp
lemma suffM (m B) : (CSide m B).val = B.val*(More m).val := by rw [suff,natM]; ring
instance dLp (x : Per (More N)) : Decidable (nextPlane x) := by unfold nextPlane; infer_instance
instance dLm (x : Per (More N)) : Decidable (backPlane x) := by unfold backPlane; infer_instance
-- origin plane

def north (N : Side) (i : Axis) : Support (More N) := univ.filter fun x => nextPlane (N:=N) (x i)
def south (N : Side) (i : Axis) : Support (More N) := univ.filter fun x => backPlane (N:=N) (x i)
@[simp] lemma north_mem (x : Site (More N)) (i) : x∈north N i ↔ nextPlane (N:=N) (x i) := by simp [north]
@[simp] lemma south_mem (x : Site (More N)) (i) : x∈south N i ↔ backPlane (N:=N) (x i) := by simp [south]
abbrev upField (m B : Side) := north (CSide m B)
abbrev downField (m B : Side) := south (CSide m B)
def seaM (m : Side) (i : Axis) := north (More m) i
def seaP (m : Side) (i : Axis) := south (More m) i -- name wrong convention change

def slideM (m : Side) (i : Axis) : Trip m := ⟨fun j=>decide (i=j),0⟩
@[simp] lemma slide_glare (i j : Axis) : (slideM m i).glare j=true ↔ i=j := by simp [slideM]
@[simp] lemma slide_inv (m : Side) (i : Axis) : (slideM m i)⁻¹=slideM m i := by apply Trip.ext; simp; rw [Trip.movei,show (slideM m i).move=0 from rfl,Signed.act_zero,neg_zero]
lemma slide_flips (m : Side) (i) (x) : (slideM m i).flips x=star x := by
  unfold flips; rw [show univ.filter (fun j=> (slideM m i).glare j=true)={i} by ext; simp only [mem_filter,mem_univ,true_and,slide_glare,mem_singleton]; exact eq_comm, if_pos (by simp)]
def revX (m B : Side) (i : Axis) := run B (slideM m i)
def revI (m : Side) (i : Axis) := adv (slideM m i)
lemma rev_rule (m B i j) (x) : revX m B i x j = if i=j then -(x j) else x j := by simp [revX,run,affine,torShift,paneShift, ←Ratio.root_embed, slideM]
lemma rev_axis (x : Site (Domain m B)) (i) : revX m B i x i= -(x i) := by simp [rev_rule]
lemma map_rule (m i j) (x) : revI m i x j = if i=j then -(x j) else x j := by simp [revI,adv,affine,paneShift,←Ratio.root_embed,slideM]
@[simp] lemma rev_back (x : Site (Domain m B)) (i) : revX m B i (revX m B i x)=x := by unfold revX; nth_rw 1 [←slide_inv m i]; exact run_back ..
@[simp] lemma map_back (x : Index m) (i) : revI m i (revI m i x)=x := by unfold revI; nth_rw 1 [←slide_inv m i]; exact adv_back ..
lemma return_north (x:Site (Domain m B)) (i) : revX m B i x∈upField m B i ↔ x∈downField m B i := by rw [north_mem,south_mem,rev_axis]; exact minus_plane ..
lemma ends_share (x:Site (Domain m B)) (i) (h:x∈upField m B i) (g:x∈downField m B i) : revX m B i x=x := by funext j; rw [rev_rule]; by_cases g':i=j; subst j; rw [if_pos rfl]; exact wedge_plane _ ((north_mem ..).mp h) ((south_mem ..).mp g); rw [if_neg g']
lemma room_ord (x : Index m) (i : Axis) : (address m B x i).val= B.val*(x i).val := by
  unfold address; rw [high_here m B, show high m B (x i)=high m B (((↑(x i).val:ℤ):Per (GridN m))) by rw [Int.cast_natCast, ZMod.natCast_zmod_val],high_cast];
  rw [← Nat.cast_mul ((B.val)) (x i).val,Int.cast_natCast,ZMod.val_natCast_of_lt];
  rw [(show (Domain m B).val=(GridN m).val*B.val from (scaleR m B).exact_size),mul_comm]; gcongr; exact ZMod.val_lt _ -- tune
lemma odd_mid (m : Side) (x : Per (GridN m)) (l:x.val=0 ∨ x.val=(More m).val) : ¬ OddAxis m x := by
  rcases l with g|g
  · rw [(ZMod.val_eq_zero x).mp g]; unfold OddAxis; change ¬ (assembly (More m)).residue 0 0=1; rw [map_zero]; exact (show ¬(0:ZMod 2)=1 by decide)
  unfold OddAxis; let A := assembly (More m)
  rw [show (fun _:Axis=>x)=wrap _ (fun _=>((More m).val:ℤ)) by
    funext i; rw [wrap_here,Int.cast_natCast,←g, ZMod.natCast_zmod_val],Ratio.residue_wrap, wrap_here,Int.cast_natCast,natM, Nat.cast_mul]
  change ¬((m.val:ℕ):ZMod 2)*2=1; rw [show (2:ZMod 2)=0 by decide,mul_zero]; decide
lemma plane_hold (a : Index m) (i) : a∈seaM m i ↔ address m B a ∈ upField m B i := by
  rw [seaM,north_mem,north_mem]; unfold nextPlane; rw [room_ord,suffM m B]; exact (mul_le_mul_iff_right₀ (show 0<B.val from B.property)).symm -- tune
lemma plane_turn (a : Index m) (i) : revI m i a∈seaM m i ↔ a∈seaP m i := by
  rw [seaM,seaP,north_mem,south_mem,map_rule,if_pos rfl]; exact minus_plane ..
lemma plane_all (a : Index m) (i : Axis) : a∈seaM m i ∨ a∈seaP m i := (cover_t (N:=More m) (a i)).imp ((north_mem ..).mpr) ((south_mem ..).mpr)
lemma plane_both (a : Index m) (i) (h:a∈seaM m i) (k:a∈seaP m i) : revI m i a=a := by funext j; by_cases f:i=j; subst j; rw [map_rule,if_pos rfl]; exact wedge_plane _ ((north_mem ..).mp h) ((south_mem ..).mp k); rw [map_rule,if_neg f]
lemma plane_room {a : Index m} (i) (h:a∈seaM m i) : room m B a⊆upField m B i := by
  intro x hx
  have he := room_mem a x|>.mp hx i
  rw [north_mem]; by_cases k:OddAxis m (a i)
  · unfold nextPlane
    let M := (More m).val; have hp : 0<(a i).val ∧ (a i).val<M := by
      have he : ¬ ((a i).val=0 ∨ (a i).val=M) := fun g=> odd_mid m _ g k
      have hg : (a i).val≤M := (north_mem a i).mp h; omega
    let j := lift (x-address m B a) i
    have hz : j.natAbs≤B.val := (component_le _ i).trans (room_span hx)
    let n := (address m B a i).val; let K := (CSide m B).val
    have hk : B.val ≤ n ∧ n+B.val≤K := by
      rw [show n=B.val*(a i).val from room_ord ..]; refine ⟨?_,?_⟩
      · exact (le_mul_of_one_le_right (by omega) hp.1)
      rw [←mul_add_one,show K=B.val*M from suffM ..]; exact Nat.mul_le_mul_left _ hp.2
    have hJ : 0≤(n:ℤ)+j ∧ (n:ℤ)+j≤ K := by omega
    have hX : x i=((Int.toNat (↑n+j):ℕ):Per (Domain m B)) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hJ.1,Int.cast_add,Int.cast_natCast,show (n:Per (Domain m B))= _ from ZMod.natCast_zmod_val _] -- tune
      rw [show (j:Per (Domain m B))=x i-address m B a i from congr_fun (wrap_lift _) i]; abel
    have hhL := suff_pos m B; have hb : (Domain m B).val=K*2 := natM _
    change (x i).val≤K
    generalize hw : Int.toNat (↑n+j)=p at hX; rw [hX,ZMod.val_natCast_of_lt] <;> omega
  rw [(room_e m B (a i) _ k).mp he, ←high_here m B]; exact ((north_mem ..).mp ((plane_hold ..).mp h)) -- tune occurrence
lemma level_keep (i) {a:Index m} (h:a∈seaM m i) : faces m a⊆seaM m i := by
  intro x hx; rw [plane_hold (B:=1)]; exact plane_room i h (room_in (mem_filter.mp hx).2 (raddr ..)) -- tune
end YM.CF.RP
