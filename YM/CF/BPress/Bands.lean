import YM.CF.Reflect.Center

/-!
eq:Bbands & eq:B-gap.
Take Axis 0 (time) in the construction. All endpoints are gauge sites.
We use coordinates `clock` in which zero of EACH slot means the beginning
of its marked **band**, NOT the beginning of the slot. Gap i follows band i.
Arcs use ZMod, also for the last gap, and count *steps*. Our supports use
only links with both endpoints in them.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace YM.CF.BPress
open Function Lattice Cube Finset
open scoped BigOperators Topology
variable {s : Side}

abbrev Tri (s : Side) := Fin 3 → Per s
abbrev event (t : Per s) (p : Tri s) : Site s := Fin.cons t p
lemma tri_card (s : Side) : Fintype.card (Tri s)= s.val^3 := by simp [Tri,Per,ZMod.card]
@[simp] lemma event_eq {u v : Per s} {p q : Tri s} : event u p=event v q ↔ u=v∧p=q := by
  constructor
  · intro h; exact ⟨congrFun h 0,(by funext a; simpa [event] using congrFun h a.succ)⟩
  · rintro ⟨rfl,rfl⟩; rfl
@[simp] lemma event_time (t : Per s) (p : Tri s) : event t p 0=t := by simp [event]
@[simp] lemma event_eta (x : Site s) : event (x 0) (Fin.tail x)=x := by simp [event]
def timeSpace (s : Side) : Per s × Tri s ≃ Site s where
  toFun x:=event x.1 x.2
  invFun x:=(x 0,Fin.tail x)
  left_inv := by rintro ⟨i,p⟩; simp [event]
  right_inv x:= event_eta x
@[simp] lemma event_up (t : Per s) (p : Tri s) : event t p+step 0=event (t+1) p := by
  funext i; refine Fin.cases ?_ (fun k => ?_) i <;> simp [event]
def glide (i : Fin 3) (p : Tri s) : Tri s := p+Fin.tail (step i.succ : Site s)
@[simp] lemma event_across (t : Per s) (p : Tri s) (i : Fin 3) :
    event t p+step i.succ=event t (glide i p) := by
  funext j; refine Fin.cases ?_ (fun k=> ?_) j <;> simp [event, glide, Fin.tail, Ne.symm (Fin.succ_ne_zero i)]

/-- Closed inclusive arc in positive time. -/
def arc (o : Per s) (length : ℕ) : Support s := univ.filter fun x=> (x 0-o).val ≤ length
@[simp] lemma arc_mem (o : Per s) (l : ℕ) (x : Site s) : x∈arc o l ↔ (x 0-o).val ≤ l := by simp [arc]
lemma step_time {i : ℕ} (t : Per s) : t+ ↑(i+1 : ℕ)= t+i+1 := by simp [add_assoc]
lemma depth_eq {i : ℕ} (t : Per s) (h : i < s.val) : (t + (i:Per s) - t).val=i := by rw [add_sub_cancel_left,ZMod.val_natCast_of_lt h]
lemma time_eq (t u : Per s) : u=t+ ↑(u-t).val := by rw [ZMod.natCast_zmod_val]; abel
lemma arc_cases (o : Per s) (l : ℕ) (x : Site s) (h : x∈arc o l) :
    ∃ a : ℕ, a ≤ l ∧ x = event (o+(a:Per s)) (Fin.tail x) :=
  ⟨_,(arc_mem ..).mp h, (event_eta x).symm.trans (congrArg (fun t=>event t (Fin.tail x)) (time_eq o _))⟩
lemma arc_card (o : Per s) (l : ℕ) (p : l<s.val) : (arc o l).card=(l+1)*s.val^3 := by
  let f : Fin (l+1) × Tri s → Site s := fun x=>event (o+ ↑(x.1.val)) x.2
  have hp (x : Fin (l+1)) : x.val < s.val:=lt_of_le_of_lt (Nat.le_of_lt_succ x.isLt) p
  have he : arc o l=univ.image f:= by
    ext x; rw [mem_image]; constructor
    · intro h; obtain ⟨a,ha,t⟩:= arc_cases o l x h; exact ⟨(⟨a,by omega⟩,_),mem_univ _,t.symm⟩
    rintro ⟨⟨i,k⟩,_,rfl⟩; change event (o+ (i.val:Per s)) k∈ _; rw [arc_mem,event_time,depth_eq _ (hp i)]; have he:=i.isLt; omega
  rw [he,card_image_of_injective,card_univ,Fintype.card_prod,Fintype.card_fin,tri_card]
  rintro ⟨i,p⟩ ⟨j,q⟩ E
  obtain ⟨e,h⟩ := event_eq.mp E
  have he:=congrArg (fun t : Per s=> (t-o).val) e; dsimp only at he; rw [depth_eq _ (hp i),depth_eq _ (hp j)] at he
  exact Prod.ext (Fin.ext he) h

/- Mixed radix clock on a single native periodic axis. Reused tangentially. -/
namespace Radix
variable (s L Q : Side)
def dial (o : Per s) (i : Per Q) (a : ℕ) : Per s :=
  o + (↑(L.val * i.val + a) : Per s)
-- explicit size argument (keeps actual lattice Side unchanged)
variable (h : s.val=L.val*Q.val)
include h
lemma dial_val (o : Per s) (i : Per Q) (a : ℕ) (p : a<L.val) :
    (dial s L Q o i a-o).val=L.val*i.val+a := by
  refine depth_eq o (lt_of_lt_of_le (b:=L.val * (i.val+1)) ?_ ?_)
  · rw [mul_add]; omega
  exact h ▸ Nat.mul_le_mul_left L.val (ZMod.val_lt i)
lemma dial_edge (o : Per s) (i : Per Q) : dial s L Q o i L.val=dial s L Q o (i+1) 0 := by
  unfold dial; rw [RP.vnext]; split_ifs with e
  · rw [show L.val*i.val+ L.val=s.val by rw [h]; exact (by rw [show L.val*i.val+L.val=L.val*(i.val+1) by ring,e])]; simp [Per]
  simp [mul_add]

def clock (o : Per s) : Per Q × Fin L.val ≃ Per s where
  toFun x:=dial s L Q o x.1 x.2.val
  invFun x:= (↑((x-o).val / L.val),⟨(x-o).val % L.val, Nat.mod_lt _ L.property⟩)
  left_inv := by
    rintro ⟨i,⟨a,p⟩⟩; simp only [dial_val _ _ _ h _ i a p]; apply Prod.ext
    · simp only; have u : (L.val * i.val+a)/L.val=i.val := by
        have hg : (a + i.val * L.val)/L.val=a/L.val+i.val:=Nat.add_mul_div_right a i.val L.property
        rw [mul_comm, add_comm, hg,Nat.div_eq_of_lt p,zero_add]
      rw [u,ZMod.natCast_zmod_val]
    apply Fin.ext; simp [Nat.mod_eq_of_lt p]
  right_inv x:=by
    have hs : (x-o).val < s.val:=ZMod.val_lt _
    have he : (x-o).val/L.val < Q.val:= (Nat.div_lt_iff_lt_mul L.property).mpr (by rw [mul_comm]; exact hs.trans_le (le_of_eq h))
    unfold dial; dsimp only; rw [ZMod.val_natCast_of_lt he,Nat.div_add_mod]; exact (time_eq o x).symm
end Radix

structure BandWidth where
  /-- L_b=p_b -/
  blank : Side
  /-- D_P (the width of actual marked band) in gauge-site steps -/
  marked : Side
  /-- w₀ -/
  collar : ℕ

namespace BandWidth
variable (B : BandWidth)
def P : ℕ := B.marked.val+ 2*B.collar
def full : Side := ⟨B.P+B.blank.val,Nat.add_pos_right _ B.blank.property⟩
def D : ℕ := B.blank.val+2*B.collar
lemma D_pos : 0<B.D := Nat.add_pos_left B.blank.property _
lemma P_pos : 0<B.P := Nat.add_pos_left B.marked.property _
lemma P_lt : B.P<B.full.val:=Nat.lt_add_of_pos_right B.blank.property
lemma full_eq : B.full.val=B.marked.val+B.D:=by change B.P + B.blank.val =_; unfold P D; omega
lemma marked_lt : B.marked.val<B.full.val:=by rw [B.full_eq]; have he:= B.D_pos; omega
lemma D_lt : B.D < B.full.val:=by rw [B.full_eq]; exact Nat.lt_add_of_pos_left B.marked.property
end BandWidth

structure Bands (s : Side) (B : BandWidth) where
  Q : Side
  enough : 4 ≤ Q.val
  size_eq : s.val = B.full.val * Q.val
  even : Even Q.val
namespace Bands
variable {B : BandWidth} (X : Bands s B)
abbrev Index := Per X.Q
def offset (i : X.Index) : Per s := ↑(B.full.val * i.val)
-- positive chronology in both bands and gaps at this stage
def start (i : X.Index) := X.offset i + (B.collar:Per s)
def stop (i : X.Index) := X.start i + (B.marked.val:Per s)
abbrev clock : X.Index × Fin B.full.val ≃ Per s := Radix.clock s B.full X.Q X.size_eq (↑B.collar)
lemma clock_eq (i : X.Index) (k : Fin B.full.val) : X.clock (i,k)=X.start i + ↑k.val := by
  change ↑B.collar+ (↑(B.full.val*i.val+k.val) : Per s)=_; rw [Nat.cast_add]; unfold start offset; abel
lemma stop_next (i : X.Index) : X.stop i + ↑B.D = X.start (i+1) := by
  simp_rw [stop,add_assoc (X.start i),←Nat.cast_add,← B.full_eq]
  have he:= Radix.dial_edge _ _ _ X.size_eq (↑B.collar) i
  unfold Radix.dial at he; rw [Nat.cast_add, Nat.add_zero] at he; unfold start offset; rw [add_comm _ (B.collar:Per s),add_assoc]; exact he.trans (add_comm ..)
def slot (i : X.Index) : Support s := arc (X.offset i) B.P
def band (i : X.Index) : Support s := arc (X.start i) B.marked.val
def gap (i : X.Index) : Support s := arc (X.stop i) B.D
include X in
lemma two_full : 2*B.full.val < s.val := by rw [X.size_eq, mul_comm 2]; apply Nat.mul_lt_mul_of_pos_left _ B.full.property; have h:=X.enough; omega
include X in
lemma full_lt : B.full.val < s.val:= by have h:= X.two_full; omega
lemma suffix (i : X.Index) : X.stop i + (B.collar:Per s)= X.offset i + ↑B.P:=by
  unfold BandWidth.P stop start; push_cast; rw [two_mul]; abel
lemma slot_qualification (i : X.Index) (x : Site s) (p : x∈X.band i) :
    x∈X.slot i ∧ B.collar ≤ delta1 s (x 0) (X.offset i) ∧
    B.collar ≤ delta1 s (X.offset i+ (B.P:Per s)) (x 0) := by
  obtain ⟨a,ha,h⟩:=arc_cases _ _ _ p
  have he : x 0= X.start i + ↑a:=congrFun h 0
  have hP:=B.P_lt; have hx:=X.two_full; have hQ:B.P=B.marked.val+2*B.collar:=rfl
  rw [slot,arc_mem]; unfold delta1; rw [he,start,add_assoc,← Nat.cast_add,add_sub_cancel_left,add_sub_add_left_eq_sub,←Nat.cast_sub (by omega : B.collar+a ≤ B.P)]
  rw [ZMod.val_natCast_of_lt (by omega : B.collar+a<s.val), ZMod.valMinAbs_natCast_of_le_half (by omega : B.collar+a≤ s.val/2), ZMod.valMinAbs_natCast_of_le_half (by omega : B.P-(B.collar+a)≤ s.val/2)]; omega
lemma band_subset_slot (i : X.Index) : X.band i ⊆ X.slot i:=fun x p=> (X.slot_qualification i x p).1
lemma band_disjoint {i j : X.Index} (p : i≠j) : Disjoint (X.band i) (X.band j):= by
  refine disjoint_left.mpr fun x h g=>?_; obtain ⟨a,ha,he⟩:=arc_cases _ _ _ h; obtain ⟨e,b,f⟩:=arc_cases _ _ _ g
  let l : Fin B.full.val:=⟨a,ha.trans_lt B.marked_lt⟩; let t : Fin B.full.val:=⟨e,b.trans_lt B.marked_lt⟩
  apply p; refine congrArg Prod.fst (X.clock.injective (a₁:=(i,l)) (a₂:=(j,t)) ?_); rw [clock_eq,clock_eq]; exact (event_eq.mp (he.symm.trans f)).1
lemma cover (x : Site s) : ∃ i : X.Index, x∈X.band i ∨ x∈X.gap i:=by
  obtain ⟨⟨i,a,p⟩,e⟩:=X.clock.surjective (x 0); rw [clock_eq] at e; refine ⟨i,?_⟩
  by_cases h:a ≤ B.marked.val
  · left; rw [band,arc_mem,←e,depth_eq _ (p.trans X.full_lt)]; exact h
  right; rw [gap,arc_mem,←e,stop]; change ((X.start i+↑a) - (X.start i+↑B.marked.val)).val ≤ _
  have he:=B.full_eq; have hg:=B.D_lt.trans X.full_lt
  rw [add_sub_add_left_eq_sub,←Nat.cast_sub (by omega : B.marked.val≤a),ZMod.val_natCast_of_lt]; all_goals omega
lemma band_card (i : X.Index) : (X.band i).card=(B.marked.val+1)*s.val^3:= arc_card _ _ (B.marked_lt.trans X.full_lt)
section ferm
variable {N : Side} (Y : Bands (More N) B)
lemma node_misses (i : Y.Index) (h : Even B.blank.val) (g : Even B.P) (k : Even B.collar) (x : Site N) :
    node x 0≠ Y.start i ∧ node x 0≠ Y.stop i := by
  have t : Even B.full.val:=g.add h
  have across {u : ℕ} (p : Even u) : node x 0 ≠ ↑u := by
    intro f; have e:=RP.val_node x 0; rw [f,ZMod.val_natCast] at e
    have h : Even (u%(More N).val):= ?_
    · obtain ⟨j,H⟩:=h; omega
    rw [Nat.even_iff] at p ⊢; rw [Nat.mod_mod_of_dvd]; exact p
    exact ⟨N.val,by rw [natM]; omega⟩
  simp only [start,offset,stop]; rw [← Nat.cast_add,←Nat.cast_add]; refine ⟨across ((t.mul_right _).add k), across (((t.mul_right _).add k).add ?_)⟩
  rcases g with ⟨g,G⟩; unfold BandWidth.P at G; rw [Nat.even_iff]; omega
end ferm
end Bands
end YM.CF.BPress
