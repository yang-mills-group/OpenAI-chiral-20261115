import YM.CF.BPress.Slice
import YM.CF.BPress.Grid.Thin
/-!
Oriented arc and cylinder coordinate, including all tangential faces. Ghost successor excluded. Canonical gauge and masks use these actual times T.rise k, not a time double-cover.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress
open Function Lattice SU Mag Cube Grid Finset
open scoped Topology BigOperators Classical Matrix
variable {s : Side}
structure Tunnel (s : Side) where
 o : Per s
 n : Side  -- positive number of steps
 room : n.val+1<s.val
namespace Bands
variable {B : BandWidth} (X : Bands s B)
def mark (i : X.Index) : Tunnel s:= ⟨X.start i, B.marked, (Nat.succ_le_of_lt B.marked_lt).trans_lt X.full_lt⟩
def ditch (i : X.Index) : Tunnel s:= ⟨X.stop i,⟨B.D,B.D_pos⟩, (Nat.succ_le_of_lt B.D_lt).trans_lt X.full_lt⟩
end Bands
namespace Tunnel
variable (W : Tunnel s)
def rise (k : ℕ) := W.o + (k:Per s)
def fall (k : ℕ) := W.rise (W.n.val-k)
def mem := arc W.o W.n.val
abbrev last := W.rise W.n.val
@[simp] lemma rise_zero : W.rise 0=W.o:=by simp [rise]
@[simp] lemma rise_succ (k:ℕ) : W.rise (k+1)=W.rise k+1:=by simp [rise,add_assoc]
@[simp] lemma fall_zero : W.fall 0=W.last:=rfl
@[simp] lemma fall_all : W.fall W.n.val=W.o:=by simp [fall]
lemma fall_before {k:ℕ}(h:k<W.n.val) : W.fall k=W.fall (k+1)+1:=by unfold fall; rw [←rise_succ, show W.n.val-(k+1)+1=W.n.val-k by omega]
lemma rise_val {k:ℕ}(p:k ≤ W.n.val+1) : (W.rise k-W.o).val=k:= depth_eq _ (lt_of_le_of_lt p W.room)
lemma rise_inj {i j:ℕ}(p : i≤W.n.val+1)(v:j≤W.n.val+1)(e:W.rise i=W.rise j): i=j:=by rw [←W.rise_val p,e,W.rise_val v]
lemma rise_mem {j:ℕ}(h:j ≤ W.n.val)(x : Tri s) : event (W.rise j) x∈ W.mem:=by rw [mem,arc_mem,event_time,W.rise_val (by omega : j≤W.n.val+1)]; exact h
lemma early (x : Tri s) : event W.o x∈ W.mem:=W.rise_zero ▸ W.rise_mem (Nat.zero_le _) x
lemma late (x : Tri s): event W.last x∈ W.mem:= W.rise_mem le_rfl x
lemma internal (x : Site s) : x∈ W.mem ↔ ∃ k ≤ W.n.val, x 0=W.rise k:= by
 constructor
 intro t; obtain ⟨j,h,e⟩:=arc_cases _ _ _ t; exact ⟨j,h,congrFun e 0⟩; rintro ⟨j,h,e⟩; rw [mem,arc_mem,e,W.rise_val (by omega : j ≤ W.n.val+1)]; exact h
lemma normal_in {i : Per s}(x : Tri s) : vl i x∈inside W.mem ↔ ∃ k < W.n.val, i=W.rise k:=by
 rw [inside_iff]; dsimp only [vl]; rw [event_up,W.internal, W.internal,event_time,event_time]; constructor
 · rintro ⟨⟨k,v,rfl⟩,l,h,e⟩; rw [←rise_succ] at e; have he:= W.rise_inj (by omega : k+1 ≤ _) (by omega) e; exact ⟨k,by omega,rfl⟩ -- tune
 rintro ⟨i,p,rfl⟩; exact ⟨⟨i,p.le,rfl⟩,i+1,p,(W.rise_succ i).symm⟩
lemma tang_in {i : Per s} (x : FlatLink s) : fl i x∈ inside W.mem ↔ ∃ k ≤ W.n.val,i=W.rise k:=by rw [inside_iff]; dsimp only [fl]; simp only [event_across,W.internal,event_time,and_self]
-- used support tests
lemma horizontal_eq {U V : Micro s}(p : Lattice.Agrees W.mem U V) {k : ℕ}(v:k≤ W.n.val) : horizontal (W.rise k) U=horizontal (W.rise k) V:= Agrees.fl p _ fun i=> W.rise_mem v i
lemma normal_eq {U V : Micro s}(p : Lattice.Agrees W.mem U V) {k : ℕ}(v:k<W.n.val) : normal (W.rise k) U=normal (W.rise k) V:= by
 funext i; let p':= W.normal_in i|>.mpr ⟨k,v,rfl⟩; obtain ⟨l,g⟩:= inside_iff ..|>.mp p'; exact p _ l g
lemma fixed_vl (u : Per s) : (u=W.o ∨ u=W.last) ↔ (u=W.rise 0 ∨ u=W.rise W.n.val) := by simp

-- Need transfer plaquette estimates on explicit coordinates back to *touched ⊆ mem* test.
theorem every_face {U : Micro s} {t : ℝ} (h : ∀ k≤ W.n.val, ∀ (x:Tri s)(i j:SpatialDir), i<j→group.chord (travel U (event (W.rise k) x) (square i.succ j.succ))≤t) (v : ∀ k< W.n.val,∀ (x:Tri s)(i:SpatialDir),group.chord (travel U (event (W.rise k) x) (square 0 i.succ))≤t) (i : Face (Per s)) (p : RG.touched i⊆ W.mem) : group.chord (faceValue U i)≤t:=by
 obtain ⟨x,⟨i,j⟩,g⟩:=i; change i<j at g; have h1:x∈W.mem:= p (by simp [RG.touched,square,visits]); obtain ⟨k,e,f⟩:= W.internal x|>.mp h1; have hh:x=event (W.rise k) (Fin.tail x):=by rw [←f,event_eta]
 have h2:x+step i∈ W.mem:= p (by simp [RG.touched,square,visits]); change group.chord (travel U x (square i j)) ≤ _; obtain ⟨j,rfl⟩:= Fin.exists_succ_eq.mpr (Fin.ne_zero_of_lt g); by_cases t:i=0; subst i; rw [hh] at h2 ⊢; rw [event_up] at h2; refine v k ?_ _ _; obtain ⟨u,t,p⟩:=W.internal _|>.mp h2; rw [event_time,←rise_succ] at p; have hu:= W.rise_inj (Nat.succ_le_succ e) (Nat.le_succ_of_le t) p; omega
 obtain ⟨i,rfl⟩:= Fin.exists_succ_eq.mpr t; rw [hh]; exact h k e _ _ _ (Fin.succ_lt_succ_iff.mp g)

-- frame allocation within the arc. Mach uses identity outside. Use for universal-frame AND axial turns.
def book (f : ℕ → HFrame s) : Mach s:= fun x=> if x ∈ W.mem then f (x 0-W.o).val (Fin.tail x) else 1
@[simp] lemma booked (f : ℕ → HFrame s) {k:ℕ}(v:k≤W.n.val) : confine (W.rise k) (W.book f)= f k:=by
 funext x; rw [confine, book,if_pos (W.rise_mem v x),event_time,W.rise_val (by omega : k ≤ W.n.val+1)]; simp [event]
@[fun_prop] lemma book_cont : Continuous W.book:= by apply continuous_pi; intro x; by_cases h:x∈W.mem; simp only [book,h,↓reduceIte]; fun_prop; simp only [book,h,↓reduceIte]; exact continuous_const

-- cut and profile quarters. L=4n+r, round each collar to n. Applies even when collar zero. Profile clipped at both ends.
def cut := W.n.val /2
def lips := W.n.val /4
def lip := W.n.val- W.lips
lemma cut_lt : W.cut < W.n.val:= Nat.div_lt_self W.n.property (by norm_num)
lemma collar_ends : W.lips ≤ W.cut ∧ W.cut<W.lip ∧ W.lip ≤ W.n.val := by have h:0<W.n.val:= W.n.property; change W.lips ≤ W.cut ∧ _; unfold cut lips lip; unfold lips; omega -- fails n=2? lips=0 lip2; 3=0;4=1 yes
lemma law0 : W.lips<W.lip:= W.collar_ends.1.trans_lt W.collar_ends.2.1
lemma law1 : ((W.n.val:ℝ))/2 ≤ (W.lip:ℝ)-(W.lips:ℝ):= by
 rw [div_le_iff₀ zero_lt_two, ←Nat.cast_sub W.law0.le]; exact_mod_cast (show W.n.val ≤ (W.lip-W.lips)*2 by unfold lip; unfold lips; omega)
def progress (k:ℕ) : ℝ := ((min (k-W.lips) (W.lip-W.lips):ℕ):ℝ)/(W.lip-W.lips:ℕ)
lemma ratio {k:ℕ} (p: W.lips ≤ k)(v : k≤ W.lip) : W.progress k=((k:ℝ)-W.lips)/(W.lip-(W.lips:ℝ)):=by unfold progress; rw [min_eq_left (by omega), Nat.cast_sub p,Nat.cast_sub W.law0.le]
lemma starts {k:ℕ}(p:k ≤ W.lips): W.progress k=0:=by simp [progress,Nat.sub_eq_zero_of_le p]
lemma ends {k:ℕ}(p:W.lip ≤ k) : W.progress k=1:=by have he:=Nat.sub_pos_of_lt W.law0; unfold progress; rw [min_eq_right (by omega)]; field_simp -- tune
lemma ratio_I (k:ℕ) : W.progress k∈ Set.Icc 0 1 := by have h : 0<W.lip-W.lips:= Nat.sub_pos_of_lt W.law0; refine Set.mem_Icc.mpr ⟨?_,?_⟩; unfold progress; positivity; unfold progress; refine div_le_one_of_le₀ ?_ (by positivity); exact_mod_cast min_le_right (k-W.lips) (W.lip-W.lips)
lemma ratio_step (k:ℕ) : |W.progress (k+1)-W.progress k|≤2/(W.n.val:ℝ):=by
 rcases lt_or_ge k W.lips with v|v; rw [W.starts v,W.starts v.le,sub_self,abs_zero]; positivity; by_cases p:k ≥ W.lip; rw [W.ends p,W.ends (by omega : W.lip ≤ k+1),sub_self,abs_zero]; positivity -- order? rw ends p first
 have hx : W.lip-W.lips>0:= Nat.sub_pos_of_lt W.law0; have ht:=W.law1; rw [←Nat.cast_sub W.law0.le] at ht; rw [W.ratio v (by omega),W.ratio (by omega : W.lips≤k+1) (by omega),← sub_div]; push_cast -- tune
 have hz : 0<(W.lip:ℝ)-W.lips := sub_pos.mpr (Nat.cast_lt.mpr W.law0); rw [show _ + 1 - _ - ((k:ℝ)-(W.lips:ℝ))=1 by ring, abs_of_pos (one_div_pos.mpr hz)]; rw [div_le_div_iff₀ hz (by positivity)]; linarith [W.law1]

end Tunnel
end YM.CF.BPress
