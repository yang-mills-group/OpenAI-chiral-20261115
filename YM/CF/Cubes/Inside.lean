import YM.CF.Cubes.Chamber

/-! Short travels in assigned faces. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Cube
open Lattice Lat SU Finset
open scoped Matrix.Norms.L2Operator MatrixOrder BigOperators
attribute [local instance] opCStarAlgebra
variable {m B N : Side}
structure BetweenY (a z b : Cover) : Prop where
  left i : min (a i) (b i) ≤ z i
  right i : z i ≤ max (a i) (b i)
lemma range_leg (x : Cover) (p : Step) (n : ℕ) (z : Cover) (h : z∈visits x (List.replicate n p)) : ∃ j≤n,z=x+j • p.vec := by
  induction n generalizing x with
  | zero => exact ⟨0,le_rfl,by simpa [visits] using h⟩
  | succ n ih =>
    rw [List.replicate_succ,visits] at h
    rcases List.mem_cons.mp h with f|f; exact ⟨0,Nat.zero_le _,by simp [f]⟩
    obtain ⟨j,hj,g⟩ := ih (x+p.vec) f
    exact ⟨j+1,by omega,by rw [g,succ_nsmul]; abel⟩
lemma range_axis (x : Cover) (p : Axis) (n : ℤ) (z : Cover) (h : z∈visits x (straight p n)) : BetweenY x z (x+n • step p) := by
  obtain ⟨j,hj,f⟩ := range_leg _ _ _ _ h
  rw [f]; constructor <;> intro i <;> by_cases e:i=p
  · subst p; change min (x i) _≤ _; by_cases h:n<0 <;> (simp [Step.vec,h,nsmul_eq_mul,zsmul_eq_mul] <;> omega)
  · change _ ≤ _; by_cases h:n<0 <;> simp [Step.vec,h,e]
  · subst p; by_cases h:n<0 <;> (simp [Step.vec,h,nsmul_eq_mul,zsmul_eq_mul] <;> omega)
  · by_cases h:n<0 <;> simp [Step.vec,h,e]
lemma append_visit {x z : Cover} {l s : Walk} (h : z∈visits x (l++s)) : z∈visits x l ∨ z∈visits (stop x l) s := by
  induction l generalizing x with
  | nil => right; simpa [stop] using h
  | cons i l ih => rw [List.cons_append,visits] at h; rcases List.mem_cons.mp h with hz|hz; exact Or.inl (List.mem_cons.mpr (Or.inl hz)); exact (ih hz).imp_left (fun w=>List.mem_cons_of_mem _ w)
lemma way_visit (x : Cover) (a b : Cover) (l : List Axis) (h : l.Nodup) (z) (e : z ∈ visits x (axisRoute a b l)) : BetweenY x z (stop x (axisRoute a b l)) := by
  induction l generalizing x with
  | nil => simp [visits,axisRoute] at e; subst z; simp only [axisRoute, List.flatMap_nil,stop]; exact ⟨by simp, by simp⟩
  | cons i l ih =>
    let s := b i-a i; let y := x+s • step i
    have hx := List.nodup_cons.mp h
    rw [show axisRoute a b (i::l)=straight i s++axisRoute a b l from rfl] at e ⊢
    rw [stop_append,straight_stop]; change BetweenY x z (stop y (axisRoute a b l))
    have ht : (stop y (axisRoute a b l)) i=y i := by rw [axisRoute_end a b y l hx.2]; simp [hx.1]
    have hg j (h:j≠i) : y j=x j := by simp [y,h]
    rcases append_visit e with q|q
    · have hu := range_axis x i s z q
      have he j (h:j≠i) : z j=x j := by
        have hk := show _ from hu.left j; have hl:= hu.right j
        change min (x j) (y j) ≤ z j at hk; change z j≤max (x j) (y j) at hl; rw [hg _ h,min_self] at hk; rw [hg _ h,max_self] at hl; exact hl.antisymm hk
      constructor <;> intro j <;> by_cases H:j=i
      · rw [H,ht]; exact hu.left i
      · rw [he _ H]; apply min_le_left
      · rw [H,ht]; exact hu.right i
      rw [he _ H]; apply le_max_left
    rw [straight_stop] at q; have hu := ih y hx.2 q
    have he : z i=y i := by have hx:= hu.left i; have hh := hu.right i; rw [ht,min_self] at hx; rw [ht,max_self] at hh; exact hh.antisymm hx
    constructor <;> intro j <;> by_cases H:j=i
    · rw [H,ht,he]; apply min_le_right
    · rw [←hg j H]; exact hu.left j
    · rw [H,ht,he]; apply le_max_right
    rw [←hg j H]; exact hu.right j
lemma march_visit (x y : Site N) (o : Lattice.Order) (z) (h : z∈visits x (march x y o)) : ∃ u : Cover, z=x+wrap N u ∧ BetweenY 0 u (lift (y-x)) := by
  let l := march x y o
  have hm (w : Cover) (l : Walk) (z) : z∈visits (x+wrap N w) l → ∃ v∈visits w l, z=x+wrap N v := by
    induction l generalizing w z with
    | nil => intro h; exact ⟨w,by simp [visits],by simpa [visits] using h⟩
    | cons i l ih =>
      intro h; rcases List.mem_cons.mp h with h|h; exact ⟨w,List.mem_cons_self,h⟩
      have he : x+wrap N (w+i.vec)=x+wrap N w+i.vec := by rw [map_add,wrap_vec,add_assoc];
      obtain ⟨t,f,p⟩ := ih (w+i.vec) z (he.symm ▸ h); exact ⟨t,List.mem_cons_of_mem _ f,p⟩
  obtain ⟨u,hU,p⟩ := hm 0 l _ (by simpa using h)
  have hu := way_visit 0 0 (lift (y-x)) (allAxes o) ((List.nodup_finRange _).map o.injective) u hU
  exact ⟨u,p,route_end (0:Cover) (lift (y-x)) o ▸ hu⟩
-- tri tie: require separation x y≤B while either point within B. circle of radius B about same label. equality of lifts via dvd_natAbs, since |u-v|+B≤3 B<4B.
lemma triangle_lift {x y z : Site (Domain m B)} (h : separation x z≤B.val) (g : separation y z≤B.val) (p : separation y x≤B.val) : lift (y-x)=lift (y-z)-lift (x-z) := by
  have H : wrap _ (lift (y-x))=wrap (Domain m B) (lift (y-z)-lift (x-z)) := by rw [map_sub,wrap_lift, wrap_lift,wrap_lift]; abel
  funext i
  let l := lift (x-z) i; let m' := lift (y-z) i; let k := lift (y-x) i
  have he : ((k:ℤ):Per (Domain m B))=↑(m'-l) := congr_fun H i
  have hg : ((Domain m B).val:ℤ) ∣ m'-l-k := (ZMod.intCast_eq_intCast_iff_dvd_sub ..).mp he -- tune
  have hk : l.natAbs≤B.val := (component_le (x-z) i).trans h
  have hm : m'.natAbs≤B.val := (component_le (y-z) i).trans g
  have ha : k.natAbs≤B.val := (component_le (y-x) i).trans p
  have hh := enough m B; have ht : 0<B.val := B.property
  change k=m'-l
  have G : m'-l-k=0 := Int.eq_zero_of_abs_lt_dvd hg (by rw [abs_lt]; omega)
  omega
lemma visit_room {x y : Site (Domain m B)} {a : Index m} (hx : x∈room m B a) (hy : y∈room m B a) (ht : separation y x≤B.val) (o : Lattice.Order) (z) (h : z∈visits x (march x y o)) : z∈room m B a := by
  obtain ⟨v,hv,e⟩ := march_visit x y o z h
  let t := address m B a
  have he : lift (y-x)=lift (y-t)-lift (x-t) := triangle_lift (room_span hx) (room_span hy) ht
  have hk : z=t+wrap _ (lift (x-t)+v) := by rw [map_add,wrap_lift,hv]; abel
  rw [room_mem]; intro i
  let L := lift (x-t) i; let U := lift (y-t) i; let D := broadface m B (a i)
  have hp : t i=high m B (a i) := high_here m B a i
  have hl : L.natAbs ≤ D := by change delta1 _ (x i) (t i)≤_; rw [hp]; exact (room_mem ..).mp hx i
  have hh : U.natAbs ≤ D := by change delta1 _ (y i) (t i)≤_; rw [hp]; exact (room_mem ..).mp hy i
  have hA := e.left i; have hB := e.right i; rw [he] at hA hB; change min 0 (U-L) ≤ v i at hA; change v i ≤ max 0 (U-L) at hB
  have hD : (L+v i).natAbs ≤ D := by omega
  unfold roomX; rw [hk]; change delta1 _ (t i+(↑(L+v i):Per (Domain m B))) _≤_; rw [hp,d_small _ _ (hD.trans (broad_le m B _))]; exact hD
lemma traverse {x y : Site (Domain m B)} {a : Index m} (hx : x∈room m B a) (hy : y∈room m B a) (ht : separation y x≤B.val) (o : Lattice.Order) {U V : Bkg (Domain m B)} (h : Agrees (room m B a) U V) : travel U x (march x y o)=travel V x (march x y o) :=
  travel_local _ _ _ _ (fun e g f=>h e (visit_room hx hy ht o _ g) (visit_room hx hy ht o _ f))
end YM.CF.Cube
