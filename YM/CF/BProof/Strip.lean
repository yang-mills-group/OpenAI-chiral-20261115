import YM.CF.BProof.Circle
import YM.Lattice.Foliation
import YM.Lattice.Support

/-! Temporal layouts for eq:Bbands. We take axis zero for time. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof
open Lattice Finset Cube
variable {s N : Side}

abbrev TAxis := Fin 3
abbrev Space (s : Side) := TAxis → Per s
abbrev time (x : Site s) : Per s := x 0
def space (x : Site s) : Space s := fun i => x i.succ

def join (x : Per s) (p : Space s) : Site s := Fin.cons x p
@[simp] theorem time_join (x : Per s) (p : Space s) : time (join x p)=x := rfl
@[simp] theorem space_join (x : Per s) (p : Space s) : space (join x p)=p := Fin.tail_cons ..
@[simp] theorem join_time_space (x : Site s) : join (time x) (space x)=x := Fin.cons_self_tail ..
@[simp] theorem time_add (x y : Site s) : time (x+y)=time x+time y := rfl
@[simp] theorem time_sub (x y : Site s) : time (x-y)=time x-time y := rfl
@[simp] theorem time_step (i : Axis) : time (step i : Site s) = if i=0 then 1 else 0 := by rw [time,step_apply]; congr 1; grind
@[simp] theorem space_add (x y : Site s) : space (x+y)=space x+space y := rfl
lemma space_step0 : space (step 0 : Site s)=0 := by ext i; simp [space,Fin.succ_ne_zero]
abbrev tstep (i : TAxis) : Space s := space (step i.succ)
@[simp] theorem tstep_apply (i j : TAxis) : (tstep i : Space s) j = if j=i then 1 else 0 := by simp [tstep,space]
lemma join_step (x : Per s) (p : Space s) : join (x+1) p = join x p + step 0 := by
 conv_rhs => rw [← join_time_space (join x p + step 0)]
 simp only [time_add,time_step,ite_true,time_join,space_add,space_join,space_step0,add_zero]
lemma step_join (x : Per s) (p : Space s) (i : TAxis) : join x (p+tstep i) = join x p + step i.succ := by
 conv_rhs => rw [← join_time_space (join x p + step i.succ)]
 simp only [time_add,time_step,Fin.succ_ne_zero,ite_false,time_join,space_add,space_join,add_zero,tstep]

def joinEquiv (s : Side) : Per s × Space s ≃ Site s where
 toFun p := join p.1 p.2
 invFun x := (time x,space x)
 right_inv := join_time_space
 left_inv p := by cases p; simp

/-- generic closed temporal interval. -/
def strip (a : Per s) (l : ℕ) : Support s := univ.filter fun x => time x ∈ arc a l
@[simp] theorem mem_strip {x : Site s} {a : Per s} {l : ℕ} : x∈strip a l ↔ along a (time x) ≤ l := by simp [strip]

theorem strip_map (a : Per s) (l : ℕ) : strip a l = ((arc a l) ×ˢ univ).map (joinEquiv s).toEmbedding := by
 ext x; rw [mem_map_equiv,mem_strip]; simp [joinEquiv]

@[simp] theorem space_card (s : Side) : Fintype.card (Space s) = s.val^3 := by simp [Space,Per,TAxis,ZMod.card]
@[simp] theorem strip_card (a : Per s) {l : ℕ} (hl : l < s.val) : (strip a l).card = (l+1)*s.val^3 := by rw [strip_map]; simp [arc_card a hl]

/-- strip setup includes all lower endpoint shifts. `pole i` = temporal coordinate of the
left face of band i; `edge i` its right face. Following this band comes a gap (`gap i`). -/
structure Strips (s : Side) where
  q : Side
  grid : Ratio q s
  long : ℕ
  short : ℕ
  pivot : ℕ
  total : long + short = grid.count.val -- for B: long=DP short=D
  enough : 4 ≤ q.val
  long_pos : 0 < long
  short_pos : 0 < short
namespace Strips
variable (S : Strips s)
abbrev Index := Per S.q
abbrev fromMark : Per s := S.pivot
abbrev fromGap : Per s := (S.pivot + S.long : ℕ)
def pole (i : S.Index) := origin S.grid S.fromMark i
def edge (i : S.Index) := origin S.grid S.fromGap i
def band (i : S.Index) := strip (S.pole i) S.long
def gap (i : S.Index) := strip (S.edge i) S.short

theorem count_small : S.grid.count.val * 4 ≤ s.val := by
 rw [S.grid.exact_size,mul_comm]; exact Nat.mul_le_mul_right _ S.enough
theorem long_lt : S.long < S.grid.count.val := by have := S.short_pos; have := S.total; omega -- uses total?
theorem short_lt : S.short < S.grid.count.val := by have := S.long_pos; have := S.total; omega
theorem count_lt : S.grid.count.val < s.val := by have := S.count_small; have : 0<S.grid.count.val := S.grid.count.property; omega

lemma last_pole (i : S.Index) : S.pole i + S.long=S.edge i := by simp [pole,edge,origin,fromMark,fromGap]; abel
lemma last_edge (i : S.Index) : S.edge i + S.short=S.pole (i+1) := by
 rw [← last_pole,add_assoc,← Nat.cast_add,S.total]; simp [pole,origin,add_assoc]

def twinsGap (x : Per s) : S.Index := owner S.grid S.fromGap x
def twinsBand (x : Per s) : S.Index := owner S.grid S.fromMark x

theorem band_dist (i : S.Index) (a : ℕ) (ha : a ≤ S.grid.count.val) : along (S.pole i) (native S.grid S.fromMark i a)=a := along_add _ (ha.trans_lt S.count_lt)
theorem gap_dist (i : S.Index) (a : ℕ) (ha : a ≤ S.grid.count.val) : along (S.edge i) (native S.grid S.fromGap i a)=a := along_add _ (ha.trans_lt S.count_lt)

lemma band_heir {i : S.Index} {x : Per s} (h : along (S.pole i) x ≤ S.long) : S.twinsBand x=i := by convert owner_native S.grid S.fromMark i (h.trans_lt S.long_lt) using 1; rw [native,show origin S.grid S.fromMark i=S.pole i from rfl,add_along]; rfl
lemma gap_heir {i : S.Index} {x : Per s} (h : along (S.edge i) x ≤ S.short) : S.twinsGap x=i := by convert owner_native S.grid S.fromGap i (h.trans_lt S.short_lt) using 1; rw [native,show origin S.grid S.fromGap i=S.edge i from rfl,add_along]; rfl
lemma band_disjoint {i j : S.Index} (h : i ≠ j) : Disjoint (S.band i) (S.band j) := disjoint_left.mpr fun _ a b => h ((S.band_heir (mem_strip.mp a)).symm.trans (S.band_heir (mem_strip.mp b)))
lemma gap_disjoint {i j : S.Index} (h : i ≠ j) : Disjoint (S.gap i) (S.gap j) := disjoint_left.mpr fun _ a b => h ((S.gap_heir (mem_strip.mp a)).symm.trans (S.gap_heir (mem_strip.mp b)))

/-- Horizontal links at every time. Share faces here. For an exact partition excluding
right endpoints use time and this normal-ownership rule instead. -/
theorem edge_from (x : Per s) :
    along (S.pole (S.twinsBand x)) x < S.long ∨ along (S.edge (S.twinsBand x)) x < S.short := by
 let a := S.twinsBand x
 let i := stamp S.grid S.fromMark x
 have hi := i.isLt
 have hg : S.pole a + i.val = x := native_stamp ..
 change along (S.pole a) x < _ ∨ along (S.edge a) x < _
 by_cases hx : i.val < S.long
 · left; rw [← hg,along_add]; exact hx; exact hi.trans S.count_lt
 right; nth_rw 1 [← hg,← last_pole]
 rw [offset_dist (S.pole a) (by omega) (by exact lt_of_le_of_lt (Nat.sub_le ..) (hi.trans S.count_lt))]; have h := S.total; omega

lemma within_mark {x : Per s} {i : S.Index} {a : ℕ} (h : along (S.edge i) x=a) (ha : a < S.short) : along (S.pole i) x=S.long+a := by
 have hu := add_along (S.edge i) x; rw [h,← last_pole,add_assoc,← Nat.cast_add] at hu
 rw [← hu,along_add]; have := S.total; have := S.count_lt; omega
lemma edge_disjoint {x : Per s} {i j : S.Index} (h : along (S.pole i) x < S.long) (u : along (S.edge j) x < S.short) : False := by
 have hx : along (S.pole j) x=S.long+along (S.edge j) x := S.within_mark rfl u
 have ht := S.total; have hz := S.band_heir h.le
 have hg : owner S.grid S.fromMark x=j := by
   have he : along (S.pole j) x < S.grid.count.val := by omega
   convert owner_native S.grid S.fromMark j he using 1; rw [native, show origin S.grid _ j=S.pole j from rfl,add_along]
 have he : i=j:=hz.symm.trans hg
 rw [he] at h; omega
end Strips

/-- Labels attach to even- and odd-indexed bands (cyclic). -/
def dirichlet (s : Side) (h : Even s.val) (x : Per s) : Prop := ZMod.castHom (even_iff_two_dvd.mp h) (ZMod 2) x = 0
@[simp] theorem dirichlet_step (h : Even s.val) (x : Per s) : dirichlet s h (x+1) ↔ ¬dirichlet s h x := by
 unfold dirichlet; rw [map_add,map_one]; exact (show ∀ x : ZMod 2,x+1=0 ↔ ¬x=0 by decide) _
lemma dirichlet_even (h : Even s.val) (x : ℕ) : dirichlet s h x ↔ Even x := by
 induction x with
 | zero => simp [dirichlet]
 | succ i ih => rw [Nat.cast_add_one,dirichlet_step,ih,Nat.even_add_one]

/-- Strips used in the manuscript, including grid, lengths and margins. Mesh provisions
for interpolation and other fine size qualifications are specified separately. -/
structure Bands (s L : Side) (w₀ P : ℕ) extends Strips s where
  gap_len : short = 2*L.val + 2*w₀
  band_len : long + 2*w₀ = P
  left : pivot = w₀
  multiplesW : 2*L.val ∣ w₀
  rP : ℕ
  powP : P = 2^rP * (2*L.val)
  rP_pos : 1 ≤ rP
  dyadicH : 2^(rP+1) ∣ q.val
  slotsH : 2*P ∣ s.val
namespace Bands
variable {L : Side} {w₀ P : ℕ} (S : Bands s L w₀ P)
lemma even_count : Even S.q.val := even_iff_two_dvd.mpr (dvd_trans (by simp : 2 ∣ 2^(S.rP+1)) S.dyadicH)
lemma lengths : P + 2*L.val=S.grid.count.val := by have := S.band_len; have := S.total; have := S.gap_len; omega
lemma multipleT : 2*L.val ∣ S.grid.count.val := S.lengths ▸ dvd_add (S.powP ▸ dvd_mul_left ..) (dvd_refl _)
lemma small : P < S.grid.count.val := by have := S.lengths; have : 0<L.val := L.property; omega
include S
lemma smaller : 2*P ≤ s.val := by have := S.small; have := S.count_small; omega
abbrev blank_p (i : S.Index) := base S.grid i
abbrev subslot (i : S.Index) := strip (S.blank_p i) P
lemma left_shift (i : S.Index) : S.pole i=S.blank_p i+w₀ := by change (S.pivot:Per s) + _ = _; rw [S.left]; exact add_comm .. 
lemma order_in {i : S.Index} {x : Per s} (h : along (S.pole i) x ≤ S.long) : w₀ ≤ along (S.blank_p i) x ∧ along (S.blank_p i) x + w₀ ≤ P := by
 have he := add_along (S.pole i) x
 have hk := S.band_len
 -- rw left shift at single occurrence
 nth_rw 1 [left_shift] at he
 rw [add_assoc,← Nat.cast_add] at he
 have hx : along (S.blank_p i) x=w₀ + along (S.pole i) x := by
   simpa only [he] using along_add (S.blank_p i) (by have := S.small.trans S.count_lt; omega : w₀+along (S.pole i) x < s.val)
 omega
lemma subslot_gap {i : S.Index} {x : Site s} (h : x ∈ S.band i) :
    x ∈ S.subslot i ∧ w₀ ≤ delta1 s (time x) (S.blank_p i) ∧ w₀ ≤ delta1 s (S.blank_p i + P) (time x) := by
 let d := along (S.blank_p i) (time x)
 have ⟨ha,hb⟩ := S.order_in (mem_strip.mp h)
 refine ⟨mem_strip.mpr (by omega),?_,?_⟩
 · rw [delta_eq]; have := S.smaller; omega
 rw [delta_eq]; have he : along (time x) (S.blank_p i + (P : Per s))= P-d := by
   conv_lhs => arg 1; rw [← add_along (S.blank_p i) (time x)]
   unfold d; exact offset_dist _ (by omega) (by have := S.smaller; have := S.count_lt; have := S.small; omega)
 change w₀ ≤ min _ (_ - _); rw [he]; unfold d; have := S.smaller; omega
end Bands

/- Boundary alignments, no node overlap ambiguities. -/
abbrev modTwo (N : Side) := ZMod.castHom (show 2 ∣ (More N).val by rw [natM]; simp) (ZMod 2)
lemma residue_node (x : Site N) (i : Axis) : modTwo N (node x i)=1 := by
 unfold node
 rw [Ratio.root_embed, Pi.add_apply, base_apply,map_add, Pi.one_apply,map_one]
 nth_rw 1 [← ZMod.natCast_zmod_val (x i)]
 rw [base_nat,map_mul,map_natCast,map_natCast]; change (↑(2:ℕ) : ZMod 2) * _ + _ = _
 rw [ZMod.natCast_self]; simp
namespace Bands
variable {L : Side} {w₀ P : ℕ} (S : Bands (More N) L w₀ P)
lemma pole_even (i : S.Index) : modTwo N (S.pole i)=0 := by
 rw [left_shift]; unfold blank_p; rw [← ZMod.natCast_zmod_val i]
 rw [map_add, base_nat,map_mul,map_natCast,map_natCast,map_natCast]
 simp only [(ZMod.natCast_eq_zero_iff _ 2).mpr (dvd_trans (dvd_mul_right ..) S.multiplesW), (ZMod.natCast_eq_zero_iff _ 2).mpr (dvd_trans (dvd_mul_right ..) S.multipleT),zero_mul,add_zero]
lemma edge_even (i : S.Index) : modTwo N (S.edge i)=0 := by
 have h : 2∣ S.long:=by
   apply (Nat.dvd_add_iff_left (show 2∣ (2*w₀:ℕ) from dvd_mul_right ..)).mpr
   rw [S.band_len]; exact S.powP ▸ dvd_mul_of_dvd_right (dvd_mul_right ..) _
 rw [← S.last_pole,map_add,S.pole_even,map_natCast,(ZMod.natCast_eq_zero_iff _ 2).mpr h,add_zero]
lemma node_not_pole (x : Site N) (i : S.Index) : time (node x) ≠ S.pole i := by
 intro e; exact one_ne_zero (by rw [← residue_node x 0, show node x 0=_ from e, S.pole_even] : (1: ZMod 2)=0)
lemma node_not_edge (x : Site N) (i : S.Index) : time (node x) ≠ S.edge i := by
 intro e; exact one_ne_zero (by rw [← residue_node x 0, show node x 0=_ from e,S.edge_even] : (1: ZMod 2)=0)
lemma node_separator (x : Site N) (i j : S.Index) (h : node x∈ S.band i) (u : node x∈ S.gap j) : False := by
 apply S.edge_disjoint
 exact lt_of_le_of_ne (mem_strip.mp h) (fun v => S.node_not_edge x i ((add_along ..).symm.trans (v.symm ▸ S.last_pole i)))
 exact lt_of_le_of_ne (mem_strip.mp u) (fun v => S.node_not_pole x (j+1) ((add_along ..).symm.trans (v.symm ▸ S.last_edge j)))
end Bands
end YM.CF.BProof
