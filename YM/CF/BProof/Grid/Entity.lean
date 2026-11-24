import YM.CF.BProof.Grid.Vertex

/-! Skeleton geometry. No small-torus uses: assume coarse period≥4. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Grid
open Lattice Function Set Finset
variable {n : ℕ} {c s : Side}
-- use pair product for equality convenience, #(Fin n→Bool)
def Entity (n : ℕ) (c : Side) := Cubic n c × Finset (Fin n) deriving Fintype, DecidableEq
namespace Entity
-- shape and anchors
variable (p : Entity n c)
abbrev home := Prod.fst (show Cubic n c×Finset (Fin n) from p)
abbrev axes := Prod.snd (show Cubic n c×Finset (Fin n) from p)
def mk (x : Cubic n c) (v : Finset (Fin n)) : Entity n c:= (x,v)
@[simp] lemma home_mk (x : Cubic n c) (v : Finset (Fin n)) : (mk x v).home=x:=rfl
@[simp] lemma axes_mk (x : Cubic n c) (v : Finset (Fin n)) : (mk x v).axes=v:=rfl
@[ext] lemma ext {p q : Entity n c}(h : p.home=q.home)(k:p.axes=q.axes):p=q:=Prod.ext h k
abbrev dim := p.axes.card

def wall (i : Fin n)(high : Bool) := mk (if high then slide p.home i else p.home) (p.axes.erase i)
@[simp] lemma wall_dim {i}(v:i∈p.axes)(x:Bool) : (p.wall i x).dim+1=p.dim := Finset.card_erase_add_one v

variable (g : Ratio c s)
def first := grow g p.home
def len (i : Fin n) : ℕ := if i∈p.axes then g.count.val else 0
lemma width (i) : p.len g i≤g.count.val:=by unfold len; split_ifs <;> omega
lemma count_small (g : Ratio c s) (hc : 4≤ c.val):4*g.count.val ≤ s.val:=by rw [g.exact_size]; exact Nat.mul_le_mul_right _ hc
lemma count_tiny (hc : 4≤ c.val): g.count.val+1<s.val:=by have := count_small g hc; have : 0<g.count.val:=g.count.property; omega
lemma narrow (hc : 4≤ c.val)(i) : p.len g i<s.val:=by have := p.width g i; have := count_tiny g hc; omega

def coord (x : Cubic n s)(i : Fin n):= along (p.first g i) (x i)
abbrev Tick := Fin n→ℕ
def put (a : Tick (n:=n)) : Cubic n s := fun i=> p.first g i + a i
def Mem (x : Cubic n s) := ∀ i,p.coord g x i ≤ p.len g i
def Proper (x : Cubic n s) : Prop:= p.Mem g x ∧ ∀ i∈p.axes, 0<p.coord g x i ∧ p.coord g x i<p.len g i

def Corner (x : Cubic n s) := ∀ i,p.coord g x i=0 ∨ p.coord g x i=p.len g i

lemma corner_mem {x : Cubic n s}(h:p.Corner g x):p.Mem g x:= fun i=> by have := h i; omega

instance (x) : Decidable (p.Mem g x):=by unfold Mem; infer_instance
instance (x) : Decidable (p.Proper g x):=by classical infer_instance

lemma coord_zero {x : Cubic n s} {i: Fin n}: p.coord g x i=0 ↔ p.first g i=x i:=along_zero
@[simp] lemma put_zero : p.put g 0=p.first g:=by ext; simp [put]
@[simp] lemma coord_first : p.coord g (p.first g)=0:=funext fun i=> along_self _
lemma mem_first : p.Mem g (p.first g):=fun i=> by rw [coord_first]; exact Nat.zero_le _
@[simp] lemma put_coord (x : Cubic n s) : p.put g (p.coord g x)=x:= funext fun i=>add_along ..
lemma coord_put (hc : 4≤ c.val) {a : Tick (n:=n)} (h: a ≤ p.len g) : p.coord g (p.put g a)=a:=funext fun i=> along_add _ ((h i).trans_lt (p.narrow g hc i))
lemma mem_put (hc : 4≤ c.val){a} (h:a ≤ p.len g):p.Mem g (p.put g a):=fun i=> by rw [coord_put p g hc h]; exact h i
lemma vtx (x : Cubic n c) {y : Cubic n s} : (mk x ∅).Mem g y ↔ grow g x=y := by
 change (∀ i,along _ _ ≤ _) ↔ _; simp only [len,axes_mk,Finset.notMem_empty,↓reduceIte, Nat.le_zero,along_zero, funext_iff]; rfl

lemma coord_update (x : Cubic n s)(i : Fin n)(a : Per s) : p.coord g (update x i a) = update (p.coord g x) i (along (p.first g i) a):=by
  ext j; by_cases h:j=i <;> try subst i
  all_goals simp_all [coord]
lemma put_step (a : Tick (n:=n))(i : Fin n) : p.put g (update a i (a i+1)) = slide (p.put g a) i:=by
  ext j; by_cases h:j=i <;> try subst i
  all_goals simp_all [put,slide,_root_.add_assoc]
lemma coord_step (x:Cubic n s)(hx:p.Mem g x) (i:Fin n)(hc:4≤c.val) : p.coord g (slide x i) = update (p.coord g x) i (p.coord g x i+1):=by
 have h:= hx i; have u:= p.width g i
 rw [slide,coord_update,along_succ (by have := count_tiny g hc; change p.coord g x i+1<s.val; omega)]; rfl

lemma mem_wall (hc:4 ≤ c.val)(x:Cubic n s) {i:Fin n}(h:i ∈ p.axes)(high:Bool) :
    (p.wall i high).Mem g x ↔ p.Mem g x ∧ (p.coord g x i=if high then p.len g i else 0) := by
 let q:=p.wall i high
 have he : (q.coord g x i ≤ q.len g i) ↔ q.first g i = x i:= by rw [len, if_neg (show i∉q.axes from Finset.notMem_erase i _), Nat.le_zero,coord_zero]
 have ha:q.first g i=p.first g i+(↑(if high then p.len g i else 0) : Per s):=by unfold len; rw [if_pos h]; cases high <;> simp [q,wall,first,grow]
 have hp : (if high then p.len g i else 0)<s.val:= by have := p.narrow g hc i; split <;> omega
 have hI:q.first g i=x i ↔ p.coord g x i=if high then p.len g i else 0:=⟨fun H=>by rw [coord,← H,ha,along_add _ hp],fun H=>by rw [ha,←H]; exact add_along ..⟩
 have hu(j)(hq:j≠i):q.coord g x j=p.coord g x j ∧ q.len g j=p.len g j:=by cases high <;> simp_all [coord,len,q,wall,first,grow,slide] -- tune
 constructor
 · intro g; have hv:= hI.mp (he.mp (g i)); refine ⟨fun j=> ?_,hv⟩; by_cases h:j=i; rw [h,hv]; split <;> omega; have hh := hu j h; rw [← hh.1,← hh.2]; exact g j -- tune layout
 rintro ⟨hz,hp⟩ j; by_cases h:j=i; rw [h]; exact he.mpr (hI.mpr hp); change q.coord g x j ≤ q.len g j; rw [(hu j h).1,(hu j h).2]; exact hz j

lemma smaller (hc:4≤ c.val) {x : Cubic n s} (h:p.Mem g x) (u:¬p.Proper g x): ∃ i∈p.axes,∃ b,(p.wall i b).Mem g x:=by
 classical
 unfold Proper at u; rw [and_iff_right h] at u; push Not at u; obtain ⟨i,g',v⟩:=u; by_cases e: p.coord g x i=0
 · exact ⟨i,g',false,(p.mem_wall g hc x g' false).mpr ⟨h,e⟩⟩
 have he:0<p.coord g x i:=Nat.pos_of_ne_zero e; exact ⟨i,g',true,(p.mem_wall g hc x g' true).mpr ⟨h,(h i).antisymm (v he)⟩⟩

lemma diameter (x : Cubic n s)(hx:p.Mem g x):dist x (p.first g)≤g.count.val:=dist_le.mpr fun i=> (delta_eq ..).trans_le ((min_le_left ..).trans ((hx i).trans (p.width g i)))

def chief (x:Cubic n s):= mk (elder g x) (univ.filter fun i=>0<(here g x i).val)
lemma zero_proper (hc:4 ≤ c.val)(x:Cubic n s) : (chief g x).Proper g x := by
 let p := chief g x; have he(i) : p.coord g x i=(here g x i).val:=by
   unfold coord; rw [show x i = p.first g i+ (here g x i).val from (glue_block g (x i)).symm] -- rhs rewrite issue
   exact along_add _ ((here g _ _).isLt.trans (by have := count_tiny g hc; change _ < s.val; omega))
 have hi (i) : i∈p.axes ↔ 0<(here g x i).val := by simp [p,chief]
 refine ⟨fun i=>?_,fun i h=>?_⟩
 · change p.coord _ _ _ ≤ p.len g i; have hv := he i; unfold len; split
   next h=> exact hv.trans_le (here g x i).isLt.le
   next h=> rw [hi] at h; omega
 change 0<p.coord g x i ∧ p.coord g x i<p.len g i; rw [he,len,if_pos h]; exact ⟨(hi i).mp h,(here g x i).isLt⟩
lemma chosen (x:Cubic n s)(h:p.Proper g x): chief g x=p:=by
 have he(i): p.coord g x i<g.count.val:=by by_cases e:i∈p.axes; exact (h.2 i e).2.trans_le (p.width g i); have u:= h.1 i; rw [len,if_neg e] at u; exact lt_of_le_of_lt u g.count.property
 have ht(i) : (here g x i).val=p.coord g x i:=by
    have hi: native g 0 (p.home i) (p.coord g x i)=x i:=by change _; rw [native,origin,zero_add]; exact add_along ..
    have he := stamp_native g 0 (p.home i) (he i); rw [hi] at he; simpa only [stamp,off,sub_zero,here] using he
 refine Entity.ext (funext (fun i=> (block_eq g (x i) _).mpr ((mem_tile g _).mpr (he i)))) ?_
 ext1 i; have hp:=ht i; simp only [chief,axes_mk,mem_filter,Finset.mem_univ,true_and]; constructor
 · intro u; by_contra hx; have hz:= h.1 i; rw [len, if_neg hx] at hz; omega
 intro u; rw [hp]; exact (h.2 i u).1
end Entity
end YM.CF.BProof.Grid
