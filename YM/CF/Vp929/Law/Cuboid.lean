import YM.Lattice.Box
/-! Optional VolumeRate with co-locality-in-law for the Cape; per-size cubical version of the cell construction. -/
set_option autoImplicit false
set_option maxHeartbeats 450000
noncomputable section
namespace YM.CF.VolumeCape
open Lattice Finset
open scoped Classical
@[ext]
structure Wall where
 a:ℤ
 b:ℤ
 e:a ≤ b
abbrev Rooms:=Axis → Wall
namespace Wall
variable {x y z:Wall} {a b:ℤ}
def win (x:Wall) : Prop := x.a < x.b
-- closed comparison
instance : PartialOrder Wall where
 le x y:= y.a ≤ x.a ∧ x.b ≤ y.b
 le_refl _:= ⟨le_rfl,le_rfl⟩
 le_trans _ _ _ h g :=⟨g.1.trans h.1,h.2.trans g.2⟩
 le_antisymm _ _ h t:= Wall.ext (le_antisymm t.1 h.1) (le_antisymm h.2 t.2)
abbrev lone (a:ℤ):Wall:= ⟨a,a,le_rfl⟩
lemma full (v:x ≤ y): y.a ≤ x.a∧x.b≤ y.b:=v
lemma seen (v:lone a ≤ x):x.a ≤ a∧ a ≤ x.b:=v
def tips (x:Wall)(a:ℤ):Prop:= x.a=a ∨ x.b=a
def cabin(x y:Wall):Prop:= x ≤ y ∧ (y.win → x.a < y.b ∧ y.a < x.b)
def Tiny(x:Wall):Prop:= x.b≤ x.a+1
lemma tipBox (v:x.tips a): lone a≤x:=by obtain rfl|rfl:=v; exact ⟨le_rfl,x.e⟩; exact ⟨x.e,le_rfl⟩
lemma stay (h:¬ y.win) (t:x ≤ y) : x=y:=by obtain ⟨u,v⟩:=full t; unfold win at h; apply Wall.ext <;> have a:=x.e <;> have b:=y.e <;> omega
lemma up (p:x ≤ y)(e:x.win): y.win:=lt_of_le_of_lt (full p).1 (lt_of_lt_of_le e (full p).2)
lemma cabin_win(p:x ≤ y)(e:x.win): x.cabin y:=⟨p,fun _=>⟨lt_of_lt_of_le e (full p).2,lt_of_le_of_lt (full p).1 e⟩⟩
lemma cabin_lift (t:z.cabin y)(e:z ≤ x)(p:x ≤ y): x.cabin y:= ⟨p,fun v=>⟨lt_of_le_of_lt (full e).1 (t.2 v).1,(t.2 v).2.trans_le (full e).2⟩⟩
lemma cabin_home(x:Wall):x.cabin x:=⟨le_rfl,fun p=>⟨p,p⟩⟩
end Wall
namespace Rooms
variable {x y z:Rooms}{a b:Cover}
def Tiny (x:Rooms):Prop:= ∀ i,(x i).Tiny
def inside(x y:Rooms):Prop:= ∀ i,(x i).cabin (y i)
abbrev here(a:Cover):Rooms:=fun i=> Wall.lone (a i)
def doors(x:Rooms):Finset Axis:= univ.filter fun i=> (x i).win
def dim(x:Rooms):ℕ:=x.doors.card
def meets(x y:Rooms):Prop:=∃ t:Cover,here t ≤ x ∧ here t ≤ y
def Corner(x:Rooms)(p:Cover):Prop:=∀ i,(x i).tips (p i)
abbrev foot (x:Rooms):Cover:=fun i=>(x i).a
abbrev headB(x:Rooms):Cover:=fun i=>(x i).b
lemma corners₁(x:Rooms):Corner x x.foot:=fun i=>Or.inl rfl
lemma corners₂(x:Rooms):Corner x x.headB:=fun i=> Or.inr rfl
lemma mem_corner (h:x.Corner a):here a ≤ x:= fun i=>Wall.tipBox (h i)
lemma touch (e:z ≤ x)(t:z ≤ y):x.meets y:=⟨z.foot,(mem_corner z.corners₁).trans e,(mem_corner z.corners₁).trans t⟩
lemma meet_comm (e:x.meets y):y.meets x:= let ⟨a,b,v⟩:=e; ⟨a,v,b⟩
lemma intro_door {i:Axis}: i∈x.doors↔(x i).win:= by simp only [doors,mem_filter,mem_univ,true_and]
theorem dim_le (p:x ≤ y) : x.doors ⊆ y.doors:= fun i v=> intro_door.2 (Wall.up (p _) (intro_door.1 v))
lemma win_of_dim (p:x ≤ y) (e:x.dim=y.dim) :∀ i,(x i).win ↔ (y i).win:=by
 have h:= eq_of_subset_of_card_le (dim_le p) (e.ge); intro i; rw [←intro_door,←intro_door,h]
lemma foot_in(x:Rooms):here x.foot ≤ x:= mem_corner x.corners₁
lemma head_in(x:Rooms):here x.headB ≤ x:= mem_corner x.corners₂
lemma place (e:inside x y): x ≤ y:=fun i=> (e i).1
lemma here_tiny (a:Cover):Tiny (here a):=fun i=>le_trans le_rfl (show a i≤ a i+1 from by omega)
lemma inside_lift (t: inside z y)(e:z ≤ x)(p:x ≤ y): inside x y:=fun i=>Wall.cabin_lift (t i) (e i) (p i)
def Plane(x y:Rooms):Prop:= x.doors=y.doors ∧ ∀ i,¬ (x i).win → x i=y i
protected lemma Plane.refl(x:Rooms): Plane x x:=⟨rfl,fun _ _=> rfl⟩
protected lemma Plane.win(t:Plane x y)(i): (x i).win ↔ (y i).win := by simp only [←intro_door,t.1]
protected lemma Plane.symm(t:Plane x y): Plane y x:=⟨t.1.symm,fun i e=>(t.2 i (mt (t.win i).mp e)).symm⟩
protected lemma Plane.trans (v:Plane x y)(t:Plane y z): Plane x z:=⟨v.1.trans t.1,fun i e=>(v.2 i e).trans (t.2 i (mt (v.win i).mpr e))⟩
protected lemma Plane.dim(v:Plane x y): x.dim=y.dim:=congrArg Finset.card v.1
lemma plane_of_doors(h:x≤y)(v:x.doors=y.doors): x.Plane y:=⟨v,fun i e=> Wall.stay (by simpa only [←intro_door,←v] using (show i∉x.doors from (mt intro_door.1 e))) (h i)⟩
lemma plane_of_dim (h:x≤y)(v:x.dim=y.dim):x.Plane y:=plane_of_doors h (eq_of_subset_of_card_le (dim_le h) v.ge)
lemma inside_of_plane (h:x≤y)(p:Plane x y): inside x y:= fun i=> ⟨h i,fun v=>(Wall.cabin_win (h i) ((p.win i).2 v)).2 v⟩
lemma pad (x:Rooms)(t:Tiny y)(e:y≤x) :∃ z:Rooms,Tiny z ∧ y≤z∧ z≤x∧ z.Plane x:=by
 have h(i:Axis):∃ w:Wall,w.Tiny∧ y i≤ w ∧ w ≤ x i ∧ ((x i).win → w.win):=by
   by_cases v:(x i).win; swap; · exact ⟨_,t i,le_rfl,e i,fun k=>(v k).elim⟩
   let a:= (y i).a; have h: (y i).b ≤ a+1:=t i; by_cases z:a=(x i).b
   · obtain ⟨r,s⟩:= Wall.full (e i); change (x i).a < (x i).b at v; refine ⟨⟨a-1,a,by omega⟩,(by change a ≤ a-1+1; omega),⟨show a-1 ≤ a from by omega,s.trans_eq z.symm⟩,⟨show (x i).a ≤ a-1 from by omega,z.le⟩,fun _=> show a-1<a from by omega⟩
   have hz:a ≤ (x i).b:=(y i).e.trans (Wall.full (e i)).2; exact ⟨⟨a,a+1,by omega⟩,le_rfl,⟨le_rfl,h⟩,⟨(Wall.full (e i)).1,show a+1 ≤ _ from (by omega)⟩,fun _=> show a<a+1 from by omega⟩
 choose w p v r s using h; let z:Rooms:=w; exact ⟨z,p,v,r,plane_of_doors r (Finset.Subset.antisymm (dim_le (show z ≤ x from r)) (fun i v=> intro_door.2 (s i (intro_door.1 v))))⟩
-- transport rectangle bounds local
abbrev bounded(x:Rooms)(r:ℕ):Prop:=∀ i,(x i).b ≤ (x i).a+r
lemma bounded_of_le {r:ℕ}(p:x ≤ y)(t:y.bounded r):x.bounded r:= fun i=> (Wall.full (p i)).2.trans ((t i).trans (add_le_add_left (Wall.full (p i)).1 _))
def Range (r:ℕ)(a b:Cover) :Prop:=∀ i,(a i-b i).natAbs≤ r
lemma Range.symm{r:ℕ}(p:Range r a b):Range r b a:= fun i=>by have h:=p i; rw [←neg_sub (a i), Int.natAbs_neg]; exact h
lemma Range.trans{r t:ℕ}{c:Cover}(p:Range r a b)(q:Range t b c):Range (r+t) a c:=fun i=>by rw [← sub_add_sub_cancel (a i) (b i)]; exact le_trans (Int.natAbs_add_le ..) (Nat.add_le_add (p i) (q i))
lemma Range.mono{r t:ℕ}(p:Range r a b)(q:r≤t): Range t a b:=fun i=>(p i).trans q
protected lemma Range.refl(r:ℕ)(x:Cover):Range r x x:= fun i=>by simp
lemma within {r:ℕ}(h:x.bounded r)(p:here a ≤ x)(t:here b ≤ x): Range r a b:= by intro i; obtain ⟨u,v⟩:=Wall.seen (p i); obtain ⟨e,f⟩:=Wall.seen (t i); have hb:= h i; omega
end Rooms
end YM.CF.VolumeCape
