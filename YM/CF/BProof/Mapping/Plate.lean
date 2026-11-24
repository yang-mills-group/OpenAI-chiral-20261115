import YM.CF.BProof.Mapping.Shadow

/- connectivity for a block patch (full sup neighbor radius rectangle). Use step in
 AXES, not sup-consecutive. Even when c side wraps `grow` connects along to base's ball.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mapping
open Lattice Finset Filter Function Grid Circle Cube
open scoped Topology BigOperators Classical
namespace Plate
variable {n:ℕ}{s c: Side}(g:Ratio c s)(x y:Cubic n s)

-- coordinate sets with relation as connectivity any arc both pos. use along a→b either direction. general relation Rectangle S-coordinate, preserving Φ on edges enough.
def Adj (x y:Per s) := x+1=y∨y+1=x
def Link (A:Finset (Per s)) (x y:Per s) := Relation.ReflTransGen (fun i j => i∈ A ∧ j∈ A ∧ Adj i j) x y
variable {A:Type*}(S: Fin n → Finset (Per s))(f:Cubic n s→A)
lemma cycle (p:Per s)(k:ℕ)(A:Finset (Per s))(h:∀ i:ℕ,i≤k→ p+i∈ A): Link A p (p+k):= by
 induction k with
 |zero=> rw [Nat.cast_zero,add_zero]; exact Relation.ReflTransGen.refl
 |succ i ih=> apply Relation.ReflTransGen.tail (ih (fun n k=> h n (by omega))); exact ⟨h i (by omega),h (i+1) le_rfl,Or.inl (by rw [Nat.cast_add_one,add_assoc])⟩
lemma sym {S:Finset (Per s)}{x y}(h:Link S x y): Link S y x:=by induction h with |refl=>exact Relation.ReflTransGen.refl|tail _ p ih=> exact Relation.ReflTransGen.head ⟨p.2.1,p.1,p.2.2.symm⟩ ih

def Bed (x:Cubic n s) := ∀ i,x i∈ S i
def Line := ∀ x i,Bed S x→ Bed S (slide x i) → f x=f (slide x i)
lemma single (i: Fin n)(w:Bed S x){p q:Per s}(h:Link (S i) p q)(u:Line S f): f (update x i p)=f (update x i q):=by
 let y(p): Cubic n s:=update x i p; have he(p)(h:p∈ S i) : Bed S (y p):=by intro j; by_cases v:j=i; subst j; simp only [y,update_self]; exact h; simp only [y,update_of_ne v]; exact w j
 have hx (p q:Per s)(h:p∈S i)(u':q∈ S i)(h':p+1=q): f (y p)=f (y q):=by
   have hz: Grid.slide (y p) i=y q:=by unfold y Grid.slide; rw [Function.update_self,h',Function.update_idem]
   exact hz ▸ u _ i (he p h) (hz.symm ▸ he q u')
 induction h with |refl=>rfl|tail _ p ih=> exact ih.trans (p.2.2.elim (fun v=> hx _ _ p.1 p.2.1 v) (fun v=>(hx _ _ p.2.1 p.1 v).symm))
lemma connect (u:∀ i,∀ x∈ S i,∀ y∈ S i,Link (S i) x y)(v:Line S f)(hx:Bed S x)(hy:Bed S y) : f x=f y:=by
 have hh (I: Finset (Fin n))(z:Cubic n s) (h:Bed S z)(e:∀ i,i∉I→z i=x i): f z=f x:=by
   induction I using Finset.induction_on generalizing z with
   |empty=> congr; ext i; exact e i (notMem_empty _)
   |insert i I p ih=>
      let f'(p: Per s):=update z i p; let t:= f' (x i); have a:t i=x i:=Function.update_self ..; have b(j:Fin n)(hx:j≠i): t j=z j:=Function.update_of_ne hx _ _
      have ht:f z=f t:= by simpa only [t,f',Function.update_eq_self] using single z S f i h (u i _ (h i) _ (hx i)) v
      refine ht.trans (ih t (fun j=>?_) (fun j e=>?_)); by_cases k:j=i; exact k ▸ a.symm ▸ (hx i); rw [b j k]; exact h j -- tune
      by_cases k:j=i; exact k ▸ a; rw [b j k]; exact ‹∀ j,j∉ insert i I → z j=x j› j (by simp [k,e]) -- name binder conflict
 exact (hh univ y hy (by simp)).symm

-- Lift any c along step path, even leaves of elder patches. restrict H accordingly
variable (T:Finset (Per c))
def unitP (T: Finset (Per c)) := univ.filter fun i=>block g i∈ T
lemma baseP {i:Per c}(p:i∈ T): base g i∈ unitP g T:=by
 apply mem_filter.mpr; simp only [mem_univ,true_and]; have hx:block g (base g i)=i:=by simpa using block_add g i (ha:=g.count.property); -- tune
 rw [hx]; exact p
lemma spin (i:Per c)(p:i∈ T)(l:Fin g.count.val): Link (unitP g T) (base g i) (base g i+l.val):=by
 apply cycle; intro t ht; apply mem_filter.mpr; simp [block_add g i (ht.trans_lt l.isLt),p]
lemma links {x y:Per c}(p:Link T x y): Link (unitP g T) (base g x) (base g y):=by
 have h(p q:Per c)(e:p∈T)(v:q∈T)(k:p+1=q): Link (unitP g T) (base g p) (base g q):=by
   have hx : base g q=base g p+g.count.val:=by rw [←k]; simp
   rw [hx]; apply cycle; intro i h; rcases h.eq_or_lt with h|h; rw [h,← hx]; exact baseP g T v
   apply mem_filter.mpr; rw [block_add g _ h]; exact ⟨mem_univ _,e⟩
 induction p with | refl=> exact Relation.ReflTransGen.refl|tail _ p ih=> exact ih.trans (p.2.2.elim (h _ _ p.1 p.2.1) (fun v=> sym (h _ _ p.2.1 p.1 v)))
lemma elevator (p:∀ x∈T,∀ y∈ T, Link T x y) {x y:Per s}(h:x∈unitP g T)(v:y∈unitP g T): Link (unitP g T) x y:=by
 have hh(x:Per s)(h:x∈unitP g T): Link (unitP g T) (base g (block g x)) x:=by simpa only [glue_block] using spin g T (block g x) (mem_filter.mp h).2 (part g x)
 exact ((sym (hh x h)).trans (links g T (p _ (mem_filter.mp h).2 _ (mem_filter.mp v).2))).trans (hh y v)

def room (a:Per c)(r:ℕ) := univ.filter fun x=> δ a x≤r
lemma spaces (a:Per c)(r:ℕ)(p:Per c)(h:p∈ Plate.room a r): Link (Plate.room a r) a p:=by
 let T:=Plate.room a r; rcases (δle a r p).1 (mem_filter.mp h).2 with h|hp
 · rw [← add_along a p]; -- avoid rewriting in T def `p` no
   apply cycle; intro i hi; exact mem_filter.mpr ⟨mem_univ _, (Posts.castδ a i).trans (hi.trans h)⟩
 apply sym; change Link T p a; have he:p+along p a=a:=add_along ..; refine he ▸ cycle p (along p a) T ?_; intro i hi; apply mem_filter.mpr; refine ⟨mem_univ _, ((Cube.d_sym ..).trans_le ?_ )⟩; have hx : p+i+ ((along p a-i:ℕ): Per c)=a:=by rw [add_assoc,← Nat.cast_add,Nat.add_sub_of_le hi, he]
 have h:=Posts.castδ (p+(i:Per c)) (along p a-i); rw [hx] at h; exact h.trans (Nat.le_trans (Nat.sub_le ..) hp)
variable (r:ℕ)
lemma slots (a:Cubic n c) : Bed (fun i=> unitP g (room (a i) r)) x ↔ Grid.dist a (elder g x)≤r:=by
 unfold Bed unitP; rw [Grid.dist_le]; simp only [mem_filter,room,mem_univ,true_and]; rfl
lemma ticket (a:Cubic n c)(v:Grid.dist a (elder g x)≤r)(u:Grid.dist a (elder g y)≤r)(T:∀ x i,Grid.dist a (elder g x)≤r → Grid.dist a (elder g (slide x i)) ≤r → f x=f (slide x i)): f x=f y:= connect x y (fun i=>unitP g (room (a i) r)) f (fun i x hx y hy=> elevator _ _ (fun a b i v=> Relation.ReflTransGen.trans (sym (spaces _ _ _ b)) (spaces _ _ _ v)) hx hy) (fun x i a b=> T _ _ ((slots ..).1 a) ((slots ..).1 b)) ((slots ..).2 v) ((slots ..).2 u) -- tune order
end Plate
end YM.CF.BProof.Mapping
