import YM.CF.BProof.Grid.Schedule
import YM.CF.BProof.Grid.Bill

/-! Micro reads through hierarchy. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Grid.Blend
open Function Lattice SU Entity MeasureTheory Finset Filter
open scoped Matrix.Norms.Frobenius BigOperators Classical Topology
variable {p c s f : Side} (r:Ratio f s)

local notation "ℬ" => SU.group
abbrev Ψ (c s : Side) := Wire ℬ 3 s × Floor E 3 c
abbrev scoutR (S:Finset (Cubic 3 s)) (x:Cubic 3 f) (m:ℕ) : Prop:=grow r x∈ collar S (m*r.count.val)
lemma scout_raise {S:Finset (Cubic 3 s)} {x y:Cubic 3 f}{k m}(h:dist y x ≤ k)(u:scoutR r S x m): scoutR r S y (m+k):= by
 rw [scoutR,add_comm,add_mul]; exact nearby (by rw [reach]; exact Nat.mul_le_mul_right _ h) u

abbrev quota (m:ℕ) := (m+1+6)*(2*(m+3)+1)^3
-- permit grows in micro cardinal and distance.
structure Shelter (g:Ratio c f)(A:Ψ c s → Floor E 3 f)(C D N:ℕ) : Prop where
 reach (S:Finset (Cubic 3 s)) : S.Nonempty → Conn S 1 → ∃ T, S⊆T ∧ Conn T 1 ∧ T⊆collar S D ∧
    T.card ≤ C*S.card+N ∧
    ∀ U V : Ψ c s, Wire.Agrees ℬ (T:Set _) U.1 V.1 →
      (∀ x, grow r (grow g x)∈T → U.2 x=V.2 x) →
      ∀ x, scoutR r S x 6 → A U x=A V x

-- rent pay at each r. UP queries and corresponding long field reads at this mesh.
lemma rents (S:Finset (Cubic 3 s))(m:ℕ)(h:Conn S 1):∃ T,S⊆ T∧ Conn T 1∧T⊆collar S ((2*m+1)*r.count.val) ∧
    T.card ≤ S.card + quota m*(S.card+r.count.val) ∧
    (∀ x,scoutR r S x m → grow r x∈ T) ∧
    ∀ U V : Wire ℬ 3 s, Wire.Agrees ℬ (T:Set _) U V → Wire.Agrees ℬ {x : Cubic 3 f|scoutR r S x m} (Wire.long ℬ U r) (Wire.long ℬ V r):=by
 obtain ⟨T,t,q,p,k,z⟩:= Grid.rent r m S h
 refine ⟨T,t,q,p,z,fun x hx=> (k x (Finset.mem_filter.mpr ⟨mem_univ _,hx⟩)).1,fun U V h i hx=>?_⟩
 exact Wire.line_eq ℬ U V _ _ _ (fun j hj=> (k i.1 (Finset.mem_filter.mpr ⟨mem_univ _,hx.1⟩)).2 i.2 j hj) h

private lemma subScout (W:Finset (Cubic 3 s)){g : Ratio p f}(q:Entity 3 p)(x:Cubic 3 f)(hx:q.Mem g x)(k:ℕ)(u:scoutR r W x k) : {x | q.Mem g x}⊆ {x|scoutR r W x (k+ (2*g.count.val))}:=by
 intro y hy; apply scout_raise r _ u; have he := Grid.triangle y (q.first g) x; rw [dist_symm (q.first g) x] at he; have hp:= q.diameter g y hy; have hz:=q.diameter g x hx; omega

lemma premise (g:Ratio c f)(m:ℕ)(hc:4≤c.val)(h:6+2*g.count.val+g.count.val ≤ m) : Shelter r g (fun U=> Grid.go g U.2 (Wire.long ℬ U.1 r)) (1+quota m) ((2*m+1)*r.count.val) (quota m * r.count.val):=by
 constructor; intro S u hv; obtain ⟨T,t,q,v,b,a,e⟩:= rents r S m hv
 refine ⟨T,t,q,v,b.trans_eq (by ring),fun U V hB hy x hx=>?_⟩
 let p:=chief g x; have hp:= (zero_proper g hc x).1
 have hh:= subScout r S p x hp 6 hx; apply Grid.go_eq g _ _ _ _ hc p ?_ ?_ hp
 · have hm(y:Cubic 3 f)(u:p.Mem g y):scoutR r S y m:=collar_le Subset.rfl (Nat.mul_le_mul_right _ (show 6+2*g.count.val ≤ m by omega)) (hh u)
   exact fun i ⟨k,v⟩=> e U.1 V.1 hB i ⟨hm _ k,hm _ v⟩
 intro y hk; apply hy; apply a; apply collar_le Subset.rfl (Nat.mul_le_mul_right _ h); exact scout_raise r (by rw [dist_symm]; exact close ..) (hh hk)

lemma nest_eq (u v : Ratio c f) : u=v := by
 have h:f.val = c.val*u.count.val:=u.exact_size; obtain ⟨u',z⟩:=u; obtain ⟨v,h⟩:=v; congr; exact Subtype.ext (Nat.eq_of_mul_eq_mul_left c.property (z.symm.trans h)) -- tune

lemma purchase (u:Ratio p f)(g: Ratio c p)(G:Ψ c s→ Floor E 3 p){C D N:ℕ}
    (h : u.count.val=2)(hv:4≤ p.val)(H: Shelter (nest u r) g G C D N)(k:ℕ)(hk:10≤k) :
    Shelter r (nest g u) (fun x=>blend ℬ u (Wire.long ℬ x.1 r) (G x)) (C+1+quota k) (max D ((2*k+1)*r.count.val)) (N+quota k*r.count.val) := by
 constructor; intro S pS qS; obtain ⟨T,t,q,v,b,e⟩:= H.reach S pS qS
 obtain ⟨U,y,w,a,f,d,σ⟩:=rents r S k qS
 obtain ⟨x,xS⟩:=pS; refine ⟨T∪U, t.trans subset_union_left, Grid.join q w _ (t xS) (y xS), union_subset (v.trans (collar_le Subset.rfl (le_max_left ..))) (a.trans (collar_le Subset.rfl (le_max_right ..))), ((card_union_le ..).trans (Nat.add_le_add b f)).trans_eq (by ring),fun A B vB hB i hb=>?_⟩
 have he (x:Cubic 3 p)(hx:scoutR (nest u r) S x 6): G A x=G B x := e A B (fun i ⟨h,v⟩=> vB i ⟨mem_union_left _ h,mem_union_left _ v⟩) (fun j hp=>hB j (by rw [grow_nest]; rw [grow_nest] at hp; exact mem_union_left _ hp)) x hx
 let o:=chief u i; have v:= (zero_proper u hv i).1
 have hz:= subScout r S o i v 6 hb; rw [h] at hz; norm_num only at hz
 have H₀: Wire.Agrees ℬ {x|o.Mem u x} (Wire.long ℬ A.1 r) (Wire.long ℬ B.1 r):=by
    intro i h; apply σ _ _ _ i ⟨collar_le Subset.rfl (Nat.mul_le_mul_right _ hk) (hz h.1),collar_le Subset.rfl (Nat.mul_le_mul_right _ hk) (hz h.2)⟩; intro i h; exact vB i ⟨mem_union_right _ h.1,mem_union_right _ h.2⟩
 apply congrArg (fun F=> closest ℬ (average (SU.group.mat ∘ F))); ext1 j; have hx:=placed u o hv i j v
 unfold book; dsimp only; rw [he,paths,o.turtle_eq ℬ u _ _ hv H₀ (List.finRange _) _ hx, paths, o.turtle_eq ℬ u _ _ hv H₀ (List.finRange _) _ v];
 · rfl
 unfold scoutR; rw [grow_nest,show (nest u r).count.val=u.count.val*r.count.val from rfl,h, ← mul_assoc]; exact collar_le Subset.rfl (Nat.mul_le_mul_right _ (by omega)) (hz hx)
end YM.CF.BProof.Grid.Blend
