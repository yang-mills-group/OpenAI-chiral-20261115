import Velour.Arabesque.Braid
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 2800
noncomputable section
namespace YM.OS.Semigroup
open Function Set Filter Complex Analysis MeasureTheory
open scoped NNReal ENNReal Topology BigOperators ContDiff InnerProductSpace ComplexOrder
variable {H : Hilbert} {a : Axis} (S:Semigroup H a)


open Boundary Probe
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin

variable {S}{H':Hilbert}{b:Axis}{T:Semigroup H' b}
variable {κ:Type}(L:S.Livery κ)(J:T.Livery κ)
   (h:a≠b)(A:S.Tiles h)(B:T.Tiles (Ne.symm h))
variable {n:ℕ}
local notation "ℓ"=> Fin n→ℝ
local notation "ℒ"=> Fin n→ℂ
local notation "σ"=> Equiv.Perm (Fin n)
variable (u:Fin n→κ)(X:Fin n→E4)
namespace Livery
local notation "D"=>S.muslin
local notation "Ω"=>L.Ω
local notation "Y"=>L.Y
local notation "U"=>S.liftL
local notation "τ"=>κ × Test4
local notation "ℙ"=>List (κ × Test4)

def frontD(a b:Axis)(x y:E4) := |y b-x b| - |y a-x a|
lemma frontD_symm(x y:E4):frontD a b x y=frontD a b y x:=by
  unfold frontD; rw [abs_sub_comm,abs_sub_comm (y a)]

def bandspace(a b:Axis)(d:ℝ)(f g:Test4):Prop:=
 ∀x y:E4,f x≠0→g y≠0→d≤frontD a b x y

lemma bandspace.symm {d:ℝ}{f g:Test4}(p:bandspace a b d f g):bandspace a b d g f:=by
 intro x y hg hf; rw [frontD_symm]; exact p _ _ hf hg

def Springs(a b:Axis)(d:ℝ)(l:ℙ):Prop:=
 List.Pairwise (fun x y:τ=>bandspace a b d x.2 y.2) l

include A B in
lemma yes_perm (w:Pact L J)(l r:ℙ)(p:l.Perm r)
   (d:ℝ)(e:0<d)(g:Springs a b d l): L.song l=L.song r:=by
  obtain ⟨m,t,y⟩:∃(n:ℕ)(t:Fin n→τ),(Each n).map t=l:=⟨_,_,List.map_get_finRange l⟩
  subst l
  obtain ⟨j,rfl⟩:= cornice r t p.symm
  let c i:=(t i).1
  let f i:=(t i).2
  rw [song_cast,song_cast]
  apply L.yes J h A B c f 1 j _ w

  change List.Pairwise _ (List.map t (List.finRange m)) at g
  rw [← List.ofFn_eq_map] at g
  refine ⟨_,e, fun x v i k q=>?_⟩
  rw [Joint.material_at] at v
  have r:∀i, f i (x i)≠0:= fun i=> Finset.prod_ne_zero_iff.mp v i (Finset.mem_univ _)
  have l:bandspace a b d (f i) (f k):= by
     rcases lt_or_gt_of_ne q with y|y
     · exact List.pairwise_ofFn.mp g y
     exact (List.pairwise_ofFn.mp g y).symm
  exact l _ _ (r i) (r k)

lemma behind_bound(x:τ)(p:LocalTest x.2):
 ∃M:ℝ,∀y:E4,x.2 y≠0→ |y a|≤M ∧ |y b|≤M :=by
   obtain ⟨v,t⟩:=p.isCompact.exists_bound_of_continuousOn
     (f:=fun y:E4=>(y a,y b)) (by fun_prop)
   refine ⟨v,fun y u=>?_⟩
   have r:=t y (subset_tsupport _ u)
   simpa [Prod.norm_def] using r

lemma uniform_behind (l:ℙ)(p:CompactW l):
 ∃M:ℝ,∀x∈l,∀y:E4,x.2 y≠0→ |y a|≤M ∧ |y b|≤M :=by
    induction l with
    | nil=>exact ⟨0,fun _ h=> False.elim (List.not_mem_nil h)⟩
    | cons x l ih=>
      obtain ⟨m,r⟩:=ih (fun _ t=>p _ (List.mem_cons_of_mem _ t))
      obtain ⟨v,q⟩:=behind_bound (a:=a) (b:=b) x (p _ List.mem_cons_self)
      refine ⟨max m v,fun y hy z u=>?_⟩
      rcases List.mem_cons.mp hy with w|w
      · obtain ⟨c,t⟩:=q _ (w ▸ u)
        exact ⟨le_max_of_le_right c,le_max_of_le_right t⟩
      obtain ⟨c,t⟩:=r _ w _ u
      exact ⟨le_max_of_le_left c,le_max_of_le_left t⟩

lemma dispersal (l:ℙ)(p:CompactW l)(x:τ)(e:LocalTest x.2)(d:ℝ):
 ∃w:ℝ,∀r:E4,|r a|≤1→w≤|r b|→∀y∈l,bandspace a b d (ahead r x.2) y.2:=by
  obtain ⟨m,t⟩:=uniform_behind (a:=a) (b:=b) (x::l)
      (fun y g=>(List.mem_cons.mp g).elim (fun h=>h.symm ▸e) (p y))
  refine ⟨4*m+1+d,fun r u y b' k z v p' g=>?_⟩
  rw [ahead_at] at p'


  obtain ⟨i,j⟩:=t _ List.mem_cons_self _ p'
  obtain ⟨i',j'⟩:=t _ (List.mem_cons_of_mem _ k) _ g
  change |z a-r a|≤m at i
  change |z b-r b|≤m at j
  have L(q s:ℝ):|q|≤|s|+|q-s|:=by
      simpa only [sub_add_cancel] using abs_add_le (q-s) s |>.trans_eq (add_comm ..)
  have v': |v a-z a|≤ 2*m+1:= by
     linarith [abs_sub (v a) (z a),L (z a) (r a)]
  have k': |r b| ≤2*m+|v b-z b|:=by
     linarith [L (r b) (z b),L (z b) (v b),abs_sub_comm (r b) (z b),
        abs_sub_comm (z b) (v b)]
  unfold frontD
  linarith


lemma compact_cons(x:τ)(l:ℙ):
 CompactW (x::l) ↔ LocalTest x.2 ∧ CompactW l :=by
 simp [CompactW]

lemma compact_last(l:ℙ)(x:τ):CompactW (l++[x]) ↔ CompactW l ∧ LocalTest x.2 :=by
 simp only [CompactW,List.mem_append,List.mem_singleton,or_imp,forall_and,forall_eq]

lemma springs_cons(x:τ)(l:ℙ)(d:ℝ):
 Springs a b d (x::l) ↔ (∀y∈l,bandspace a b d x.2 y.2) ∧ Springs a b d l:=List.pairwise_cons

lemma spring_last(l:ℙ)(d:ℝ)(x:τ)(p:∀y∈l,bandspace a b d x.2 y.2)(q:Springs a b d l):
 Springs a b d (l++[x]):=
 List.pairwise_append.mpr ⟨q,by simp,fun i r y v=>
    (List.mem_singleton.mp v).symm ▸ (p i r).symm⟩

private lemma lastSplit(l:ℙ):
 l=[]∨∃m:ℙ,∃x:τ,l=m++[x]:= by induction l using List.reverseRec with
  | nil=>exact Or.inl rfl
  | append_singleton=>exact Or.inr ⟨_,_,rfl⟩

include A B
lemma yes_window (w:Pact L J)(fr:S.Fray L.Q L.Y)(d:ℝ)(e:0<d)
  (l r:ℙ)(p:l.Perm r)(q:Springs a b d l)(c:CompactW l)
   (v y:ℙ)(z:CompactW v)(f:CompactW y):
 L.song (v++l++y)=L.song (v++r++y):=by
 suffices ∀n (v y:ℙ),v.length+y.length=n→ CompactW v → CompactW y →
    ∀(l r:ℙ),l.Perm r→Springs a b d l→CompactW l →
     L.song (v++l++y)=L.song (v++r++y)
   from this _ v y rfl z f _ _ p q c
 clear v y z f p q c l r
 intro n; induction n using Nat.strong_induction_on with
 | h n ih =>
   intro v y a' z f l r p q c
   rcases y with _|⟨x,y⟩
   · rcases lastSplit v with u|⟨u,x,rfl⟩
     · simp [u,L.yes_perm J h A B w l r p d e q]
     obtain ⟨zu,zx⟩:=(compact_last _ _).mp z
     obtain ⟨M,t⟩:=dispersal (a:=a) (b:=b) l c x zx d
     rw [List.append_nil,List.append_nil]
     apply L.peel_left h A fr (u++[x]) l (u++[x]) r M
     intro s p1 p2
     let m:=parade s u
     let j:=onFoot s x
     have y:m.length+(0:ℕ)<n:=by
        simp [m,parade] at *
        omega
     have x':= ih _ y m [] rfl (zu.parades s) (by simp [CompactW])
        (j::l) (j::r) (p.cons _) ((springs_cons _ _ _).mpr ⟨t s p1 p2,q⟩)
        ((compact_cons j l).mpr ⟨LocalTest.ahead zx s,c⟩)
     simpa [m,j,parade] using x'
   obtain ⟨fx,fy⟩:=(compact_cons _ _).mp f
   obtain ⟨M,t⟩:=dispersal (a:=a) (b:=b) l c x fx d
   apply L.peel_right h A fr (v++l) (x::y) (v++r) (x::y) M
   intro s p1 p2
   let m:=parade s y
   let j:=onFoot s x
   have t':v.length+m.length<n:=by
     simp [m,parade]; simp at a'; omega
   have x':=ih _ t' v m rfl z (fy.parades s)
        (l++[j]) (r++[j]) (p.append_right _) (spring_last l d j (t s p1 p2) q)
        ((compact_last l j).mpr ⟨c,LocalTest.ahead fx s⟩)
   simpa [m,j,parade] using x'
#print axioms yes_window

lemma prelim (w:Pact L J)(fr:S.Fray L.Q L.Y)
  (i j:τ)(u:LocalTest i.2)(k:LocalTest j.2)(d:ℝ)(e:0<d)
  (q:bandspace a b d i.2 j.2)
  (r t:ℙ)(z:CompactW r)(f:CompactW t):
 L.song (r++[i,j]++t)=L.song (r++[j,i]++t):=by
   refine L.yes_window J h A B w fr d e _ _ (List.Perm.swap ..) ?_ ?_ r t z f
   · exact List.pairwise_cons.mpr ⟨fun _ t=>(List.mem_singleton.mp t).symm ▸ q,
             List.pairwise_singleton _ _⟩
   simp only [compact_cons]
   exact ⟨u,k,by simp [CompactW]⟩
#print axioms prelim
