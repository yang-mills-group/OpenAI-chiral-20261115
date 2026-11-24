import YM.CF.Fock.Dom
import YM.CF.Flare.Wits
/-! Elementary CAR accounting: particle changes and diagonal locality. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Cache
open Function Filter Metric Fock Finset Flare
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n:Type*} [Fintype n] [LinearOrder n]
variable {m:Type*} [Fintype m] [DecidableEq m]
variable {S:n→m}
private lemma secf {A:FC n}{i:n}{t X: Finset n}
 (h:Sector X false A) (e:i∉X) (g:i∉t) : A (insert i t) (insert i t)=A t t := by
 let w:=parity i t
 have he: put i * A=A * put i:=by simpa [Sector.grainB] using (Sector.up i (mem_singleton_self _)).apart h (by simpa)
 let b:=basisKet t
 let c:=basisKet (insert i t)
 have hk:inner ℂ (acts (put i) b) (acts (put i*A) b)=inner ℂ b (acts (A) b):=by
   rw [act_mul, ←act_inner (put i) (acts (put i) b),←act_mul, show acts (star (put i)*put i) b=b from (vacant_act i t).trans (if_neg g)]
 rw [he,act_mul,show acts (put i) b=w • c from (put_act _ _).trans (if_neg g),map_smul,inner_smul_right,inner_smul_left] at hk; change w*(star w * _)= _ at hk
 rw [←mul_assoc w,show star w=w from parity_star ..,show w*w=1 from parity_sq ..,one_mul] at hk
 unfold b c at hk; rwa [basis_inner,basis_act,basis_inner,basis_act] at hk
private lemma secured {A:FC n}{X s : Finset n}(p:Sector X false A) : A (s∩X) (s∩X)=A s s := by
 let R:=s∩X
 suffices h:∀ t:Finset n,Disjoint t X → A R R=A (t∪R) (t∪R) by
    let l:=s\X
    have he:l∪R=s:=by ext; simp only [l,R,mem_inter,mem_union,Finset.mem_sdiff]; tauto
    have hx:=h l disjoint_sdiff_self_left; rw [he] at hx; exact hx
 intro t H; induction t using Finset.induction_on with
 | empty=>simp [R]
 | insert i t ht ih=>
    have he:=disjoint_insert_left.mp H; change _=A (insert i t∪R) _; rw [insert_union,secf p he.1 (show i∉ t∪R by simp [R,ht,he.1])]; exact ih he.2
lemma stake {A:FC n}{s t X: Finset n}(p:Sector X false A)(e:s∩X=t∩X): A s s=A t t:=by rw [←secured (s:=s) p,e,secured p]

def variety (S:n→m) (x:m) := univ.filter (fun v:n=> S v=x)
def parcel (S:n→m) (x:m) (s:Finset n):= s∩variety S x
def changes (S:n→m) (s t : Finset n) := univ.filter (fun x=> parcel S x s≠parcel S x t)
private lemma vary {s t:Finset n}{x:m} : x ∉ changes S s t ↔ parcel S x s=parcel S x t:= by simp [changes]
lemma changes_comm (s t:Finset n) : changes S s t=changes S t s:=by ext; simp [changes,eq_comm]
lemma changes_union (s t u:Finset n): changes S s t ⊆ changes S s u∪changes S u t:=by
 intro i h; by_contra hp; rw [Finset.mem_union,not_or] at hp; exact vary.mpr ((vary.mp hp.1).trans (vary.mp hp.2)) h
def ChangeBill (S:n→m) (k:ℕ)(A:FC n) := ∀ s t:Finset n,A s t≠0 → (changes S s t).card ≤ k
lemma ChangeBill.star {k:ℕ}{A:FC n}(p:ChangeBill S k A): ChangeBill S k (star A):=by intro s t h; rw [changes_comm]; apply p; intro hp; rw [Matrix.star_apply,hp,star_zero] at h; contradiction
lemma ChangeBill.add {k:ℕ}{A F:FC n}(p:ChangeBill S k A) (v:ChangeBill S k F) : ChangeBill S k (A+F):=by
 intro s t h; rw [Matrix.add_apply] at h; by_cases l:A s t=0; rw [l,zero_add] at h; exact v s t h; exact p s t l
lemma ChangeBill.sub {k:ℕ}{A F:FC n}(p:ChangeBill S k A) (v:ChangeBill S k F) : ChangeBill S k (A-F):=by
 intro s t h; rw [Matrix.sub_apply] at h; by_cases l:F s t=0; rw [l,sub_zero] at h; exact p s t h; exact v s t l
lemma ChangeBill.scale {k:ℕ}{A:FC n}(p:ChangeBill S k A)(c:ℂ) : ChangeBill S k (c • A):=by
 intro s t h; exact p s t (right_ne_zero_of_mul (show c*A s t≠0 from h))
lemma ChangeBill.series {I:Type*} {k:ℕ}(W: Finset I)(f:I→FC n)(p:∀ i∈ W,ChangeBill S k (f i)): ChangeBill S k (∑ i∈W,f i):=by
 intro s t h; rw [Matrix.sum_apply] at h; obtain ⟨u,z,v⟩:= exists_ne_zero_of_sum_ne_zero h; exact p u z _ _ v
lemma ChangeBill.le {k v:ℕ}{A:FC n}(p:ChangeBill S k A)(z:k≤v): ChangeBill S v A:=fun i j h=> (p i j h).trans z
lemma change_nil (S:n→m)(k): ChangeBill S k 0:= fun _ _ h=> False.elim (h rfl)
lemma change_one (S:n→m)(k): ChangeBill S k 1:= by intro i j h; rw [Matrix.one_apply] at h; split at h; subst i; simp [changes]; contradiction
lemma ChangeBill.mul {k l:ℕ}{A B:FC n}(p:ChangeBill S k A)(q:ChangeBill S l B):ChangeBill S (k+l) (A*B):=by
 intro s t h; rw [Matrix.mul_apply] at h; obtain ⟨u,b,v⟩:= exists_ne_zero_of_sum_ne_zero h
 exact (Finset.card_le_card (changes_union _ _ u)).trans ((Finset.card_union_le ..).trans (Nat.add_le_add (p s u (left_ne_zero_of_mul v)) (q u t (right_ne_zero_of_mul v))))
variable (S) {A:FC n}{x y:m}{s t W:Finset n}
omit [Fintype m] in
lemma exclusive (h:Sector (variety S x) false A)(e:A s t≠0)(p:x≠y) : parcel S y s=parcel S y t:=by
 ext i; by_cases g:i∈ variety S y <;> simp only [g,parcel,mem_inter,and_false,and_true]
 exact (h.dotGrade _ _ e i (by intro l; exact p (((mem_filter.mp l).2).symm.trans (mem_filter.mp g).2))).symm
lemma change_loc (p:Sector (variety S x) false A) : ChangeBill S 1 A:=by
 intro i j h; refine le_trans (card_le_card (t:={x}) (fun v l=> ?_)) (card_singleton _).le; by_contra k; exact vary.mpr (exclusive _ p h (Ne.symm (by simpa using k))) l
lemma change_put (i:n) : ChangeBill S 1 (put i) := by
 intro s t h; rw [put_entry] at h; split_ifs at h with p k <;> first|contradiction| subst s
 refine (card_le_card (t:={S i}) ?_).trans (card_singleton _).le
 intro x g; by_contra l; apply vary.mpr ?_ g
 ext u; by_cases hp:u=i; subst u; simp [parcel,variety, Ne.symm (show x≠S i from fun h=>l (mem_singleton.mpr h))]; simp [parcel,hp]
lemma change_letter (i : Reader0 n) : ChangeBill S 1 (ton i) := by
 obtain ⟨b,v⟩:=i; have ht:ChangeBill S 1 (create v):=by rw [create_def]; exact ChangeBill.series _ _ fun i _=> (change_put S i).scale _
 cases b; exact ht; exact ht.star
lemma change_ice (L:Op n)(i:Reader0 n) : ChangeBill S 1 (iceT L i):=change_letter _ (i.1, acts (if i.1 then 1+star L else 1-L) i.2)
-- Cut on a fixed pattern inside one tile. Diagonal projectors are not needed to be Sector.
def fixed (S:n→m) (W:Finset n)(x:m) : FC n := cutM (univ.filter (fun u=> parcel S x u=parcel S x W))
omit [Fintype m] in
lemma fix_left (A:FC n)(v w:Finset n): (fixed S W x*A) v w=if parcel S x v=parcel S x W then A v w else 0:=by unfold fixed cutM; rw [Matrix.diagonal_mul]; split_ifs <;> simp_all
omit [Fintype m] in
lemma fix_right (A:FC n)(v w:Finset n): (A*fixed S W x) v w=if parcel S x w=parcel S x W then A v w else 0:=by unfold fixed cutM; rw [Matrix.mul_diagonal]; split_ifs <;> simp_all
omit [Fintype m] in
lemma fix_middle (h:Sector (variety S x) false A) : fixed S W x * A * fixed S W x= A W W • fixed S W x:=by
 let f:=fixed S W x; ext s t
 rw [fix_right,fix_left]
 split_ifs with ht hs
 · by_cases hg:s=t
   · subst t; rw [stake h (show s∩variety S x=W∩variety S x from hs)]; simp [fixed,cutM,show parcel S x s= _ from hs]
   simp only [Matrix.smul_apply,fixed,cutM,Matrix.diagonal_apply_ne _ hg,smul_zero]
   by_contra p; apply hg
   ext i; by_cases g:i∈ variety S x; swap; · exact (h.dotGrade _ _ p _ g).symm
   suffices he : i∈parcel S x s ↔ i ∈parcel S x t by simpa [parcel,g] using he
   rw [hs,ht]
 all_goals by_cases hg:s=t <;> simp_all [fixed,cutM]
end YM.CF.Buffered.Cache
