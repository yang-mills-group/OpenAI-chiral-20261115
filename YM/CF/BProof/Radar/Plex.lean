import YM.CF.BProof.Radar.Locus
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.BProof.Mesh
open Lattice Function Finset Equiv Regard
open scoped BigOperators Classical
variable {A B U V:Type*}{n: Side}{p d o r:ℕ}

-- Abstract connected component in field of active sites S and attribute Z. Cat.Sparsity used at any active centre. parameter diameter *2.
namespace Cat
abbrev Sty(S:Support n)(x y:Site n)(l:ℕ):= x∈S ∧ y∈S∧separation x y≤l
variable (S:Support n) (l:ℕ)
def sun (i:Site n) : ℕ → Support n
 | 0=>{i}
 | k+1=> sun i k ∪ (halo l (sun i k)∩S) -- carry i even if off; later when all.
lemma keep(i:Site n)(k:ℕ):sun S l i k⊆ sun S l i (k+1):= by rw [sun]; exact subset_union_left
lemma mono(i:Site n): Monotone (sun S l i):= monotone_nat_of_le_succ (keep S l i) -- tune
lemma warm(i:Site n)(k:ℕ):i∈sun S l i k:= mono S l i (Nat.zero_le _) (show i∈sun S l i 0 from mem_singleton_self _)
lemma lit{x y:Site n}{k:ℕ}(h:x∈ S)(t:y∈sun S l x k):y∈S:=by induction k with | zero=> exact (by rw [sun,mem_singleton] at t; simpa [t] using h)|succ k ih=> rw [sun] at t; rcases mem_union.mp t with t|t; exact ih t; exact (mem_inter.mp t).2
local notation "Xκ"=>Site n
lemma size(i j:Xκ)(k:ℕ)(h:j∈sun S l i k) : separation i j ≤ k*l:=by
 induction k generalizing j with|zero=> rw [sun,mem_singleton] at h; simp [h]|succ k ih=> rw [Nat.succ_mul]; rw [sun] at h; rcases mem_union.mp h with h|h; exact (ih _ h).trans (Nat.le_add_right ..); obtain ⟨y,g,u⟩:= halo_spec.mp (mem_inter.mp h).1; exact (separation_triangle i y j).trans (Nat.add_le_add (ih _ g) u)
abbrev Vale(S:Support n)(l r:ℕ):=∀ Y⊆ S, (∀ x∈Y,∀ y∈Y,separation x y ≤ 2*(r*l))→Y.card ≤ r
abbrev component (r:ℕ) (x:Site n):= sun S l x r
variable {i j:Site n}
namespace Vale
variable (t:Vale S l r)
include t
lemma charge(h:i∈S) : (component S l r i).card≤r:=t _ (fun i v=>lit S l h v) fun x u y v=> le_trans (separation_triangle x i y) (by have he:=size S l i x _ u; have hv:=size S l i y _ v; rw [separation_comm x i]; omega)
private lemma plateau {i: Site n} (t:i∈ S){k:ℕ}(h: sun S l i k=sun S l i (k+1)) :∀ u≥ k, sun S l i u=sun S l i (u+1):=by
 intro u p; induction u,p using Nat.le_induction with | base=> exact h| succ x hx ih=> nth_rw 1 [sun]; rw [show sun S l i x=sun S l i _ from ih]; rfl
lemma stabil(h:i∈S): component S l r i=sun S l i (r+1):=by
 have hr:= charge S l t h; change (sun S l i r).card≤ r at hr; unfold component; by_contra k
 have hp(x:ℕ)(p:x ≤ r): x<(sun S l i x).card:= by induction x with|zero=> simp [sun]|succ x ih=>
    have hx:= ih (by omega); have hu: (sun S l i x).card < (sun S l i (x+1)).card:= card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨keep S l i x, fun f=> k (plateau S l t h f r (by omega))⟩); omega
 exact not_lt.mpr hr (hp r le_rfl)
lemma major(h:i∈ S){k:ℕ} : sun S l i k⊆component S l r i:=by
 induction k with|zero=>exact mono _ _ _ (Nat.zero_le _)|succ k ih=> rcases le_or_gt (k+1) r with u|u; exact mono _ _ _ u; rw [←plateau S l t h (stabil _ _ t h) k (by omega)]; exact ih
end Vale
-- concat component once truncated
lemma tenor {k r:ℕ} {x y z:Site n}(h:y∈sun S l x k)(g:z∈sun S l y r): z∈sun S l x (k+r):=by
 induction r generalizing z with
 | zero=> rw [sun,mem_singleton] at g; simpa [g]
 | succ r ih=> rw [sun] at g; rw [Nat.add_succ,sun]; rcases mem_union.mp g with t|t; exact mem_union_left _ (ih t); apply mem_union_right; apply mem_inter.mpr; refine ⟨?_,(mem_inter.mp t).2⟩; obtain ⟨w,h,t⟩:= halo_spec.mp (mem_inter.mp t).1; exact halo_spec.mpr ⟨_,ih h,t⟩
lemma arc (u:j∈ S)(v:separation i j≤ l):j∈ sun S l i 1:= mem_union_right _ (mem_inter.mpr ⟨halo_spec.mpr ⟨_,mem_singleton_self i,v⟩,u⟩)
lemma equal(k:ℕ){x y:Xκ}(h:x∈ S)(g:y∈sun S l x k):x∈sun S l y k:=by
 induction k generalizing y with
 | zero=> rw [sun,mem_singleton] at g; rw [g]; exact warm ..
 | succ k ih=> rw [sun] at g; rcases mem_union.mp g with t|t; exact keep _ _ _ k (ih t); obtain ⟨w,v,u⟩:=halo_spec.mp (mem_inter.mp t).1; rw [add_comm]; apply tenor S l (z:=x) (arc _ l (lit _ _ h v) (separation_comm .. ▸ u)) (ih v)
lemma connected (g:Vale S l r)(h:i∈ S)(t:j∈component S l r i) : component S l r j=component S l r i:=Subset.antisymm (fun k v=> g.major S l h (tenor _ _ t v)) (fun k v=>g.major S l (lit _ _ h t) (tenor _ _ (equal S l _ h t) v))
-- Depends on S in n*l. helper Vale movement for exact output set
lemma home (e:Perm Xκ)(V:Support n)(x:Xκ)(p:∀ x,x∈S↔e x∈V)(t:∀ x y,separation (e x) (e y)=separation x y) (k:ℕ):sun V l (e x) k=(sun S l x k).map e.toEmbedding:=by
 induction k with | zero=> simp [sun]| succ k ih=>
   ext y; obtain ⟨y,rfl⟩:=e.surjective y; simp only [sun,ih,map_union,mem_union,mem_map_equiv,Equiv.symm_apply_apply,mem_inter,←p,halo_spec]; apply or_congr_right'; intro _; apply and_congr_left'; constructor <;> rintro ⟨i,g,h⟩
   · obtain ⟨i,rfl⟩:= e.surjective i; exact ⟨_,by simpa using g, t .. ▸ h⟩
   exact ⟨e i,by simpa,(t ..).trans_le h⟩
lemma shore (T:Support n)(x:Site n)(k:ℕ)(p:∀ i:Site n,separation x i≤ k*l→ (i∈S↔ i∈T)): sun S l x k=sun T l x k:=by
 induction k with|zero=>rfl|succ k ih=>
    have ht:=ih (fun i h=> p i (h.trans (by rw [Nat.succ_mul]; omega))); ext y; by_cases e: separation x y ≤ (k+1)*l; rw [sun,sun,ht]; simp only [mem_union,mem_inter,p y e]; simp only [show y∉sun S l x (k+1) from fun v=> e (size S l _ _ _ v),show y∉sun T l x (k+1) from fun v=>e (size T l _ _ _ v)] -- size .. v tune
end Cat
end YM.CF.BProof.Mesh
