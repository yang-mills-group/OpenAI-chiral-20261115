import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Algebra.Operations
/-! noncommutative products expansion over assignments. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress
open Function Finset
open scoped BigOperators Classical
variable {A I H: Type*} [Fintype I] [Ring A] (s : List I) (t : I→ Finset H)
def walkMul {A I:Type*}[Monoid A] (s:List I) (f:I→ A) := (s.map f).prod
lemma walk_sum [Nonempty H] (f:I→H→A)(p:s.Nodup)(v:∀ i,i∈s): walkMul s (fun i=>∑ a∈t i,f i a)= ∑ w∈Fintype.piFinset t,walkMul s (fun i=> f i (w i)):=by
 let h:H:=Classical.arbitrary H; let U(l:List I):= Fintype.piFinset fun i=> if i∈l then t i else {h}; have ht (l) (w:I→H) : w∈ U l ↔ (∀ i∈l, w i∈ t i) ∧ (∀ i∉l,w i=h):=by
    unfold U; rw [Fintype.mem_piFinset]; constructor
    · intro p; constructor; intro i b; specialize p i; rwa [if_pos b] at p; intro i b; specialize p i; simpa [b] using p
    intro p i; by_cases v:i∈l; rw [if_pos v]; exact p.1 i v; rw [if_neg v]; exact mem_singleton.mpr (p.2 i v)
 have e(l:List I)(p:l.Nodup) : walkMul l (fun i=>∑ a∈t i,f i a)=∑ w∈U l, walkMul l fun i=> f i (w i) := by
    induction l with
    | nil=> rw [show U []={fun _=> h} from (by ext u; simp [ht,funext_iff])]; simp [walkMul]
    | cons i l ih=>
     obtain ⟨g,hL⟩:= List.nodup_cons.mp p; let α(x:H×(I→H)):= update x.2 i x.1 -- tune name conflict
     have hh(w:I→H) : w∈U (i::l)↔ w i ∈ t i ∧ update w i h∈U l:=by
        simp only [ht]; constructor
        · rintro ⟨p,v⟩; refine ⟨p _ List.mem_cons_self, fun j t=>?_,fun j k=>?_⟩; have hx:j≠i:= fun h=>g (h ▸ t); rw [update_of_ne hx]; exact p j (by simp [t])
          by_cases p:j=i; simp [p]; rw [update_of_ne p]; exact v j (by simp [p,k])
        rintro ⟨p,a,b⟩; constructor; intro j x; rcases List.mem_cons.mp x with rfl|v; exact p; have hx:= a j v; rw [update_of_ne (fun p : j=i=>g (p ▸ v))] at hx; exact hx
        intro j h; have hx:j≠i:=fun v=> h (by simp [v]); have hu:= b j (fun x=>h (by simp [x])); rwa [update_of_ne hx] at hu
     have name (k:I→ H)(p:k∈U l): update k i h=k:= by rw [←(ht ..|>.mp ‹_›).2 i g]; apply update_eq_self
     have he: U (i::l)= (t i×ˢ U l).image α :=by
       ext x; rw [hh]; constructor
       · intro h'; refine mem_image.mpr ⟨(x i,update x i h),mem_product.mpr h',?_⟩; simp [α]
       intro p; obtain ⟨⟨w,k⟩,v,rfl⟩:= mem_image.mp p; unfold α; simp [(mem_product.mp v).1,(mem_product.mp v).2,name k (mem_product.mp v).2]
     rw [walkMul,List.map_cons,List.prod_cons,← walkMul,ih hL,sum_mul]; rw [he,sum_image, sum_product]; swap
     · rintro ⟨a,x⟩ p ⟨k,y⟩ s e; obtain ⟨hx,g'⟩:= mem_product.mp p; obtain ⟨w,b⟩:=mem_product.mp s; have he:=congrFun e i; have hu :=congrArg (fun x:I→H=> update x i h) e
       simp [α] at he; refine Prod.ext he ?_; simpa [α,name x g',name y b] using hu
     apply sum_congr rfl; intro i' z; rw [mul_sum]; apply sum_congr rfl; intro v _; rw [walkMul,walkMul,List.map_cons,List.prod_cons]; refine congrArg₂ (·*·) ?_ ?_; · simp [α]
     apply congrArg List.prod; apply List.map_congr_left; intro j t; simp [α,update_of_ne (show j≠i from fun v=>g (v ▸ t))]
 rw [e s p]; simp only [U,v, ↓reduceIte]
variable {R : Type*} [CommSemiring R] [Algebra R A]
lemma walk_scalar (f:I→ A) (w:I→ R) : walkMul s (fun i=>w i • f i) = walkMul s w • walkMul s f:=by
 induction s with
 | nil=> simp [walkMul]
 | cons i s ih=>simp only [walkMul,List.map_cons,List.prod_cons] -- recursive simp loop?
                unfold walkMul at ih; rw [ih, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
lemma walk_prod {M : Type*}[CommMonoid M](p:s.Nodup)(v:∀ i,i∈s)(f:I→M) : walkMul s f=∏ i,f i:=by
 rw [← show s.toFinset=univ from (eq_univ_iff_forall ..|>.mpr (by simpa using v))]; rw [walkMul,List.prod_toFinset ..]; exact p
end YM.CF.BPress
