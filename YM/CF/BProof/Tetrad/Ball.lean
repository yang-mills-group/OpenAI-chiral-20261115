import YM.CF.BProof.Tetrad.Shuffle
import YM.CF.BProof.Tetrad.Chop
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Tetra
open Function Finset List
open scoped BigOperators Classical
open Regard
variable {n:ℕ}
abbrev Wheel(n:ℕ) := Σ X: Fin n→Tone, Fin (massZ (ofFn fun i=> some (X i))) -- better polar
abbrev Cage(n:ℕ) := Σ X:Fin n→Tone, Fin (polar (ofFn X))
abbrev color(a:Cage n)(i:Fin n):= a.1 i
def pose (x: Fin n→ Option Tone)(F: Fin n→Tone):Prop:=∀ i,x i=none ∨ x i=some (F i)
lemma sum_p(f:Road→ℕ)(x: Fin n→Option Tone): fill f (ofFn x)= ∑ y:Fin n→Tone, if pose x y then f (ofFn y) else 0 :=by
 induction n generalizing f with|zero=> simp [pose, List.ofFn_zero]|succ n ih=>
   rw [List.ofFn_succ]; set p:=(fun i:Fin n=> x i.succ)
   let j:=Fin.consEquiv (fun _: Fin (n+1)=>Tone); rw [←Equiv.sum_comp j, Fintype.sum_prod_type]; simp_rw [show ∀ (a:Tone)(y:Fin n→Tone),j (a,y)=Fin.cons (α:=fun _=>Tone) a y from fun _ _=>rfl,ofFn_cons]; have he(a:Tone)(V:Fin n→Tone):pose x (j (a,V)) ↔ (x 0=none∨ x 0=some a)∧ pose p V:=by unfold pose; simp only [Fin.forall_fin_succ (n:=n),j]; simp [p] -- tune
   simp_rw [show ∀ (a:Tone)(x':Fin n→Tone),pose x (Fin.cons a x') ↔ _ from he]; cases u:x 0 with
   | none=> rw [f_s]; simp only [true_or, true_and]; exact sum_congr rfl fun i _=> ih _ p
   | some i=> rw [f_c, Finset.sum_eq_single (f:=fun a:Tone=>_) i]; simpa [u] using ih (fun x=> f (i::x)) p; intro a _ h; simp [h.symm]; simp
lemma count_pose (p: Fin n→Option Tone):Regard.count (fun x:Cage n=>pose p x.1)= massZ (ofFn p):=by
 unfold Regard.count; rw [Fintype.sum_sigma]; dsimp only
 rw [massZ,sum_p]; apply sum_congr rfl; intro i hx; by_cases u:pose p i <;> simp [u]
lemma inherit (h:2 ≤ n) : Nonempty (Cage n) :=by
 let p (i:Fin n):Option Tone:=none; let x:= ofFn p; have hh: 0< massZ x:=by
    have he:∀ i∈x,i=none:=fun i h=>by simp [x,p] at h; exact h.2 -- tune need Nonempty fin
    have hu:2≤ x.length:=by simpa [x]
    generalize vv:x=y at he hu ⊢; induction y using List.reverseRecOn with | nil=>simp at hu| append_singleton x a _=> rw [he a (by simp),deleteZ]; exact mul_pos (by decide) (money (fun i v=> he i (by simp [v]))); intro v; subst x; simp at hu
 have ht:= count_pose p; by_contra! hx; haveI:IsEmpty (Cage n):= hx; change massZ x > 0 at hh; change _= massZ x at ht; rw [←ht] at hh; unfold Regard.count at hh; simp at hh
variable (a b:Finset (Fin n))(x:a → Tone)(y:b→Tone)
def scene (i:Fin n) : Option Tone:= if h:i∈a then some (x ⟨i,h⟩) else if h:i∈b then some (y ⟨i,h⟩) else none
lemma moneyB (p:Disjoint a b): ball (Pieces a (@color n)) (Pieces b color) x y = massZ (ofFn (scene a b x y)):=by
 rw [← count_pose]; refine count_con _ _ fun i=>?_ ; constructor; rintro ⟨u,v⟩ j; unfold scene; split; right; rw [←u]; rfl; split; right; rw [←v]; rfl; tauto
 intro h; constructor
 · apply funext; rintro ⟨j,p⟩; have hv:=h j; rw [scene,dif_pos (show j∈a from p)] at hv; exact (Option.some.inj (hv.resolve_left (by simp))).symm
 apply funext; rintro ⟨j,v⟩; have hv:=h j; have ht:j∉a:=fun g=>Finset.disjoint_left.mp p g v; rw [scene,dif_neg ht,dif_pos (show j∈b from v)] at hv; exact (Option.some.inj (hv.resolve_left (by simp))).symm
end YM.CF.BProof.Tetra
