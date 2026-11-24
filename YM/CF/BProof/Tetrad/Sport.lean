import YM.CF.BProof.Tetrad.Ball
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Tetra
open Function Finset List Regard
open scoped BigOperators Classical
variable {n:ℕ}{A:Type*}
lemma next_val (i: Fin n) : i.castSucc+1=i.succ:=by cases n with|zero=>exact i.elim0|succ n=>ext; rw [Fin.val_add,Fin.val_one]; simp; omega
variable [NeZero n]
lemma uv (X:A→A→Prop)(f:Fin n→A): Cycle.Chain X (ofFn f) ↔ ∀ i,X (f i) (f (i+1)) :=by
 rcases n with _|n; exact (NeZero.ne 0 rfl).elim
 rw [Cycle.chain_ne_nil _ (ne_nil_of_length_pos (by simp)),getLast_ofFn_succ, isChain_cons]; have ht:(ofFn f).head? = some (f 0):=by rw [ofFn_succ]; rfl
 simp only [ht,Option.mem_some_iff]; rw [List.isChain_ofFn]; simp only [forall_eq']
 constructor; rintro ⟨p,h⟩ i; induction i using Fin.lastCases with | last=> rw [Fin.last_add_one]; exact p| cast i=>rw [next_val]; exact h i.val (by omega)
 intro h; refine ⟨by simpa using h (Fin.last n),fun i p=>?_⟩; let k:Fin n:=⟨i,by omega⟩; have hx:=h k.castSucc; rw [next_val] at hx; exact hx
lemma roll_a (f:Fin n→Tone): polar (ofFn (fun i=>f (i+1)))=polar (ofFn f):=by
 rcases n with _|n; exact (NeZero.ne 0 rfl).elim
 rw [List.ofFn_succ',concat_eq_append,List.ofFn_succ (f:=f)]; simp_rw [next_val,Fin.last_add_one]; exact trim _ [f 0]
open Fin.NatCast
lemma roll(f:Fin n→Tone)(j:Fin n) : polar (ofFn fun i=> f (i+j))=polar (ofFn f):=by
 have he(j:ℕ):polar (ofFn fun i:Fin n=> f (i+↑j))= polar (ofFn f):=by
    induction j with|zero=> simp|succ j ih=>
       push_cast; have h: (fun i:Fin n=>f (i+(↑j+1)))=(fun i=>f ((i+1)+↑j)):=funext fun i=>by rw [add_comm (↑j:Fin n) 1, add_assoc]
       rw [h]; exact (roll_a (fun i=> f (i+(↑j:Fin n)))).trans ih
 simpa using he j.val
lemma turn(j:Fin n) : ∃ E:Equiv.Perm (Cage n),∀ x i,color (E x) i=color x (i+j):=by
 let Y:= Equiv.arrowCongr (Equiv.addRight j).symm (Equiv.refl Tone); have hu(x:Fin n→ Tone): polar (ofFn x)=polar (ofFn (Y x)):=(roll x j).symm
 refine ⟨Equiv.sigmaCongr Y (fun x=> Fin.castOrderIso (hu x)),?_⟩ -- want equiv not iso
 intro x i; rfl
lemma colors (p:2≤n)(v:Cage n) (i:Fin n): color v i≠ color v (i+1):=by
 have hp:smooth true (ofFn (color v)):=by by_contra h; have hc: polar (ofFn v.1)=0:=clash true _ h; have ht:=v.2.isLt; omega
 apply (uv (· ≠ ·) v.1).1 (hp.resolve_left ?_) i; rw [List.length_ofFn]; omega
lemma marked {a b:Finset (Fin n)} (p:2≤n)(h:Disjoint a b)(u:∀ i∈a, i+1∉b)(v:∀ i∈b,i+1∉a): Pen a b (@color n):=by
 apply count_pen; intro x y x' y'; let g(i:Fin n): Tale:= if e:i∈a then some (true,x ⟨i,e⟩,x' ⟨i,e⟩) else if e:i∈b then some (false,y ⟨i,e⟩,y' ⟨i,e⟩) else none
 have he(i j:Bool):ofFn (scene a b (if i then x else x') (if j then y else y'))=showQ i j (ofFn g):=by
    rw [showQ,List.map_ofFn]; congr; ext k; by_cases ha:k∈a <;> by_cases hb:k∈b <;> cases i <;> cases j <;> simp [scene,ha,hb,spot,g] -- orientation
 have hp:Cycle.Chain fear (ofFn g):=by
    apply (uv ..).mpr; intro i; by_cases ha:i∈a; · unfold fear; have hh:=u i ha; by_cases hb:i+1∈a <;> simp [ha,hb,g,hh] -- simp proj
    by_cases hb:i∈b; · unfold fear; by_cases hm:i+1∈b <;> simp [ha,hb,v i hb,g,hm] -- wrong ¬ after simp shadow
    simp [ha,hb,fear,g]
 have hi:= quartZ (ofFn g) (by simpa using p) hp; unfold Bet at hi; rw [←he,←he,←he,←he] at hi; simp only [ite_true,Bool.false_eq_true,if_false] at hi
 simp_rw [moneyB a b _ _ h]; exact hi
end YM.CF.BProof.Tetra
