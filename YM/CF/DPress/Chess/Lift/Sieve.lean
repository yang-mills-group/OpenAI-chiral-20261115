import YM.CF.DPress.Chess.Lift.Wings
import YM.CF.Reed.Dance
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.Chess.Print
open Function Filter Finset Lattice Rush Scroll Lat Dial SU Branch Wilson Fock Fixed NormedSpace Spire Scree Skye Tap Reed
open scoped Topology BigOperators NNReal ENNReal Kronecker Classical Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {I:Type*}[Fintype I][LinearOrder I]{s t:Finset I}{u:Wave I}{A B C D:FC I}{b:Bool}
-- start algebraic.
abbrev Equal (u:Wave I)(A B:FC I):Prop:= acts (star A) u=acts (star B) u
lemma deeper (v:Equal u A B)(C: FC I): Equal u (A*C) (B*C):=by unfold Equal; rw [star_mul,star_mul,act_mul,act_mul,v]
lemma unitS (p:Equal u A B)(h: Equal u C D): Equal u (A+C) (B+D):=by unfold Equal; rw [star_add,star_add,act_add,act_add,p,h]
lemma colorT(p:Equal u A B)(c:ℂ):Equal u (c • A) (c • B):=by unfold Equal; rw [star_smul,star_smul,act_smul,act_smul,p]
abbrev Fantasy (D:FC I)(s t:Finset I):Prop:=∀ i∈ t,∃ c:ℂ,(think s).term i*D+D*(think s).term i=c • 1
lemma put_b (i:I) : Fantasy (put i) s t:=by
 intro k u; by_cases h:k∈s; · exact ⟨0,by rw [show (think s).term k=put k from if_pos h,put_put,zero_smul]⟩
 rw [show (think s).term k= -takeF k from if_neg h,mul_neg,neg_mul,←neg_add,mixed]; split; exact ⟨-1,(neg_one_smul ..).symm⟩; exact ⟨0,by simp⟩
lemma take_b(i:I):Fantasy (takeF i) s t:=by
 intro k u; by_cases h:k∈s; swap; · rw [show (think s).term k= -takeF k from if_neg h, mul_neg,neg_mul,←neg_add,take_take]; exact ⟨0,by simp⟩
 rw [show (think s).term k=put k from if_pos h,add_comm,mixed]; split; exact ⟨1,(one_smul ..).symm⟩; exact ⟨0,by simp⟩
lemma grain_u (a b:Bool): Sector.grainB (a.xor b) true=Sector.grainB a true * Sector.grainB b true:=by cases a<;>cases b<;>simp [Sector.grainB]
lemma peel (p:Fantasy D s t)(v:Fine s t b A):∃ X,Fine s t (b.xor true) X ∧ A*D= X+ Sector.grainB b true • (D*A):=by
 induction v with
 | empty=> exact ⟨0,Fine.empty _,by simp⟩
 | one=>exact ⟨0,Fine.empty _,by simp [Sector.grainB]⟩
 | seed i t=> obtain ⟨c,h⟩:= p i t; exact ⟨_,Fine.one.scale c,by rw [←h]; simp [Sector.grainB]⟩
 | @grow X Y a b v w ih it=>
   obtain ⟨A,F,p⟩:=ih; obtain ⟨B,H,h⟩:=it; let c:=Sector.grainB b true; refine ⟨X*B+c • (A*Y),?_ ,?_⟩
   · refine Fine.add (by rw [Bool.xor_assoc]; exact v.grow H) (Eq.mp (congrArg (fun p=> Fine _ _ p _) (show (a.xor true).xor b=(a.xor b).xor true from (by cases a<;> cases b<;> exact rfl))) ((F.grow w).scale _)) -- tune xor grind
   rw [mul_assoc,h,mul_add,Algebra.mul_smul_comm,←mul_assoc X D,p,add_mul, Algebra.smul_mul_assoc, mul_assoc D,grain_u]; unfold c; cases a<;> cases b <;> simp [Sector.grainB]; all_goals abel
 | @add a X Y _ _ ih it=>
   obtain ⟨C,p,h⟩:=ih; obtain ⟨U,k,q⟩:=it; refine ⟨C+U,p.add k,?_⟩; rw [add_mul,h,q,mul_add,smul_add]; abel
 | scale _ c ih=>
   obtain ⟨U,h,k⟩:=ih; refine ⟨c • U,h.scale c,?_⟩; rw [Algebra.smul_mul_assoc,k,smul_add,Algebra.mul_smul_comm,smul_comm c]
abbrev shadow {I:Type*}[Fintype I][LinearOrder I](D:FC I)(s:Finset I):Prop:= acts (star D) (basisKet s)=0
abbrev pre (s t: Finset I)(b: Bool)(A: FC I):Prop:= ∃ V: FC I,Fine s t b V∧ Equal (basisKet s) A V
lemma earn (q:Fantasy D s t)(h:shadow D s)(p:Fine s t b A): pre s t (b.xor true) (A*D):=by
 obtain ⟨V,h',e⟩:= peel q p; refine ⟨V,h',?_⟩; unfold Equal; rw [e,star_add,star_smul,star_mul,act_add,act_smul,act_mul,h,map_zero,smul_zero,add_zero]
lemma put_p {i:I}(h:i∈t)(p:i∈s): Fine s t true (put i):=(show (think s).term i=put i from if_pos p) ▸ .seed i h
lemma take_p{i:I}(h:i∈ t)(p:i∉s):Fine s t true (takeF i):=by
 have ht:=Fine.seed (s:=s) _ h; rw [show (think s).term i= -takeF i from if_neg p] at ht; simpa using ht.scale (-1)
lemma rise_t (s t:Finset I)(d:Bool)(P:FC I)(p:Sector t d P) :∀ (b:Bool)(Q:FC I), Fine s t b Q → pre s t (b.xor d) (Q*P):=by
 induction p with
 | zero=> intro a b q; rw [mul_zero]; exact ⟨_,Fine.empty _,rfl⟩
 | one=> intro a b q; rw [mul_one,Bool.xor_false]; exact ⟨_,q,rfl⟩
 | add _ _ i p=> intro a b h; obtain ⟨T,F,k⟩:=i a b h; obtain ⟨Y,u,v⟩:= p a b h; rw [mul_add]; exact ⟨_,F.add u, unitS k v⟩
 | mul _ _ i p=> intro a b h; obtain ⟨T,F,k⟩:=i a b h; obtain ⟨Y,u,v⟩:= p _ T F; rw [←mul_assoc,←Bool.xor_assoc]; exact ⟨Y,u,Eq.trans (deeper k _) v⟩ -- meta
 | scale _ c i=> intro a b h; obtain ⟨T,f,p⟩:=i a b h; rw [Algebra.mul_smul_comm]; exact ⟨_,f.scale c,colorT p c⟩
 | up i p=>
   intro a b h; by_cases v:i∈ s; exact ⟨_,h.grow (put_p p v),rfl⟩
   exact earn (put_b i) (show shadow (put i) s from by unfold shadow; change acts (takeF i) _=_; rw [take_act,if_neg v]) h
 | down i p=>
   intro a b h; by_cases v:i∈ s; swap; exact ⟨_,h.grow (take_p p v),rfl⟩
   exact earn (take_b i) (show shadow (takeF i) s from by unfold shadow; rw [takeF,star_star,put_act,if_pos v]) h
lemma prime (p:Sector t b A): pre s t b A:=by simpa using (rise_t s t b A p false 1 .one)
lemma all_up (w:Wave I)(p:Sea (cutM s) w)(h: Equal (basisKet s) A B): Equal w A B:=by
 have hp :Sea (cutM s) (basisKet s):=⟨by rw [cutLine,cut_basis,if_pos (mem_singleton_self _)],by simp⟩; let k:=inner ℂ (basisKet s) w; have hq:w=k • basisKet s:= (Eq.symm p.1).trans (hp.scalar (cutM_idp s) w); unfold Equal; rw [hq,map_smul,map_smul,h] -- scalar arg order
end YM.CF.DPress.Chess.Print
