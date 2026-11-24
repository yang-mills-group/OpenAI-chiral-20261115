import YM.CF.Reed.Dance
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Bide.Temper
open Fock NormedSpace Function Filter Finset Reed
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
attribute [local instance] opCStarAlgebra
variable {I:Type*}[LinearOrder I][Fintype I]
/-- Equality of row functional. -/
def rel (p:Wave I)(A B:FC I):Prop:=acts (star A) p=acts (star B) p
variable {p:Wave I} {A B U V W:FC I} {b a:Bool} {S F:Finset I}
namespace rel
lemma trans (h:rel p A B)(g:rel p B U): rel p A U:= Eq.trans h g
lemma mul_right (h:rel p A B)(X:FC I):rel p (A*X) (B*X):=by unfold rel; rw [star_mul,star_mul,act_mul,act_mul,show acts _ _= _ from h]
lemma plus (h:rel p A B)(g:rel p U V) : rel p (A+U) (B+V):=by unfold rel; rw [star_add,star_add,act_add,act_add,show acts _ _= _ from h,show acts _ _=_ from g]
lemma smul (h:rel p A B)(c:ℂ): rel p (c•A) (c•B):=by unfold rel; rw [star_smul,star_smul,act_smul,act_smul,show acts _ _= _ from h]
lemma bra (h:rel p A B)(q:Wave I): inner ℂ p (acts A q)=inner ℂ p (acts B q):=by rw [←act_inner,←act_inner,show acts _ _=_ from h]
end rel
local notation "tα"=> (think S)
abbrev lost (S:Finset I)(i:I):= star ((think S).term i)
lemma bad_null(i:I):rel (basisKet S) (lost S i) 0:=by unfold rel lost; rw [star_star,star_zero,act_zero]; by_cases h:i∈ S; rw [show (tα).term _=put i from if_pos h]; exact (put_act ..).trans (if_pos h); rw [show (tα).term i= -takeF i from if_neg h,act_neg,take_act,if_neg h,neg_zero]
lemma mark_z (S:Finset I)(i j:I): (think S).term i*lost S j+lost S j*(think S).term i=if i=j then 1 else 0:=by
 let F:FC I:=put i; let G:FC I:= put j; unfold lost; by_cases p:i∈ S <;> by_cases q:j∈ S
 · rw [show (think S).term i= _ from (if_pos p : (think S).term i=put i),show (think S).term j=put j from if_pos q]; rw [add_comm,show star (put j)=takeF j from rfl,mixed]; simp [eq_comm]
 · rw [show (think S).term i=put i from if_pos p,show (think S).term j= -takeF j from if_neg q,star_neg,takeF,star_star,mul_neg,neg_mul, ←neg_add,put_put,neg_zero,if_neg (fun (h:i=j)=> q (h ▸ p))]
 · rw [show (think S).term i= -takeF i from if_neg p,show (think S).term j=put j from if_pos q,show star (put j)=takeF j from rfl,mul_neg,neg_mul, ←neg_add,take_take,neg_zero,if_neg (fun (h:i=j)=> p (h.symm ▸ q))]
 rw [show (think S).term i= -takeF i from if_neg p,show (think S).term j= -takeF j from if_neg q,star_neg,neg_mul_neg,neg_mul_neg,show star (takeF j)=put j from star_star _,mixed]
lemma picky : ∀ c:Bool,Sector.grainB (a.xor b) c=Sector.grainB a c* Sector.grainB b c:=by intro c; cases a <;> cases b <;> cases c<;> simp [Sector.grainB]
lemma brush_right (i:I) (h:Fine S F b A) : ∃ D, Fine S F (b.xor true) D∧ A*lost S i=D+ Sector.grainB b true • (lost S i*A):=by
 let B:=lost S i
 induction h with
 | empty=> refine ⟨0,Fine.empty _,?_⟩; simp
 | one=> refine ⟨0,Fine.empty _,?_⟩; simp [Sector.grainB]
 | seed j u=> rw [show Sector.grainB true true=(-1:ℂ) from rfl]; refine ⟨if j=i then 1 else 0,(by split<;>first|apply Fine.empty|exact Fine.one),?_⟩; rw [←mark_z]; module
 | @grow P Q a b v w p q=>
    obtain ⟨D,f,t⟩:=p; obtain ⟨E,u,k⟩:=q; let g:=Sector.grainB b true
    refine ⟨P*E + g • (D*Q),?_,?_⟩
    · apply Fine.add; rw [Bool.xor_assoc]; exact v.grow u
      rw [Bool.xor_assoc, Bool.xor_comm b, ← Bool.xor_assoc]; exact (f.grow w).scale g
    rw [mul_assoc,k,mul_add,Algebra.mul_smul_comm,←mul_assoc P,t,add_mul,Algebra.smul_mul_assoc,smul_add,picky true]; unfold g; rw [smul_smul, mul_assoc (lost _ _),add_assoc,mul_comm (Sector.grainB a true)]
 | add _ _ p q=> obtain ⟨V,u,h⟩:=p; obtain ⟨W,t,x⟩:=q; refine ⟨_,u.add t,?_⟩; rw [add_mul,h,x,mul_add,smul_add,add_add_add_comm]
 | scale _ c p=> obtain ⟨X,t,q⟩:=p; refine ⟨_,t.scale c,?_⟩; rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc,q,smul_add,smul_comm c]
abbrev comf(S T:Finset I)(b:Bool)(A:FC I):Prop:=∃ X,Fine S T b X∧ rel (basisKet S) A X
namespace comf
lemma fine (h:Fine S F b A): comf S F b A:=⟨A,h,rfl⟩
lemma roller (A:FC I)(h:Fine S F b A)(i:I):comf S F (b.xor true) (A*lost S i):=by
 obtain ⟨V,t,q⟩:= brush_right i h; have hp:= ((bad_null (S:=S) i).mul_right A).smul (Sector.grainB b true); rw [q]; refine ⟨V,t,?_⟩; have hx:= rel.plus (show rel (basisKet S) V V from rfl) hp; simpa using hx
lemma scale (U:comf S F b A)(x:ℂ):comf S F b (x•A):=by obtain ⟨U,v,p⟩:=U; exact ⟨_,v.scale x, p.smul x⟩
lemma neg (h:comf S F b A) : comf S F b (-A):= by simpa using h.scale (-1)
lemma plus (h:comf S F b A)(p:comf S F b B): comf S F b (A+B):=by obtain ⟨V,t,q⟩:=h; obtain ⟨W,u,e⟩:=p; exact ⟨_,t.add u, q.plus e⟩
lemma through (p:comf S F b B)(u:rel (basisKet S) A B):comf S F b A:=by obtain ⟨X,p,y⟩:=p; exact ⟨X,p,u.trans y⟩
lemma knows (h: Sector F b A): ∀ B a,Fine S F a B→comf S F (a.xor b) (B*A):=by
 induction h with
 | zero=> intro B a _; rw [mul_zero]; exact fine (Fine.empty _)
 | one=> intro B a h; rw [mul_one, Bool.xor_false]; exact fine h
 | up i v=>
    intro B a p; by_cases h:i∈S; rw [←show (think S).term i=put i from if_pos h]; exact fine (p.grow (Fine.seed i v))
    have hv:put i= -lost S i:=by unfold lost; rw [show (think S).term i= -takeF i from if_neg h,star_neg,takeF,star_star,neg_neg]
    rw [hv,mul_neg]; exact (roller B p i).neg -- fix parser
 | down i v=>
    intro B a p; by_cases g:i∈S; rw [show takeF i=lost S i from (congrArg star (if_pos g : (think S).term i= put i)).symm]; exact roller B p i
    have hv: takeF i= -(think S).term i:=by rw [show (think S).term i= -takeF i from if_neg g,neg_neg]
    rw [hv,mul_neg]; exact (fine (p.grow (Fine.seed i v))).neg
 | add _ _ i j=> intro B a p; rw [mul_add]; exact (i B a p).plus (j B a p)
 | scale _ c i=> intro B a p; rw [Algebra.mul_smul_comm]; exact (i B a p).scale _
 | @mul a b P Q _ _ i j=> intro B q h; obtain ⟨X,t,y⟩:=i B q h; rw [←mul_assoc,← Bool.xor_assoc]; exact through (j _ _ t) (y.mul_right Q)
lemma final (h: Sector F b A): comf S F b A:=by simpa only [one_mul,Bool.false_xor] using knows (S:=S) h 1 false Fine.one
end comf
end YM.CF.BProof.Bide.Temper
