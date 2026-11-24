import YM.CF.Floe.Poles
import YM.CF.Floe.Hop
import YM.CF.Drapes.Awash
set_option autoImplicit false
noncomputable section
namespace YM.CF.Floe
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology Kronecker
open Filter NormedSpace Function Lattice Lat SU Fock Phase Cube Tenant Branch Drapes Metric Finset
attribute [local instance] opCStarAlgebra
variable {N:Side}{a b c d r:ℝ}
abbrev FrameP(N:Side):=BayP N→Op (Model N)
abbrev pMat:= (z:IndexK)→ FrameP z.1
local notation "D"=> Kelp N a
def tag (u:Bool)(N:Side)(a:ℝ):= if u then varp (a:=a) (N:=N) else (varp (a:=a) (N:=N)).reverseV
@[simp] lemma tag_other(u:Bool)(N:Side)(a:ℝ):(tag u N a).reverseV=tag (!u) N a:=by
 cases u <;> simp only [tag,Bool.not_true,Bool.not_false,ite_true,Bool.false_eq_true,ite_false]; let X:= @varp N a; change X.reverseV.reverseV=X
 have hx : ∀ (L: Tag (ku (N:=N) (a:=a))), L.reverseV.reverseV=L:=by
   rintro ⟨F,g⟩; unfold Tag.reverseV; congr 1; ext x:1; apply Subtype.ext; change cc (cc _)=_; ext i j; change star (star _)=_; rw [star_star]; rfl
 exact hx _
abbrev certS (F:pMat)(u v:Bool)(a b r:ℝ):Prop:=∀ j:IndexK,Crown (badge _) (tag u j.1 b) (tag v j.1 b) a r (fun x=>F j x.val)
variable {F G:pMat}{u v w:Bool}
lemma slim_e(h:certS F u v a b r)(p:c ≤ b):certS F u v a c r:=by
 intro i; let X:=Kelp i.1 b; let Y:=Kelp i.1 c; let f(y:Y):X:=⟨y.val,cut_j y.property p⟩; have ht:Towards (ku (a:=b) (N:=i.1)) (badge _) (ku (a:=c) (N:=i.1)) (badge _) f 1:=by
   refine ⟨Continuous.subtype_mk continuous_subtype_val _,rfl,rfl,fun _ _=>rfl,fun S x y=>by rw [one_mul]; exact le_rfl,fun g h V u z t=>?_⟩
   exact h V u (f ∘ z) t
 have hu(w:Bool) : (tag w i.1 b).run=(tag w i.1 c).run:=by cases w<;> rfl
 exact ht.bring (hu u) (hu v) (h i) le_rfl
abbrev LedgerP (F:pMat)(u v:Bool):Prop:=∃ a b r:ℝ,0<a∧0<b∧0<r ∧ certS F u v a b r
variable {u v w z:Bool} (h:LedgerP F u v)
namespace LedgerP
lemma keeps(h:certS F u v a b c)(p:0<a)(q:0<b):LedgerP F u v:=by refine ⟨a,b,max 1 c,p,q,lt_max_of_lt_left one_pos,fun i=>(h i).books (le_max_right ..)⟩
variable (g:LedgerP G w z)
include h g
lemma like :∃ a b r:ℝ,0<a∧0<b∧0<r∧certS F u v a b r ∧ certS G w z a b r:=by
 obtain ⟨a,b,c,h,h',l,A⟩:=h; obtain ⟨d,e,f,t,u,p,B⟩:=g; exact ⟨min a d,min b e,max c f, lt_min h t,lt_min h' u,lt_max_of_lt_left l,fun i=> ((slim_e A (min_le_left b e) i).books (le_max_left ..)).drop (min_le_left ..),fun i=> ((slim_e B (min_le_right b e) i).books (le_max_right ..)).drop (min_le_right ..)⟩
omit g
lemma plus (g:LedgerP G u v):LedgerP (fun i x=>F i x+G i x) u v := by obtain ⟨_,_,_,p,x,y,h,h'⟩:=like h g; exact keeps (fun i=> (h i).plus (h' i)) p x
lemma times (g:LedgerP G v w):LedgerP (fun i x=>F i x*G i x) u w := by obtain ⟨_,_,_,p,x,y,h,h'⟩:=like h g; exact keeps (fun i=> (h i).product (h' i) p.le) p x
lemma scale_t(k:ℝ):LedgerP (fun i x=> k • F i x) u v:=by obtain ⟨a,b,r,l,p,h,t⟩:=h; have hx:=fun i=> (t i).scale (k:ℂ); have hZ:(fun i x=>(k:ℂ) • F i x)=(fun i x=> k • F i x):=funext fun i=>funext fun x=>(by rw [show (k:ℂ) = k • (1:ℂ) by simp, smul_assoc, one_smul]); exact hZ ▸ keeps (F:=fun i x=>(k:ℂ) • F i x) hx l p
lemma minus :LedgerP (fun i x=> -F i x) u v:=by simpa only [neg_one_smul] using scale_t h (-1)
lemma sub (g:LedgerP G u v):LedgerP (fun i x=>F i x-G i x) u v:=by simp_rw [sub_eq_add_neg]; exact plus h (minus g)
lemma mirrorL:LedgerP (fun i x=>star (F i (echoL x))) v u:=by
 obtain ⟨a,b,c,p,t,u,h⟩:=h; exact keeps (fun i=>(h i).impose eθ eθ_o (fun g d=>ele_e g d) ema echo_valid) p t
omit h in
private lemma tr_l {s t: Tag (ku (a:=a) (N:=N))}{f:Raw (Kelp N a) (Model N)} (h:Crown (badge _) s t b r f) : Crown (badge _) t.reverseV s.reverseV b r fun x=>(f x)ᵀ:=by
 obtain ⟨F,C,p,t,h⟩:=h; refine ⟨_,_,fun i=>⟨(show Ticket _ _ i (Function.swap (C i)) (fun x=> (F i x)ᵀ) from ?_), fun j k=> (p i).fuel k j⟩,t.flip,?_⟩
 · convert! (p i).toTicket.starT.ccT using 2; -- tune
   funext z; unfold cc; rw [star_star]
 intro x; dsimp only; rw [h]; simp only [Matrix.transpose_sum]
lemma transL:LedgerP (fun i x=>(F i x)ᵀ) (!v) (!u):=by obtain ⟨a,b,c,p,t,u',h⟩:=h; have ht:=fun i=>tr_l (h i); simp only [tag_other] at ht; exact keeps ht p t
lemma ccL:LedgerP (fun i x=>cc (F i (echoL x))) (!u) (!v):=transL (mirrorL h)
omit h
lemma identL(u:Bool): LedgerP (fun _ _=>1) u u:= keeps (a:=1) (b:=1) (fun i=>Crown.ident ..) zero_lt_one zero_lt_one -- tune
end LedgerP
end YM.CF.Floe
