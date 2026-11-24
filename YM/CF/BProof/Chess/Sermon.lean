import YM.CF.BProof.Chess.Spike
/-! q is the number of remaining doubling steps. N0=2 * v * 2^q tilings at this
 intermediate slot length. Never splits a marked p subslot. Full bound in terms of
 per-finest-homogeneous-arrangement upper prices to s/P power. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Chess
open Function Filter Metric NormedSpace Finset Lattice Cube Bide Spire Bide.Half RG Fock Lat Skye Scree
open scoped Matrix.Norms.L2Operator Matrix ComplexOrder Topology BigOperators InnerProductSpace Kronecker Classical
attribute [local instance] opCStarAlgebra
variable {N L:Side}{i:Axis}{s t h z w:ℕ}
local notation "Trup"=> Scute N L i w
namespace Drum
variable {H:Obs N→ℝ}(D:Drum N L i w H)
open Scute Tack
variable {p n m k r a:ℕ}{A B c:ℝ}{x y:Scute N L i w}
abbrev stamped (p k a:ℕ)(c:ℝ)(x: Scute N L i w):Prop:= ∃ y,pair p k c y ∧ x=y*(vacant N L i w a)
local notation "ϑv" a:max=> vacant N L i w a
lemma stampX (u:stamped p k a c x): x.length=p*k+a:=by obtain ⟨F,g,v⟩:=u; rw [v,surge,g.number,lVac]
abbrev either (p k a:ℕ)(c:ℝ)(x:Scute N L i w) : Prop:= stamped p k a c x ∨ stamped p k a c x.bar
lemma stampB (u:either p k a c x): x.length=p*k+a:= u.elim stampX fun p=> (bar_l x) ▸ stampX (x:=x.bar) p
lemma twin (h:halfC L N (x.length*n)): home L ((x*x.bar)^n).length N:=by unfold home; rw [pow_l,surge,bar_l,add_mul,field_add, show field L _= _ from h, natM]; omega -- wildcard ambiguous repeated? rewrite all
lemma allowCut (p:0<n)(q:halfC L N (x.length*n)): field L x.length ≤ (More N).val:=by
 have h:x.length≤ x.length*n:=Nat.le_mul_of_pos_right _ p; have hz:= natM N; apply le_trans _ (b:=field L (x.length*n)) (by rw [show field L _=_ from q]; omega); unfold field; gcongr
include D
lemma rotation (g:0<n)(T: halfC L N (x.length*n))(W:stamped p k a c x): ∃ y: Scute N L i w,pair p (2*k) c y ∧ price H ((x*x.bar)^n)=price H ((y* vacant N L i w (2*a))^n):=by
 obtain ⟨F,z,hv⟩:= W; subst x; let V:=ϑv a; let x:= F*V; let Θ:= (F.bar*F)*V; have hh: home L ((x*x.bar)^n).length N:= twin T
 have hu:field L (F*V).length ≤ _:= allowCut (x:=F*V) g T; have hx:field L (p*k) ≤ (More N).val:=by rw [← z.number]; rw [surge,field_add] at hu; omega
 have hk: x.bar= V * F.bar:=by unfold x; rw [bar_mul _ _ hu D.pos]; exact congrArg (·*F.bar) (bar_v a)
 have hp : x.bar*x=V*Θ:=by rw [hk]; unfold x Θ; simp only [_root_.mul_assoc]
 have hF : home L ((x.bar*x)^n).length N:=by simp only [pow_l,surge,bar_l] at hh ⊢; exact hh
 refine ⟨F.bar*F,by rw [two_mul]; exact pair.paste (z.flip hx D.pos) z,?_⟩
 change price H ((x * x.bar)^n) = _; rw [D.cycle _ _ _ hh,hp,D.cycle _ _ _ (hp ▸ hF : home L ((V*Θ)^n).length N), two_mul a, vacant_plus,show Θ*V= F.bar*F*(V*V) from _root_.mul_assoc ..] -- tune hp ▸
lemma idea (g:0<n)(T:halfC L N (x.length*n))(W:either p k a c x): ∃ y: Scute N L i w,pair p (2*k) c y ∧ price H ((x*x.bar)^n)=price H ((y* vacant N L i w (2*a))^n):=by
 cases W with
 | inl W=> exact D.rotation g T W
 | inr W=>
   obtain ⟨F,v,t⟩:=D.rotation g T (x:=x.bar) W; rw [D.cycle _ _ _ (twin T)]; rw [bar_b] at t; exact ⟨_,v,t⟩ -- rw location under binder?
-- full dyadic propagation by backward induction
namespace Costed
variable (K:Costed D p c A B)
local notation "TagR" q:max m:max v:max=> A^(2*v*(m*2^q))*B^(2*v)
include K
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
lemma coreX (v:ℕ)(h:0<v)(q m a:ℕ)(T: p=a*2^q)(g:halfC L N ((p*m+a)*(v*2^q))) (α:Type)[Finite α](f:α→Scute N L i w)(π:α→α)(u:Tack π (p*m+a) f)(xS:∀ i,either p m a c (f i))(x:List α)(V:x.length=2*(v*2^q)): ∃ y:Scute N L i w, pair p (2*m) c y ∧ price H (stack f x) ≤ price H ((y* vacant N L i w (2*a))^(v*2^q)):=by
 have hp:0<v*2^q:=by positivity
 obtain ⟨b,Q⟩:= D.sign g hp u x V; obtain ⟨Z,t,v⟩:=D.idea hp (u.size b ▸ g) (xS b)
 exact ⟨Z,t,Q.trans_eq v⟩

lemma path (v:ℕ)(h:0<v)(q m a:ℕ)(T: p=a*2^q)(g:halfC L N ((p*m+a)*(v*2^q))) : ∀ (α:Type)(_i:Finite α) (f:α→ Scute N L i w)(π:α→α),Tack π (p*m+a) f → (∀ i,either p m a c (f i)) → ∀ X:List α,X.length=2*(v*2^q)→ price H (stack f X) ≤ A^(2*v*(m*2^q))*B^(2*v):=by
 -- avoid moving hp Y etc; strong auxiliary helper
 induction q generalizing m a with
 | zero=>
   intro α fα f π u x X v'; obtain ⟨y,G,z⟩:= K.coreX D v h _ m a T g α f π u x X v'; apply le_trans z; simp only [pow_zero, mul_one] at *; subst a
   rw [show vacant N L i w (2*p)=(vacant N L i w p)^2 from ?_]; swap; · rw [power_v,mul_comm p]
   -- count n
   let n:=(m+1)*v; have p0:0<n:=by unfold n; positivity
   have hh: halfC L N (p*n):=by unfold n; rw [← mul_assoc, mul_add,mul_one]; exact g
   rw [← show 2*m*v=2*v*m by ring]; exact K.rent D G 2 v n p0 hh (by unfold n; ring)
 | succ q ih=>
   intro α fα f π u x X v'; obtain ⟨y,G,z⟩:= K.coreX D v h _ m a T g α f π u x X v'; apply le_trans z; let Z:= y * ϑv (2*a); let b:=2*a; let m':=2*m; let k:=v*2^q
   have he:p=b*2^q:=by unfold b; rw [T,pow_succ]; ring
   have hM:p*(2*m)=2*(p*m):= by ring
   have hv:v*2^(q+1)=2*k:=by unfold k; rw [pow_succ]; ring
   have hU : halfC L N ((p*m'+b)*k):=by unfold m' b; rw [hv] at g; rw [hM,←mul_add,mul_comm (2:ℕ),mul_assoc]; exact g
   let V (t:Unit):=Z; let F:=code V
   have hh:stamped p m' b c Z:= ⟨y,G,rfl⟩; have hE(i:Unit×Bool): either p m' b c (F i):=by rcases i with ⟨⟨⟩,g⟩; cases g; exact Or.inl hh; exact Or.inr (by change stamped _ _ _ _ Z.bar.bar; rw [bar_b]; exact hh)
   let X:= List.replicate (2*k) ((),false); have hz:stack F X=Z^(2*k):=by simp [stack,X]; rfl -- tune
   rw [hv,← hz, show 2*v*(m*2^(q+1))=2*v*(m'*2^q) from ?_]; swap; · unfold m'; rw [pow_succ]; ring
   exact ih m' b he hU (α:=Unit×Bool) inferInstance F jump (equip V fun _=> stampX hh) hE X (List.length_replicate ..) -- order revert issues
-- can simplify IH arg named
end Costed
end Drum
end YM.CF.BProof.Chess
