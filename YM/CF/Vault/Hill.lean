import YM.CF.Vault.Sage
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vault
open Function Filter Matrix NormedSpace Finset Fock Lat Lattice Rush Cube Next.Free Laurent Fir Bloch SU Drapes Peaks Dial Tulip Scroll Branch
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators Kronecker InnerProductSpace
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 8000
section
variable {I:Type*}[Fintype I][DecidableEq I]
variable {P Q W V T K:Op I}(p:IsStarProjection P)(q:IsStarProjection Q)
include p
lemma coherex (e:star V*W=1)(h:Commute P W) : Clad P P W V (P*star V*P):=by
  have hp:P*P=P:=p.1; have hu:=mul_eq_one_comm.mp e
  have he: P*star V=star V*P:=by apply (live_of hu).mul_left_cancel; rw [←mul_assoc W,←mul_assoc W,←h.eq,mul_assoc P,hu,mul_one,one_mul] -- tune
  have hx:P*W*P=W*P:=by rw [h.eq,mul_assoc,hp]
  have ht:P*star V*P=star V*P:=by rw [he,mul_assoc,hp]
  rw [ht]; refine ⟨p,p,e,?_,?_,?_,?_⟩
  · rw [hx,←mul_assoc, mul_assoc (star V),h.eq,←mul_assoc,e,one_mul,hp]
  · rw [hx, ←mul_assoc,mul_assoc W,he,←mul_assoc,hu,one_mul,hp]
  · rw [←mul_assoc P,ht]
  rw [mul_assoc,hp]
include q
lemma clutch (e:star V*W=1) (x:T=throat P Q W+throat (1-P) (1-Q) V)(w:IsUnit T): Clad P Q W V (P*T⁻¹*Q):=by
 let A:=throat P Q W; let B:=throat (1-P) (1-Q) V
 have h:A*P=A:=by unfold A throat; rw [mul_assoc,p.isIdempotentElem.eq];
 have he:Q*A=A:=by unfold A throat; rw [←mul_assoc,←mul_assoc,q.isIdempotentElem.eq]
 have hl:Q*B=0:=by unfold B throat; rw [←mul_assoc,←mul_assoc,Porth q,zero_mul,zero_mul]
 have hp:B*P=0:=by unfold B throat; rw [mul_assoc,sub_mul 1 P,one_mul,p.isIdempotentElem.eq,sub_self,mul_zero]
 have ht : Q*T=A:=by rw [x,mul_add,he,hl,add_zero]
 have hT : T*P=A:=by rw [x,add_mul,h,hp,add_zero]
 refine ⟨p,q,e,?_,?_,?_,?_⟩
 · change P*T⁻¹*Q*A=P; rw [mul_assoc,he, ←hT,← mul_assoc, mul_assoc P, (Fock.live w).2,mul_one,p.isIdempotentElem.eq]
 · change A*(P*T⁻¹*Q)=Q; rw [←mul_assoc, ←mul_assoc A P,h,←ht,mul_assoc Q T,(Fock.live w).1,mul_one, q.isIdempotentElem.eq]
 · rw [←mul_assoc,←mul_assoc,p.isIdempotentElem.eq]
 rw [mul_assoc _ Q Q, q.isIdempotentElem.eq]
end
variable (j:ℕ)(L:Side)(ho:Odd L.val)(p:1≤j)(e:Even j)
include p ho e
lemma emin: Still L (fun G x=>∀ i: Duel, Safe (scrap true (coast j) i G (post x))∧ Safe (scrap false (urban j L ho) i G (post x))) :=by
 let t:=canUse j L ho; obtain ⟨-,A,B⟩:=cup j L ho e p t true; have ht:= marginH j L ho e p _ t
 have hp: slateQ L true (coast j):=ht.forward (fun {N P} G h x g i=> (g i true).lead); have hx: slateQ L false (urban j L ho):= ht.forward (fun {N P} G h x g i=>(g i true).beam)
 refine ((pad_safe ho (BoxD.marked A) (fiat _ _ p _) hp).plus (pad_safe ho (BoxD.marked B) (fiat_j _ _ ho p _) hx)).forward ?_; exact fun {N P} G h x g i=> ⟨g.1 i,g.2 i⟩
abbrev Commuting (b:Bool){N P:Side}(G:Ratio N P)(x:Sew N P)(i:Duel):Prop:=let y:=post x; Clad (chalk j b i G y) (umber j L ho b i G y) (fade j b i G y) (fade j (!b) i G y) (rust j L ho b i G y) ∧ Clad (lobe G b) (lobe G b) (fade j b i G y) (fade j (!b) i G y) (rusty j b i G y)
lemma vintage (b:Bool): Still L (fun G x=>∀ i:Duel, Commuting j L ho b G x i):=by
 apply (((emin j L ho p e).plus (stable_j j L ho e).2.2).plus (handsome j L ho e p b).2).forward; intro N P G h x g i
 let y:=post x
 have ht:IsStarProjection (chalk j true i G y):=(g.1.1 i).1.projection
 have hv:IsStarProjection (umber j L ho true i G y):=(g.1.1 i).2.projection
 have ha:IsStarProjection (chalk j b i G y):= by cases b; exact ht.one_sub; exact ht
 have hp:IsStarProjection (umber j L ho b i G y):=by cases b; exact hv.one_sub; exact hv
 obtain ⟨hu,he,-⟩:=motionX G j i x (h.symm ▸ ho) b (g.1.2 i)
 refine ⟨clutch ha hp he ?_ (g.2 i),?_⟩
 · unfold caveat zoom risk; rw [show umber j L ho (!b) i G (post x)=1-umber j L ho b i G (post x) by cases b<;>simp [umber,firmF],show chalk j (!b) i G (post x)=1-chalk j b i G (post x) by cases b <;> simp [chalk,firmF]] -- tune throat unfolded
 unfold rusty; rw [charge_p]; exact coherex (lobe_sq ..) he hu
lemma land_v (b:Bool): Land L (umber j L ho b) (zoom j L ho b) (rust j L ho b):=by
 refine ⟨(funds_u j L ho e p b).2, stricter j L ho e p b,(handsome j L ho e p b).1,fun i _ _ G h=> ?_,(vintage j L ho p e b).forward ?_⟩
 · rw [show umber _ _ _ _ i G _=_ from (ucap j L ho p b G h i).2,show zoom _ _ _ _ i G _=_ from zoom_id j L ho e p b G h i]; exact (brass j L ho e p _ (canUse j L ho) b).jet i.1 G h -- try
 intro N P G h x u i; have he : Commuting j L ho b G x i:= u i; let S:= (show _∧ _ from he).1; refine ⟨S.helm,?_,S.right⟩; unfold zoom risk throat; rw [←mul_assoc,←mul_assoc,S.helm.isIdempotentElem.eq]
lemma land_p (b:Bool): Land L (lendX b) (slackX j b) (rusty j b) :=by
 have he : BoxD L (ℒ false) (ℒ false) (lendX b (ι:=Duel)):= boldX L false b; have ht:BoxD L (ℒ true) (ℒ true) (lendX b (ι:=Duel)):=boldX L true b
 refine ⟨he,(he.chain (fade_cost j L ho e b)).chain ht,(ht.chain (fade_cost j L ho e (!b)).balm).chain he,fun i _ _ G h=>?_,(vintage j L ho p e b).forward ?_⟩
 · refine ⟨plus_r G b,?_⟩; unfold slackX risk throat; change _*fade _ _ i G _ *_*_= _; rw [show fade _ _ _ _ _=_ from fade_at j L ho e G h b i]
   let X:=lobe G b; unfold lendX; rw [mul_assoc,plus_r,←mul_assoc, mul_assoc X,proffer G j L ho (@Peaks.cloth j) _ b (canUse j L ho) h e,←mul_assoc,plus_r,cc_mul,cc_mul]; simp only [mul_assoc] -- tune
 intro N P G h x g i B A; have hz:= (show _∧_ from (g i : Commuting ..)).2; refine ⟨hz.helm,?_,hz.right⟩
 unfold B lendX A slackX risk throat lendX; rw [←mul_assoc,←mul_assoc,(lobe_sq ..).isIdempotentElem.eq]
end YM.CF.Vault
