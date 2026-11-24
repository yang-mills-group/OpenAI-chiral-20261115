import YM.CF.Levier.Star
set_option maxHeartbeats 350000
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Levier
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Spire Nacre
-- analytic profiles under affine pullback incl sail seams
variable {N:Side}(b:Bool)(a:Shape)
open Urn
variable {P: Side}(G:Ratio N P)(h: Odd G.count.val)(e:ℝ)(k:Sweep N)(q:Shape)
local notation "κ"=> (Iota G)
-- dual locally evaluate on conjugated ambient
variable {C:Seal (Site (More P))→Toll (Iota G)}{d p r:ℝ}{v t:Bool}
def chillF(x:cro G e):↑(cro G e):=⟨(icec x.val.1,ice x.val.2),legal_r G x.property.1,ice_o x.val.2 e x.property.2⟩
lemma wish_f(u:Sweep N)(x:cro G e): chillF G e (toWish G e u x) = toWish G e u (chillF G e x):=by
    have ht {N:Side}(A:Shape)(b: Bool)(x:Chin N): ice (gateC b A x)= gateC b A (ice x):=by funext i t; unfold ice gateC; rw [nectar_w]; rw [show (!t).xor (A.s.flip i.2)= !(t.xor (A.s.flip i.2)) by cases t<;>cases A.s.flip i.2 <;>rfl] -- tune
    exact Subtype.ext (Prod.ext (Prod.ext (ht ..) (ht ..)) (ht ..))
lemma chill_k(x:cro G e)(g:Site (More P)→E): chillF G e ((hall G e).drive g x)=(hall G e).drive g (chillF G e x):=Subtype.ext (Prod.ext (jazzI ..).symm (icy_g ..))
lemma chill_e(S:Seal (Site (More P)))(x y:cro G e):(hall G e).eval S (chillF G e x) (chillF G e y)=(hall G e).eval S x y:=by unfold hall deal chillF icec; dsimp only; rw [ice_f,ice_f,ice_f]
lemma chill_c:Continuous (chillF G e):= Continuous.subtype_mk (((burnOut.comp (continuous_fst.comp (continuous_fst.comp continuous_subtype_val))).prodMk (burnOut.comp (continuous_snd.comp (continuous_fst.comp continuous_subtype_val)))).prodMk (burnOut.comp (continuous_snd.comp continuous_subtype_val))) _
lemma chill_L(f:cro G e→ℂ)(p:Looks _ f): Looks _ fun x=>star (f (chillF G e x)):=realigns p (chillF G e) fun V h γ v=> ((snowy h _ v.fst.fst).prodMk (snowy h _ v.fst.snd)).prodMk (snowy h _ v.snd)
lemma cool_h(X: NoteS G e) (S:Seal (Site (More P)))(P: Suite (badge _) (pinH G e t) (pinH G e v) S (C S) (X S)) : Suite (badge _) (pinH G e v) (pinH G e t) S (Function.swap (C S)) (fun x=>star (X S (chillF G e x))):=by
    have he: Ticket (pinH G e t) (pinH G e v) S (C S) (X S ∘ chillF G e) := by
       refine ⟨fun g d=> ?_,fun i j=>?_⟩
       · rw [Function.comp_apply,chill_k]; exact P.frame ..
       have hp:=P.expo i j; exact ⟨hp.positive,hp.triggered,fun x=>hp.bounded _,fun x y=> (hp.variation (chillF G e x) (chillF G e y)).trans_eq (by rw [chill_e]), hp.connected.comp (chill_c G e)⟩
    exact ⟨he.starT,fun i j=> chill_L G e _ (P.fuel j i)⟩
-- Crown-S utility
variable {G e}{W X:NoteS G e}
abbrev Bisca (G:Ratio N P)(e:ℝ)(a c:Bool)(d p:ℝ)(F:NoteS G e):Prop:= ∃ C: Seal (Site (More P))→Toll (Iota G),(∀ S, Suite (badge _) (pinH G e a) (pinH G e c) S (C S) (F S))∧ Ledger d C p
lemma Bisca.flips (h:Bisca G e t v d p X):Bisca G e v t d p (fun S x=>star (X S (chillF G e x))):=by obtain ⟨C,u,w⟩:=h; exact ⟨_,fun S=>cool_h G e X S (u S), w.flip⟩ -- tune
lemma Bisca.plusK (h:Bisca G e t v d p X)(f:Bisca G e t v d r W): Bisca G e t v d (p+r) (X+W):=by obtain ⟨C,u,h⟩:=h; obtain ⟨F,p,f⟩:=f; exact ⟨_,fun S=> (u S).plus (p S), h.pairT f⟩
lemma Bisca.sm (l:ℂ)(h:Bisca G e t v d p X): Bisca G e t v d (‖l‖*p) (fun S x=> l • X S x):=by obtain ⟨C,u,h⟩:=h; exact ⟨_,fun S=> (u S).accel l, h.funds (norm_nonneg l)⟩
end YM.CF.Levier
