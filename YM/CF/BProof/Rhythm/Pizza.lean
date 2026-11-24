import YM.CF.BProof.Trek.Lit
import YM.CF.BProof.Gates.Coat
/-! BPoets in the actual projected period. All frames from Y labels. No tag pose used in
selecting which Mark branch is charged. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Rhythm
open Function Cube Spin Extension Metric MeasureTheory Dial Lat Tulip Tenant Branch Fock SU Lattice Angular Circle Hero Dream Filter Mark Mapping Finset Hearth Trek Gates
open RG Wilson Mapping.House Pricing
open scoped Topology Matrix Matrix.Norms.L2Operator ContDiff Classical BigOperators
attribute [local instance] opCStarAlgebra
variable {c:Clip}{w R v:ℝ}{S:Gates.Stage c w R v} {L:Side} {a:ℕ}{y:ℝ}{d:ℕ}(P:Gates.Stage.Entice S L a d y){s:Side}(Y:S.Setup L a s d y)
namespace Lease
open Gates.Stage Gates.Stage.Setup
-- availability at y \to \infty
variable {ψ:ℝ}
def magC (S:Gates.Stage c w R v):= (Mark.grounds S.K).choose
theorem mag_p(S:Gates.Stage c w R v): 0< magC S:=(Mark.grounds S.K).choose_spec.1
theorem mag_C(S:Gates.Stage c w R v): ∀ᶠ y:ℝ in atTop, ∀ {s:Side}(e:Bond s), cd SU.group 1 (Angular.mag y e) ≤ magC S*aA y := (Mark.grounds S.K).choose_spec.2

def wearC (S:Gates.Stage c w R v)(y:ℝ):ℝ:= magC S*aA y+xi y+wc y+S.scene.C*Face.fine y
lemma wear_p (S:Gates.Stage c w R v) : 0<wearC S y:=by
 unfold wearC; have ht:= mag_p S; have hp:= S.scene.true_p; have h₁:0<aA y:= coin_pos ..; have h₂:0<xi y:=coin_pos ..; have h₃:0<wc y:=coin_pos ..; have h₄:0<Face.fine y:=coin_pos ..; positivity
lemma wearPL (S:Gates.Stage c w R v) : NPL (wearC S) := (((PL.muln (PL.const _) (coin_n (by norm_num) _)).add (coin_n (by norm_num) _)).add (coin_n (by norm_num) _)).add ((PL.const _).muln (coin_n (by norm_num) _)) -- tune defeq
variable (T:PathData SU.group)(θ:ℝ)(x:Pawn Y.yard)(h:T.Bounds c w R v)(k:θ∈Set.Icc (1/2) 2)(hx:Along P Y T θ x)
variable {u v':ℝ}(H:Herald u v') {t:ℕ}(C:Sized t H.whole) {n:Side}(f:Ratio n s)
local notation "V₀"=> area P Y T θ x
local notation "K₀"=> color P Y T θ x -- conflict colour
local notation "S₀" => Y.yard
local notation "B₀" => Y.bad x
local notation "J₀"=> Y.g
local notation "C'"=>wearC S y
abbrev wear := actual Y.hall f V₀ S₀ K₀ x.mood
-- width from padding timeline
include h k hx
lemma nearT (M:ℕ)(H:4*M+4≤Y.yard.long)(hp:∀ e:Bond s,cd SU.group 1 (Angular.mag y e)≤magC S*aA y)
 (b:Bond s)(i:Y.yard.Index)(p:Y.yard.Vic i M (time b.1))(e:Y.Green x (i,BProof.space b.1)):SU.group.chord (V₀ b)≤ C':=by
 rw [←cd_one]; have hh:= Y.qualified P T θ x h k hx b p H e -- tune p p': maybe parameter order from lemma includes p' qualifier includes x:p
 apply (cd_triangle _ _ (mag y b) _).trans ((add_le_add (hp b) hh).trans ?_); unfold wearC; linarith only [show 0 ≤ S.scene.C*Face.fine y from mul_nonneg S.scene.true_p.le (coin_pos ..).le]
lemma lit(Q:Pad S₀ H C Y.g.count.val)(e:Herald.Warm H (DP L a y) y)(p:f.count=H.body)(g:4≤ n.val) (δ:Sound S₀ H C C')(hp:∀ b:Bond s,cd SU.group 1 (mag y b)≤ magC S*aA y): Permit (wear P Y T θ x f) C V₀ Y.g B₀ C':=by
 apply grantN S₀ Y.hall f V₀ K₀ x.mood B₀ Y.g H C p g δ
 have he:=P.dull; have hx':= (Y.proceeds P T θ x hx).2.2.2; have hh:= Y.account_f P T θ x hx.2.2.1
 have hz:= Y.force P V₀ hx' hh
 let K:= (Face.blendR S.F S.K Y.hall.g); have hv:Y.yard.long= DP L a y:=Y.length P; let E:= S.scene.costM*mA y -- qualify names
 refine (show Light S₀ V₀ K₀ x.mood B₀ Y.g H C Y.hall f y K E C' from { warm:=?_, p:= ?_,heat:=?_,camp:=?_,lens:=?_,near:=?_,already:=hx'.flat})
 · exact hv ▸ e
 · intro i u; have ht:= P.dull.frame s Y.hall rfl rfl (Y.sized P) P.Fqual (Y.yard.u i) V₀ (K₀ i); rw [←hv] at ht; refine facade (Y.yard.u i) Y.yard.long Y.hall V₀ (K₀ i) f y K E Y.yard.lL Y.yard.long_pos (hh i u) ((ht (hh i u)).1) (fun j a=> Y.spend P _ hx' i u j (by rw [Yard.leases, if_neg u]; exact a)) ?_; have h :thresh y/2 ≤ tip f.count:= p ▸ e.tip_body; exact ⟨fun x a b u=> ((hz i).1 x a b u).trans h,fun x a b u=> ((hz i).2 x a b u).trans h⟩
 · intro i hi k₁ e' h₁; rw [←cd_one]; have he:= Y.yard.haven y Y.hall V₀ K₀ hx' i hi k₁ ⟨e',h₁⟩ -- x shadow!
   apply le_trans (cd_triangle _ _ (mag y k₁) _); refine (add_le_add (hp k₁) he).trans ((le_add_of_nonneg_right (coin_pos ..).le).trans (le_add_of_nonneg_right (mul_nonneg S.scene.true_p.le (coin_pos ..).le)))
 · intro i b v x' u'; have ht:=(Y.colorful P T θ x h k b x' v (show Y.Green x _ from clear_weaker S₀ J₀ B₀ _ _ u' (by decide : 1≤2))).2; change _≤_; exact ht.trans (le_add_of_nonneg_left (add_nonneg (add_nonneg (mul_nonneg (mag_p S).le (coin_pos ..).le) (coin_pos ..).le) (coin_pos ..).le)) -- tune
 · intro i b v x' r u v'; apply (Y.fol P T θ x h k b x' v r (show Y.Green x _ from clear_weaker S₀ J₀ B₀ _ _ u (by decide : 1≤2)) (show Y.Green x _ from clear_weaker S₀ J₀ B₀ _ _ v' (by decide : 1≤2))).1; exact (yard_climb P Y T θ x hx.2.2.1 i v b).2 x' r
 intro b u e; refine nearT P Y T θ x h k hx C.blockY (by have ht:= Q.long; have h:=C.near; omega) hp b _ u (clear_weaker S₀ J₀ B₀ _ _ e (by decide : 1≤2))
end Lease
end YM.CF.BProof.Rhythm
