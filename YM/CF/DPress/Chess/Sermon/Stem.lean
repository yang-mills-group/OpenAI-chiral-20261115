import YM.CF.DPress.Chess.Sermon.Buyer
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.Chess.Sermon
open Function Filter Lattice RG Wilson MeasureTheory ProbabilityTheory Push.GridApprox FD Skye Tree Precision Rush Spire Scree Lift Transit Bough Turn Push.SectorMeasure Tulip
open Fock Finset Girt
open Cube (More assembly node)
open scoped Topology BigOperators Pointwise Classical ENNReal NNReal Bough Matrix.Norms.L2Operator YM.CF.BPress
attribute [local instance] opCStarAlgebra
variable (W:Wall) {n m:Side}{K:Ratio n m}{S:StepData (More n) (More m)}{r ℓ d:ℕ}{β u k:ℝ}{P:Loom n}
open Lat Scroll Peaks
local notation "R_" => W.crop n Wall.rail
local notation "Q_" => W.crop n ℓ
local notation "ΨA"=> W.boost K.count
namespace Learn
def weight (g:Pane n→ℝ) (A:HT n): HT n:= fun s=> g s.1 • A s
lemma charged {g:Pane n→ℝ}{A:HT n} (p: Envelope g)(t: LocalOn (R_) g)(v:Learn W ℓ A): Learn W ℓ (weight g A):=⟨fun i j u=>by unfold weight; rw [v.bits i j u,t i.1 j.1 u.1],Env.scale (Env.along p measurable_fst) v.envelope,fun i=> by rw [weight,←Complex.coe_smul]; exact (show Reed.Fine _ _ _ _ from v.issue i).scale _⟩ -- tune occurrence
end Learn
def mirror (A:HT n) : HT n:=fun x=> W.θ _ (A (wake W x))
abbrev peer_H (A B:HT n)(x:Stage n):= mirror W A x * B x
lemma mir_C {A:HT n}(p:Envelope A):Envelope (mirror W A):= Env.along (pole_w A _ (W.θ_c n) p) (cap_C W n).measurable -- tune
lemma peer_C {A B:HT n}(p:Envelope A)(u:Envelope B):Envelope (peer_H W A B):= BPress.Law.prodP (mir_C W p) u
lemma mir_weight (g: Pane n→ℝ) (A:HT n) (x: Stage n) : mirror W (Learn.weight g A) x= g (W.shine n x.1) • mirror W A x:=theta_rsmul ..
lemma peer_wt (g: Pane n→ℝ) (A B:HT n) (x: Stage n): peer_H W (Learn.weight g A) (Learn.weight g B) x=(g x.1*g (W.shine n x.1)) • peer_H W A B x:=by unfold peer_H; rw [mir_weight,Learn.weight,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul,mul_comm (g _)] -- tune RHS maybe first reorder
variable {L:Side}{v:Op SU.Slot}{j:ℕ}{q:Chi}{M: Tulip.Male}(X: Scope L K S P ℓ d) (h:Tide j M K d v (W.crop n (2*ℓ))){A B:HT n}
variable (p:Learn W ℓ A)(t:Learn W ℓ B)
namespace Scope
def cred (v:S.ratio=ratio K)(a:Tour K): Tour K:= Prod.map (wake (ΨA)) (Prod.map (W.shine _) (peer_T W v)) a
local notation "ψ0"=> crop_U K q k
lemma stove_peer (x:Tour K)(p:S.ratio=ratio K) : Scroll.stanza K W.shape inert (crop_U K q k (cred W p x))= crop_U K q k x:=by
 let Z:=x.1.2; let A:= x.2.2.1; let Y:= x.2.2.2; let X:= wake (ΨA) x.1; let V:=W.boost K.count; let a:=W.joy n
 have ht:seine K (ζF W p A) q k (V.shine m Z) (W.shine n Y)= V.shine _ (seine K A q k Z Y):=by
    have ht1:V.shine m=flashA (reSweep K a):= by rw [show a=W.joy n from rfl,W.rod]
    rw [ht1]; exact seine_mv K q k S p A a Y Z
 change (stir inert _ (seine K _ q k (V.shine m Z) (W.shine n Y)),stir inert _ (W.shine n Y))= (seine K A q k Z Y, Y)
 refine Prod.ext ?_ ?_; · change stir inert _ (seine K (ζF W p A) q k (V.shine m Z) (W.shine n Y))=seine K A q k Z Y; rw [ht,← W.broad, ← Wall.shine_t]; exact Wall.twice V m _
 change stir inert W.shape (W.shine _ (x.2.2.2))= x.2.2.2; rw [← W.shine_t]; exact Wall.twice W n x.2.2.2
include p t
lemma pearl_p {L:Side}{o: Odd L.val}{v0:S.ratio=ratio K}(x:Tour K)(g:Along j L o (Vault.Thread j) true M K (unionP (ψ0 x))) : rise K M j v (peer_H W A B (alight K x)) (ψ0 x) (((retire W v0 (emit W (T:=A) (q:=q) (k:=k) h))*emit W (T:=B) (q:=q) (k:=k) h) x):=by
 let Ξt:= cred W v0 x; let y:=wake W (alight K x); let z:=crop_U K q k Ξt; have he:Scroll.stanza K W.shape inert z=ψ0 x:=stove_peer W x v0; have hu:= (h.issue (A y) (p.issue y)).peer z W.shape (Fixed.pinSpin W.i) W.Ξjet (he.symm ▸ g); rw [he,←W.broad] at hu; exact Lift.rise.mul hu ((h.issue _ (t.issue (alight K x))).Up _ g)
end Scope
end YM.CF.DPress.Chess.Sermon
