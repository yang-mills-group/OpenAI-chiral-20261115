import YM.CF.DPress.FD.Law.Tuck
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.DPress.FD
open Function Filter Lattice Finset Cash
open scoped Topology BigOperators ENNReal NNReal Classical
variable {n:Side} {r k:ℕ}
variable {I J K:Type*}
abbrev Deck(r:ℕ):= Bifold r→Cycle.C
abbrev δPsi (s:Signed) (Z:Deck r):Deck r:= Z ∘ Bifold.frame s
namespace Deck
open Cycle Bifold
variable (t:2*r<n.val)
local notation "V'"=> Site n
abbrev AS(n:Side)(r:ℕ) := Bifold r→Cycle.Skin (Site n)
abbrev cabin : Vision n r (AS n r):= Vision.bunch (fun i:Bifold r=> Cycle.Lens (jog n i) (stepP i t) (stepR i t))
abbrev X(t:2*r < n.val):=Up (cabin t).c
abbrev Role : Vision n r (X t) := (cabin t).trim
abbrev host (x: X t)(v: Site n):Deck r:= fun y=> x.val y v
lemma sees (U:Support n)(X Y:Deck.X t)(p:(Role t).looks U X Y)(i:Site n)(v:i∈U):host t X i=host t Y i:=by funext j; exact (Cycle.look U _ _).1 (p j) i v -- hU p treated Setoid syntax
lemma merit (i j:Site n)(v:i≠j)(h:separation i j ≤ r)(X:X t): host t X i≠host t X j:=by
 obtain ⟨a,w⟩:= Bifold.event t i j v h; rw [w]; intro k; apply Cycle.born (jog n a) _ (x:=X.val a) ?_ i (congrFun k a) -- have ht
 swap; · intro v; let z:=(cabin t).c; apply X.property.ne'; exact (Finset.prod_eq_zero (s:=univ) (mem_univ a) (f:=fun j:Bifold r=> Cycle.mass (jog n j) (X.val j)) v) -- tune
 exact stepP a t
lemma δΨ_id (Z:Deck r): δPsi 1 Z=Z:=by unfold δPsi; funext i; rw [comp_apply,show frame 1 i=i from Subtype.ext (Signed.act_one i.val)]
lemma δΨ_add (X:Deck r)(s t:Signed):δPsi (s*t) X=δPsi t (δPsi s X):=by funext i; simp only [δPsi,comp_apply]; rw [show frame (s*t) i= frame s (frame t i) from Subtype.ext (Signed.act_mul s t i.val)]
def root(s:Signed)(x:Site n) : Equiv.Perm (AS n r):=⟨fun u i y=> u (frame s i) (aura s x y),fun z i y=> z ((frame s).symm i) ((aura s x).symm y), fun i=>funext (fun v=>funext fun t=>by simp),fun i=>funext fun v=>funext fun t=>by simp⟩
lemma cost_root(s:Signed)(x:Site n)(U:AS n r): (cabin t).c.μ (root s x U)=(cabin t).c.μ U:=by
 let Y(i:Bifold r):=jog n i; let F(i:Bifold r):= Cycle.mass (Y i) (U i); change (∏ i:Bifold r,Cycle.mass (Y i) (U (frame s i) ∘ aura s x))= ∏ i,F i; exact Finset.prod_equiv (Bifold.frame s) (fun i=> by simp) fun i _=> Cycle.symmetry (Y i) _ (aura s x) (theme s x i) _ -- use orientation.!
-- pull periodic family by s relative coords. keep support.Proof gets suff.
abbrev Chooses [Fintype I] (P:Cash I) (e: Equiv.Perm I) := ∀ x,P.μ (e x)=P.μ x
-- Lift restricting positive support preserving ν.
section
variable [Fintype I] (P:Cash I) (e:Equiv.Perm I)(p:Chooses P e)
def similar :Equiv.Perm (Cash.Up P):= Equiv.subtypeEquiv e (fun x=> (show 0<P.μ x↔ _ from by rw [p]))
lemma costSim : Chooses P.permit (similar P e p):=fun x=> p _
end
abbrev light (s:Signed)(x:Site n):=similar _ (root s x) (cost_root t s x)
lemma w_L (s:Signed)(x:Site n) : Chooses (Role t).c (light t s x):= costSim _ _ _ -- likely ellipsis wrong
lemma follows (U:X t)(s:Signed)(x y:Site n):host t (light t s x U) y= δPsi s (host t U (aura s x y)):=rfl
end Deck
end YM.CF.DPress.FD
