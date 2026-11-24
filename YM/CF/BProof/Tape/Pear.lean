import YM.CF.Scree.Locus
import YM.CF.BProof.Tape.Gift

/-! prop:B-bra & outer Wick on the actual law. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Tape
open Function Filter Fock Finset Branch Stint Align Wick Hearth Spin Tenant Lat Lattice Tulip Cube Fig
open Dial Paige Spire Vault Scree Skye Rush Scroll Drapes Cascade
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical Hearth
attribute [local instance] opCStarAlgebra
variable {j:ℕ} {a b l r η δ c v:ℝ} {N:Side}{F: Core j a b l r N}
def pressK(x:Loft F δ c v η): Phys N:=let S:=x.val.1.val.2; Double.pressB (bandSites S true) (bandSites S false) (view x (false,false) 1)
def sunny(x:Loft F δ c v η):= Story (view x (true,false)) (view x (false,false)) (view x (true,true)) (view x (false,true))
theorem apartSeat(S:Support N): Disjoint (bandSites S true) (bandSites S false):= by apply Finset.disjoint_left.mpr; intro i p h; exact (show i.1.2∉plusHalf from mem_compl.mp ((mem_band S false i).1 h).2) (show i.1.2∈plusHalf from ((mem_band S true i).1 p).2) -- tune
section
variable {U K L : Side} {w:Odd L.val}{Y: Pricing j L w (Vault.Thread j)} (g: Grasp Y K δ)(p:g.roundZ ≤ (mid U K).val) {G: Core j a b l r (mid U K)} (x:Loft G δ c v η)
-- specialize Grasp, parameters coincide or restrict at smaller in Ride. notation C etc.
abbrev repair := carried x.val.1
def lampWorld : Phys (Scree.mid U K):= Wick.expire (G.upright (carried x.val.1)) (G.wind (carried x.val.1)) (Spire.changeM (m:=U) g (repair x) G.M)
def buh (W:Stun (mid U K)) : ℂ:=Spire.hum U K (g.cost U G.M) (repair x) W
include p in
lemma realPulse (J: Interest (mid U K)) (e:J.P=G.aim.val)(k:J.M=G.M): lampWorld g x=relV (m:=U) g J (repair x):=by
 let T:= repair x; let hT:Guard T δ:= x.val.1.val.1.property; have hp:= (show Ride .. from x.property).breeze -- tune
 unfold lampWorld relV; rw [e,k]; exact (Wick.sustain (Wick.Task.sea hp.1 (sea_g p T hT G.M)) hp).symm -- tune
include p
lemma certified (W:Pearl g)(q:Stamped j L w Y)(h:1≤j)(X:Stun (mid U K))(hp:Lat.Slow (repair x) (hook X) W.q)(ht:view x (true,false) 0=postC X)(f:sunny x)(pF:solid x) :
    inner ℂ (pressK x) (lampWorld g x)=Complex.exp (keyF x-Spire.zen (buh g x X)):=by
 let T:= repair x; let hT:Guard T δ:= x.val.1.val.1.property; let A:= G.upright T; let C:=view x (true,false) 0; let S:=changeM (m:=U) g T G.M
 have hr:Ride A (G.wind T) _ _ _ _ _ _ c η:=x.property; -- constraints
 have he:Sea A S:= sea_g p T hT G.M; have hx:Shelf A C η:= by have he:=hr.rails _ walk0; rw [rug_null hr.breeze] at he; exact he
 let t:=tickCost A C; have hz: Initial A C S (buh g x X):=by
    have hxV:= change_v W q p h G.M T hT X hp t (show Real.exp t=‖coneP j G.M (repair x) X‖ from (hx.money.trans (by change ‖filled A C‖= ‖filled A _‖; rw [show C=postC X from ht])))
    rw [Initial,show filled A C=filled A (postC X) from congrArg _ ht]; -- tune
    exact hxV
 let D:= x.val.1.val.2; let V:=G.wind T; let T':= G.θ T 1; let Z:= view x (false,false); have hf: Task T' (expire A V S):=(Wick.Task.sea hr.breeze.1 he).quantS (hr.breeze.fit 1)
 rw [pressK, lampWorld, press_value hf (apartSeat D) hr.frame]; exact writeLog hr f pF he hz -- press deck relation
lemma earnedOrder : Scores (fun i j:Double.Tree (Single (mid U K))=> driftW x i j) (Wick.claim basisKet (lampWorld g x) (pressK x)):=by
 let T:= repair x; let hT:Guard T δ:= x.val.1.val.1.property; let A:= G.upright T; let V:=G.wind T; let S:=changeM (m:=U) g T G.M; have hr:Ride A V _ _ _ _ _ _ c η:= x.property; have H:Wick.Task (G.θ T 1) (expire A V S):=(Wick.Task.sea hr.breeze.1 (show Sea A S from sea_g p T hT G.M)).quantS (hr.breeze.fit 1); let M:= x.val.1.val.2
 have he:= finalGauge H (apartSeat M) hr.frame (basisKet (n:=Double.Tree (Single (mid U K)))); simp_rw [issue_std] at he; exact he
end
end YM.CF.BProof.Tape
