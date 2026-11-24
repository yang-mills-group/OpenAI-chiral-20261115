import Bay.C.Leather
import YM.CF.Hive.Hen
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay.C
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
open Hake Jet Sault Stax Sour
attribute [local instance] Sour.loreM Sour.loreN
open Rill Branch Tenant Drapes Leaf



open Levier Urn Ione
open Peaks

set_option synthInstance.maxSize 24000

section
variable {n:Type*}[LinearOrder n][Fintype n]{P Q:Op n}(h:IsStarProjection P)
 (g:IsStarProjection Q)(b r:Bool)(U:UNI n)(v:sings b U P=swapX r Q)
include v
-- adaptation of appleT. also on odd.
open Sault

lemma crab (x:FC (LeanV n))(hx:spanP (LeanV n) x):
 Spire.tourP U b r ((nursery P h).eval x)=(nursery Q g).eval (sauce b r U x):=by
 let H:= nursery P h; let G:= nursery Q g;let W:=sauce b r U
 change Spire.tourP U b r (H.eval x)=G.eval (sauce b r U x)
 let L:= (univ:Finset (Finset (LeanV n)))
 rw [show x=∑ i∈L, crumb x i • poke i from hx,map_sum,nutmeg,sauce,singT,win_sum,map_sum,map_sum]; refine sum_congr rfl fun i _=> ?_
 rw [map_smul,cumin,win_c,twist_scalar,map_smul,H.eval_oneT]; congr 1
 change Spire.tourP U b r (H.tag i)=G.eval (W (poke i))
 clear ‹i∈L› -- tune variable
 induction i using Finset.induction_on_min with
 | empty=> rw [poke,Poly.tag_void,Poly.tag_void,show W 1=1 from ?_,G.eval_one]; cases r <;> simp [Spire.tourP,singT,theta_one,win_i]
           unfold W sauce; rw [singT,win_i,map_one]
 | insert j S k ih=> rw [poke,Poly.tag_min _ _ _ k,Poly.tag_min _ _ _ k,nomZ,show W (_*_)=_ from singm ..]; change _=G.eval (W (put (n:=LeanV n) j)*W (poke S)); rw [fireT G (show spanP (LeanV n) (W (put j)) from (show poke {j}=put j from Poly.tag_once (cane _) _) ▸ sauceS b r U {j}) (sauceS b r U S),ih]; congr 1; exact (apple h g b r U v j).symm


lemma peel_all (x:FC (LeanV n))(q:Wave n)(z:Wave n):
 arum U b r q (ballL (nursery P h) z (acts x (vacuum _))) =
 ballL (nursery Q g) (arum U b r q z) (acts (sauce b r U x) (vacuum _)):=by
 rw [←tileL x,←tileL (sauce b r U x),←plower b r U, loaf,loaf,arum_act,
    crab h g b r U v _ (skit x)]

/- generic lawn socket over all wave inputs, omit any nonzero scalar on pilot.
 R and W actual pilot exterior onto sea using nursery P after exponent H. -/
omit v in
abbrev turfSock (P:Op n)(h:IsStarProjection P)(R:Wave n)(H m:FC (LeanV n))(y:FC n) : Prop:=
 let L:= ballL (nursery P h) R
 ∀ z,L (acts H (acts m z))= acts y (L (acts H z))

omit v in
private lemma ripe (z:Wave (LeanV n)):
 ∃ x:FC (LeanV n), acts (sauce b r U x) (vacuum _) = z :=by
 let K:=∑ i,z.ofLp i • poke i
 have t:acts K (vacuum _)=z:=by
    unfold K; rw [act_sum]
    simp_rw [act_smul,poked]
    exact basis_expand z
 obtain ⟨w,h⟩:=(twist (quantU (spice U r))).surjective K
 refine ⟨windX (b.xor r) w,?_⟩
 rw [sauce,singT,show windX (b.xor r) (windX (b.xor r) w)=w from ?_,show twist (quantU (spice U r)) w=K from h,t]
 cases b.xor r; rfl
 exact cc_cc _

lemma turfU (A R:Wave n)(H m:FC (LeanV n))(y:FC n)
 (p:turfSock P h R H m y):
 turfSock Q g (arum U b r A R) (sauce b r U H) (sauce b r U m) (Spire.tourP U b r y):=by
 intro z
 obtain ⟨x,rfl⟩:= ripe b r U z
 have hs:= congrArg (arum U b r A) (p (acts x (vacuum _)))
 rw [←act_mul,←act_mul,←act_mul,peel_all h g b r U v,arum_act, peel_all h g b r U v] at hs
 unfold sauce at hs; rw [singm,singm,singm,act_mul,act_mul,act_mul] at hs
 exact hs
end
