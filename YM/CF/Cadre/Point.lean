import YM.CF.Cadre.Deluge
import YM.CF.Sault.Govern
import YM.CF.Scree.Locus
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Cadre
open Function Filter Topology Lattice Finset Palot
open scoped Classical
variable {A:Type*}[Fintype A][DecidableEq A]
local notation "ΣA"=> Palot.leaf A
local notation "ΣG"=> hook A
variable (Y:Palot.leaf A)(D O:Finset A)(F:hook A)
-- P supports meeting kernel leaf Y
open Fock Pastry Sault PowerSeries
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
attribute [local instance] opCStarAlgebra
variable {I:Type*}[LinearOrder I][Fintype I](W: leaf A→ Finset I)(K: leaf A→ FC I)(R: Palot.leaf A→ PowerSeries (Dough I))
local notation "ℊ"=>PowerSeries (Dough I)
variable (C:Palot.leaf A→ Palot.leaf A→ Finset (Palot.leaf A)→ PowerSeries (Dough I))(e:∀ X:leaf A,derivative (Dough I) (R X)=∑ Y:leaf A,∑ F∈ drum X Y (O∩X.val), C X Y F)
variable (η:∀ X Y:leaf A,∀ G∈drum X Y (O∩X.val),∀ i:ℕ,(coeff i (C X Y G)).val=Sault.rind (K Y * (coeff i (∏ t∈G,R t)).val))
variable (ω:∀ X:leaf A,Fock.Sector (W X) false (K X)) (t:∀ X Y:leaf A,Disjoint X.val Y.val→ Disjoint (W X) (W Y))(hU:∀ X i, Flour (W X) (coeff i (R X)).val)
lemma car_v(R: Palot.leaf A→ PowerSeries (Dough I)) : coeff 0 (hGas O R)=hGas O (coeff 0 ∘ R):=by rw [coeff_zero_eq_constantCoeff]; unfold hGas; simp_rw [map_sum,map_prod]; rfl
lemma hub_e (s:∀ i,Aqua (R i)): Aqua (hGas O R) ∧ hitU (hGas O R)=hGas O (hitU ∘ R):=by
 unfold hGas; let M:=stream O; have hk(u:ΣG): Aqua (gal u R)∧ hitU (gal u R)=∏ i∈u,(hitU ∘ R) i:=Aqua.ψ_m u R fun i _=> s i; let H:= Aqua.ψ_p M (fun i=>gal i R) fun i _=>(hk i).1; exact ⟨H.1,H.2.trans (sum_congr rfl fun i _=>(hk i).2) ⟩
abbrev poseL(I:Type*)[LinearOrder I][Fintype I](z:Dough I):=acts z.val (vacuum I)
include ω η t hU e
lemma opus {m:Type*}[LinearOrder m][Fintype m](f:Wave I→L[ℂ]Wave m)(Q:FC m)(u:∀ i,Aqua (R i))(p:∀ X: Wave I,f (acts (∑ Y:ΣA,K Y) X)=acts Q (f X)): f (poseL I (hGas O (hitU ∘ R)))=acts (NormedSpace.exp Q) (f (poseL I (hGas O (coeff 0 ∘ R)))):=by
 have ht(i:ℕ):=Eq.trans (congrArg f (scion O W K R C e η ω t hU i)) (p _)
 rw [←car_v,← (hub_e O R u).2]; exact loft f Q _ (hub_e O R u).1 ht
omit ω η t hU e
open Matrix Lat Lattice Fock Spire Scree SU Tap Proa Thera NormedSpace Dial Scroll Drapes Tulip Rush Peaks
open scoped ContDiff
variable {n:Side}
lemma dance (P F:Op (Single n))(U:Op Slot)(x:Scree.Phys n)(g:IsStarProjection P)(t:TagG P F)(v: star U=U)(p:Sea P x)(W:leaf A→Finset (LeanV (Single n)))(K:leaf A→ FC (LeanV (Single n)))(R:sailZ A (ribbon (Single n)))(C:ΣA→ΣA→Finset ΣA→ PowerSeries (ribbon (Single n)))(e:∀ X:ΣA,derivative (ribbon (Single n)) (R X)=∑ Y:ΣA,∑ T∈ drum X Y (O∩X.val), C X Y T)
 (η:∀ X Y:ΣA,∀ G∈drum X Y (O∩X.val),∀ i:ℕ,(coeff i (C X Y G)).val=Sault.rind (K Y * (coeff i (∏ t∈G,R t)).val))(wa:∀ X:ΣA,Fock.Sector (W X) false (K X))(h:∀ X Y:ΣA,Disjoint X.val Y.val→ Disjoint (W X) (W Y))(hU:∀ X i, Flour (W X) (coeff i (R X)).val)(θ:∀ i,Aqua (R i))(he:∑ X:ΣA,K X=dma P F (-(plankP n U)) (tickA n)):let c:=acts (exp (dg F)) x
 acts ((nursery P g).cook (hGas O (hitU ∘ R))) c=scaleZ U (acts ((nursery P g).cook (hGas O (coeff 0 ∘ R))) c):=by
 intro c; let f:= ballL (nursery P g) c; let A':= -(plankP n U); let S:= tickA n; let Q:=dg A'-Matrix.trace (S*A') • 1; let Y:=f.toContinuousLinearMap; have hv:∀ X:Wave (LeanV (Single n)),Y (acts (∑ i:ΣA,K i) X)=(acts Q) (Y X):=by intro Z; rw [he]; exact lease F S g t x p Z A'
 have hu(i:ribbon (Single n)):acts ((nursery P g).cook i) c=Y (poseL _ i):= (loaf (nursery P g) c i.val).symm
 rw [bet _ _ v,hu,hu]; exact opus O W K R C e η wa h hU Y Q θ hv
end YM.CF.Cadre
