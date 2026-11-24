import YM.CF.Sault.Cider
import YM.CF.Hive.Punt
import YM.SU5.Exchange.Seed.Transit
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Sault
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Pastry Vow
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Scree
variable {n m:Type*}[LinearOrder n][Fintype n][LinearOrder m][Fintype m]

-- extending Cook.appleT to any Fock test on the whole pilot
variable {P Q:Op n}(h:IsStarProjection P)(g:IsStarProjection Q)(b r:Bool)(U:UNI n)(v:sings b U P=swapX r Q)
include v
lemma apple_fee (i:Finset (LeanV n)): Spire.tourP U b r ((nursery P h).eval (poke i))=(nursery Q g).eval (sauce b r U (poke i)):=by
 let H:= nursery P h; let G:=nursery Q g; let W:= sauce b r U
 rw [Poly.eval_oneT]
 change Spire.tourP U b r (H.tag i)=G.eval (W (poke i))
 induction i using Finset.induction_on_min with
 | empty=> rw [poke,Poly.tag_void,Poly.tag_void,show W 1=1 from ?_,G.eval_one]; cases r <;> simp [Spire.tourP,singT,theta_one,win_i]
           unfold W sauce; rw [singT,win_i,map_one]
 | insert j S k ih=> rw [poke,Poly.tag_min _ _ _ k,Poly.tag_min _ _ _ k,nomZ,show W (_*_)=_ from singm ..]; change _=G.eval (W (put (n:=LeanV n) j)*W (poke S)); rw [fireT G (show spanP (LeanV n) (W (put j)) from (show poke {j}=put j from Poly.tag_once (cane _) _) ▸ sauceS b r U {j}) (sauceS b r U S),ih]; congr 1; exact (apple h g b r U v j).symm
lemma fullApple (Y:FC (LeanV n))(p:spanP (LeanV n) Y): Spire.tourP U b r ((nursery P h).eval Y)=(nursery Q g).eval (sauce b r U Y):=by
 rw [p,map_sum,nutmeg,sauce,singT,win_sum,map_sum,map_sum]; refine sum_congr rfl fun i _=> ?_
 rw [map_smul,cumin,win_c,twist_scalar,map_smul]; exact congrArg (_ • ·) (apple_fee h g b r U v i)
omit v

def angelK (U:UNI (LeanV n))(b:Bool)(x:Wave (LeanV n)): Wave (LeanV n):= acts (quant U.val) (dove b x)
lemma angel_act (X:FC (LeanV n))(x:Wave (LeanV n)): angelK (Scree.spice U r) (b.xor r) (acts X x)=acts (sauce b r U X) (angelK (Scree.spice U r) (b.xor r) x):=by
  unfold angelK; rw [dove_acts]; exact (Fock.swivel (quantU (Scree.spice U r)) (windX _ X) (dove (b.xor r) x))
lemma angel_sur (U:UNI (LeanV n))(b: Bool): Surjective (angelK U b):=by
  intro x; let y:=acts (star (quant U.val)) x; refine ⟨dove b y,?_⟩; unfold angelK
  rw [show dove b (dove b y)=y from ?_,←act_mul]; -- rw with let y maybe need unfold y
  · let T:=quantU U; rw [show quant U.val*star (quant U.val)=1 from T.property.2,act_one]
  cases b; rfl
  ext i :1; change star (star (y.ofLp i))=_; rw [star_star]
include v
lemma ball_hover (c:Wave n)(z: Wave n)(x:Wave (LeanV n)) :
    Spire.arum U b r z (ballL (nursery P h) c x)=ballL (nursery Q g) (Spire.arum U b r z c) (angelK (Scree.spice U r) (b.xor r) x):=by
  let Y:=∑ i: Finset (LeanV n),x.ofLp i • poke i
  have he:x=acts Y (vacuum _):=by unfold Y; rw [act_sum]; simp_rw [act_smul,poked]; exact (basis_expand ..).symm
  let K:=Scree.spice U r
  rw [he]
  rw [loaf,arum_act, show Spire.tourP _ _ _ _= _ from fullApple h g b r U v Y (snack (fun _ _=> spanS (spanPt _) _)),angel_act]
  rw [show angelK K (b.xor r) (vacuum _)=vacuum _ from ?_,loaf]
  unfold angelK vacuum; rw [dove_base]; exact quant_vac ..
end YM.CF.Sault
