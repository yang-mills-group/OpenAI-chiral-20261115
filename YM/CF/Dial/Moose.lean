import YM.CF.Dial.Beet
import YM.CF.Fock.Salary
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Dial
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip Fock Peaks
open scoped Topology Matrix MatrixOrder BigOperators Matrix.Norms.L2Operator Kronecker InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {ι:Type*}{L:Side}{V:Chop ι}
def rentD(u:Bool) :Chop ι:= fun i N P G x=> squareD G u x
def beamV(u:Bool)(P:Chop ι): Chop ι:= fun i c f G x=> P i G x*squareD G u x *cc (P i G (chargeB x))
def moist(u:Bool)(P: Chop ι): Chop ι:=fun i _ _ G x=> beamV u P i G x *star (beamV u P i G (chargeB x))+ (1-P i G x)-1
lemma moist_p (u:Bool)(P:Chop ι){N F:Side}(G: Ratio N F)(x:Sew N F)(i:ι): moist u P i G (post x)=shrinkV (P i G (post x)) (squareD G u (post x))-1:=by
  unfold moist; rw [charge_p]; simp only [beamV,charge_p,shrinkV,body]
def slateQ(L:Side)(v:Bool)(P:Chop ι):= Still L fun G x=>∀ i,IsStarProjection (P i G (post x))
lemma tight (u:Bool)(L:Side)(P:Chop ι)(v:BoxD L (u,true) (u,true) P)(hp: Odd L.val)(h:slateQ L u P)
    (p:∀ i {N F:Side}(G: Ratio N F),G.count=L→ P i G (vacancyY N F)*helmC G=helmC G*cc (P i G (vacancyY N F))) : BoxD L (u,true) (u,true) (moist u P) ∧ (Still L fun G x=>∀ i,‖moist u P i G (post x)‖ ≤ 1/2):=by
  have he: BoxD L (u,true) (u,false) (beamV u P):= v.corner (tablesB _ u L hp)
  have hx:BoxD L (u,true) (u,true) (moist u P):=((he.chain he.balm).add (BoxD.one.sub v)).sub BoxD.one; refine ⟨hx,?_⟩
  obtain ⟨k,K⟩:= (show Still _ _ from h).stamp
  have hh(i) {N F:Side}(G: Ratio N F)(hg:G.count=L)(hz:k ≤N.val): moist u P i G (vacancyY N F)=0:=by
    let X:=(vacancyY N F); let S:= P i G X; let Y:=squareD G u X
    have h1: IsStarProjection S:= K G hg hz i
    have h2:S*Y=Y*cc S:=by rw [show Y= _ from helm_eq G u]; exact p i G hg
    have h3:Y∈unitary _ := unit_square G u _
    have h4:shrinkV S Y=1:=by
      rw [shrinkV,thud h1 h2, star_mul,h1.isSelfAdjoint.star_eq,←mul_assoc,mul_assoc S Y (star Y),show Y*star Y=1 from h3.2,mul_one,h1.isIdempotentElem.eq]; abel
    rw [vacancyY,moist_p]; exact sub_eq_zero.mpr h4
  obtain ⟨a,m,d,b,r,H⟩:= pay_small hx @hh (show 0<(1:ℝ)/2 by norm_num)
  apply (show Tills L (fun G x=>∀ i,‖moist u P i G x‖≤1/2) from ⟨m,b,r,fun G he hv x f i=> (H i G he hv).lib.boundOp d.le ⟨_,f⟩⟩).gilded
def ingot(u:Bool)(P:Chop ι):Chop ι:= fun i _ _ G x=>pencil (moist u P i G x)
def Medal(L:Side)(u:Bool)(P : Chop ι):Prop:=BoxD L (u,true) (u,true) (ingot u P)∧ Still L fun G x=>∀ i,
 let S:=P i G (post x); let V:=(ingot u P i G (post x)).trace.re /4; let Y:= squareD G u (post x); Real.exp V= ‖filled S Y‖
lemma affluent(u:Bool)(L:Side)(P:Chop ι)(v:BoxD L (u,true) (u,true) P)(hp:Odd L.val)(h:slateQ L u P)
    (p:∀ i{N F:Side}(G: Ratio N F),G.count=L→ P i G (vacancyY N F)*helmC G=helmC G*cc (P i G (vacancyY N F))): Medal L u P:=by
  obtain ⟨q,t⟩:= tight _ _ _ v hp h @p; refine ⟨ink q (show 0<(1:ℝ)/2 by norm_num) (by norm_num) t,?_⟩; apply (t.plus h).forward
  intro N F G he x hs i S V Y; have he:= (hs.1 i).trans_lt (by norm_num : (1:ℝ)/2<1); rw [moist_p] at he
  unfold V ingot; rw [moist_p,← tally_log he]; exact to_sal (hs.2 i) (skew_square G u x) he
variable (j:ℕ)(L:Side)(ho:Odd L.val)(hj:Even j)(hp:1≤j)(T:Script Male)(t:Use j L T)(u:Bool)
include hj hp ho t
lemma scour :Medal L false (mateF (wh j L ho u)) ∧ Medal L true (mateF (foal j u)):=by
  have p:=brass j L ho hj hp T t u
  refine ⟨affluent _ _ _ p.lay ho (p.sky.forward (by intro N P G he x h; exact fun i=> (h i).1)) (fun i N F G he=> (p.jet i G he).1), affluent _ _ _ (BoxD.marked (cup j L ho hj hp t u).2.1) ho ?_ (fun i N F G he=> homeT G j i u hp)⟩
  apply (marginH j L ho hj hp T t).forward; intro N F G he x h i; exact (h i u).lead
end YM.CF.Dial
