import Lucent.Carve
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.Lucent
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Buffered Buffered.Lifted Skye MeasureTheory NormedSpace
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
open Ballad EmberWind Window Lamour.Bridge Celeste
open WakeInvestment

set_option maxHeartbeats 380000
open YM.Stationary (Gaia)
open Onyx Kea Flare Dial Ballad.Twah Cordial Emu Gist
open Regis Circuit
variable {I:Type}(Y:I→Role)
namespace Arity

-- small fermionic bills, follow ZecaQuorum

private lemma wick₂ {T : Type*}(d : T→T→ℂ)(p q r s : T) : runes d [p,q,r,s]= d p q*d r s-d p r*d q s+d p s*d q r:=by
  simp [runes,claps,picks,spinC,offer,besideX,cites,Fock.cval,extendsU,beside]; ring

private lemma wick₃ {T : Type*}(d : T→T→ℂ)(p q r s t u : T) : runes d [p,q,r,s,t,u]=
    d p q*runes d [r,s,t,u]- d p r*runes d [q,s,t,u]+ d p s*runes d [q,r,t,u]- d p t*runes d [q,r,s,u]+d p u*runes d [q,r,s,t]:=by
  simp_rw [wick₂]
  simp [runes,claps,picks,spinC,offer,besideX,cites,Fock.cval,extendsU,beside]; ring
abbrev moneyC := billX (outside Y) (upstairs Y)
@[simp] lemma inSelf (i:I): billX (outside Y) (upstairs Y) i i=0:=Quorum.side (Role.pt ∘ Y) (upstairs Y) i
variable (i j k:I)(a b c d e f: Slot)
lemma oneW : germ Y [(i,a,b)]=0:=by
 change runes _ [(i,b,true),(i,a,false)]=0; simp [runes,claps,picks,spinC,offer,besideX,cites,Fock.cval,extendsU,funds]

def ep [DecidableEq I](x y:I):ℂ:= if x=y then 1 else 0
lemma twoW : germ Y [(i,a,b),(j,c,d)]= -(ep b c*ep d a* (moneyC Y i j*moneyC Y j i)):=by
 change runes _ [(i,b,true),(i,a,false),(j,d,true),(j,c,false)]=_
 rw [wick₂]
 simp only [dcash, funds_neg,funds,inSelf,ite_self,zero_mul,zero_sub, moneyC,ep] -- one_mul loops!
 split_ifs<;> ring
lemma fund (Y:I→Role)(i j:I)(p q:Slot): germRho (outside Y) (upstairs Y) (i,p,true) (j,q,false)=ep p q * billX (outside Y) (upstairs Y) i j:=by rw [funds];simp [ep,ite_mul]
lemma threeW : germ Y [(i,a,b),(j,c,d),(k,e,f)] =
    ep b c*ep d e*ep f a * (moneyC Y i j * moneyC Y j k * moneyC Y k i) +
    ep b e*ep f c*ep d a * (moneyC Y i k * moneyC Y k j * moneyC Y j i) :=by
 change runes _ [(i,b,true),(i,a,false),(j,d,true),(j,c,false),(k,f,true),(k,e,false)]=_
 rw [wick₃]
 simp only [wick₂,dcash,funds_neg,fund,inSelf,mul_zero,zero_mul,moneyC]
 ring
