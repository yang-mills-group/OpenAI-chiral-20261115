import YM.SatinExist.Lack
import YM.SU5.Cordial.Fountain
set_option autoImplicit false
set_option maxHeartbeats 330000
noncomputable section
namespace YM.CF.Buffered.Ballad
open Function Filter Metric Fock Mir.Trip Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Lifted Bilinear Window Skye Emu Onyx Kea Flare Dial
open Cache Glaze
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology Kronecker
attribute [local instance] opCStarAlgebra
open Py.Rate.LocalLimit.Papal (Weaver household)
open YM.CF.Lamour YM.CF.Velvet YM.CF.Lamour.Bridge.Celeste
open Twah
namespace Chalice
/-! Adaptation of CFP SPF's uniform tangent proof. Now *matrices of generation*! also on-site hops, actual permit. -/
open Lamour.Bridge
open Cordial
open YM.Stationary (Gaia)
private lemma wick₂ {T : Type*}(d : T→T→ℂ)(p q r s : T) : runes d [p,q,r,s]= d p q*d r s-d p r*d q s+d p s*d q r:=by
  simp [runes,claps,picks,spinC,offer,besideX,cites,Fock.cval,extendsU,beside]; ring

-- lists may repeat points
private lemma wick₃ {T : Type*}(d : T→T→ℂ)(p q r s t u : T) : runes d [p,q,r,s,t,u]=
    d p q*runes d [r,s,t,u]- d p r*runes d [q,s,t,u]+ d p s*runes d [q,r,t,u]- d p t*runes d [q,r,s,u]+d p u*runes d [q,r,s,t]:=by
  simp_rw [wick₂]
  simp [runes,claps,picks,spinC,offer,besideX,cites,Fock.cval,extendsU,beside]; ring

variable {I:Type}(Z:I→DirSpin)(D:I→Gaia)(V:Window.Family)
abbrev torch (i:I):Stone:= ((V,V.1),Z i)
abbrev wicket(i:I):= Window.index V (Z i).1 (Z i).2
local notation "ξ"=>torch Z V
lemma edition (p q r:Slot)(a b c:I)(hp:p∈colors V)(hq:q∈ colors V)(hr:r∈ colors V):
 let K:= gang (ξ)
 runes (germRho (digs D) Z) (K (K (K [] a p) b q) c r)= if p=q ∧ q=r then Window.sixM (D a) (D b) (D c) (wicket Z V a) (wicket Z V b) (wicket Z V c) else 0:=by
 let P:= digs D
 let d:= germRho P Z
 have hv(i:I)(p:Slot)(h:p∈colors V):setRuby (ξ i).1 p=p:=Prod.ext (congrArg (fun z:Window.Family=>z.1) (show V =_ from ((mem_filter.mp h).2).symm)) rfl -- check
 dsimp only; change runes _ [(a,setRuby (ξ a).1 p,true),(a,p,false),(b,setRuby (ξ b).1 q,true),(b,q,false),(c,setRuby (ξ c).1 r,true),(c,r,false)]=_; rw [hv _ p hp,hv _ q hq,hv _ r hr] -- unfolds app?
 rw [wick₃]; simp only [dcash,funds,funds_neg,wick₂,mul_zero, zero_mul,sub_zero,zero_sub]
 -- use self transport
 have hp(i:I):Cordial.billX (digs D) Z i i=0:= pulse_diag (ξ) D i
 simp_rw [hp]
 by_cases h:p=q <;> by_cases t:q=r
 · subst p; subst q; simp [wicket,Cordial.billX,digs,sixM, Window.index]; ring
 · subst p; simp [t,Ne.symm t]
 · subst r; simp [h,Ne.symm h]
 simp [h,t,Ne.symm h, Ne.symm t]
lemma evening(a b c:I): depictionC (ξ) [a,b,c] D=numberX V * sixM (D a) (D b) (D c) (wicket Z V a) (wicket Z V b) (wicket Z V c):=by
 let K:=gang (ξ); let d:=germRho (digs D) Z; let C (p q r:Slot):=runes d (K (K (K [] a p) b q) c r); let S:= colors V; let T:= sixM (D a) (D b) (D c) (wicket Z V a) (wicket Z V b) (wicket Z V c)
 change (∑ p∈ S, ∑ q∈ S,∑ r∈ S, C p q r)=_
 have hx(p q:Slot)(z:p∈S)(e:q∈ S): (∑ r ∈ S,C p q r)=if p=q then T else 0:=by
    by_cases h:p=q
    · subst p; rw [if_pos rfl,sum_eq_single_of_mem q e]; · exact (edition Z D V _ _ _ a b c z z z).trans (if_pos ⟨rfl,rfl⟩)
      intro i hi v; exact (edition Z D V _ _ _ a b c z z hi).trans (if_neg (fun x=> v x.2.symm))
    rw [if_neg h]; exact sum_eq_zero (fun i ht=> (edition Z D V _ _ _ a b c z e ht).trans (if_neg fun x=> h x.1))
 have he(p:Slot)(h:p∈S): (∑ q∈S, ∑ r∈S,C p q r)=T:=by rw [sum_congr rfl (fun q t=> hx p q h t)]; simp [h]
 rw [sum_congr rfl he,sum_const]; unfold S; rw [Window.colors_card,nsmul_eq_mul]; rfl
end Chalice
end YM.CF.Buffered.Ballad
