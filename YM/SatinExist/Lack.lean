import YM.SatinExist.Regale
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
variable {I:Type*}(Z:I→Stone)(D:I→Gaia)
local notation "τ" => digs D
local notation "X"=>paint Z
local notation "ρ" => germRho (τ) X
private lemma wire2 {T:Type*}(d:T→ T→ℂ)(p q:T):runes d [p,q]= d p q:=by simp [runes,claps,picks,spinC,offer,besideX,cites,Fock.cval,extendsU,beside]
private lemma wire {T:Type*}(d:T→ T→ℂ)(p q r s:T):runes d [p,q,r,s]=d p q*d r s-d p r*d q s+d p s*d q r:=by simp [runes,claps,picks,spinC,offer,besideX,cites,Fock.cval,extendsU,beside]; ring
variable (i j:I) (p q:Slot)
abbrev lawC:= billX (digs D) (paint Z)
lemma pulse_diag : Chalice.lawC Z D i i=0:=by change pencil (D i-D i) _ _=0; erw [sub_self]; simp [Onyx.pencil] -- lowercase
lemma coin : Chalice.depictionC Z [i] D=0:=by
 change ∑ i' ∈ modes (Z i).1, runes (ρ) (gang Z [] i i')=0; apply sum_eq_zero; intro b t; rw [show gang Z [] i b=[(i,setRuby (Z i).1 b,true),(i,b,false)] from rfl,wire2,funds, show billX _ _ i i= 0 from pulse_diag Z D i, ite_self]
-- two. direct Ruby mirror.be
lemma salt : let G:=gang Z; let y:= Z i; let z:= Z j; runes (ρ) (G (G [] i p) j q)= if setRuby y.1 p=q ∧ setRuby z.1 q=p then -(lawC Z D i j)*(lawC Z D j i) else 0:=by
 dsimp only
 rw [show gang Z (gang Z [] i p) j q=[(i,setRuby (Z i).1 p,true),(i,p,false),(j,setRuby (Z j).1 q,true),(j,q,false)] from rfl,wire]; simp only [funds,funds_neg,dcash]
 simp only [show billX _ _ i i=0 from pulse_diag Z D i,show billX _ _ j j=0 from pulse_diag Z D j]; split_ifs <;> simp_all [lawC]
def redstar (x:Ruby):Ruby:= ((x.2,x.1.2),x.1.1)
def stones (x:Stone):Stone:= (redstar x.1, (x.2.2,x.2.1))
lemma stones_inv(x:Stone):stones (stones x)=x:=rfl
private lemma sheet {u v:Ruby}{p q:Slot} (h:p∈modes u)(t:q∈ modes v)(z:setRuby u p=q∧setRuby v q=p): v=redstar u:=by
 rcases p with ⟨a,b⟩; rcases q with ⟨c,d⟩; simp only [setRuby,Prod.mk.injEq] at z; have he:u.1=(a,b.isLeft):=(mem_filter.mp h).2.symm; have ht:v.1=(c,d.isLeft):=(mem_filter.mp t).2.symm; apply Prod.ext (by simp [redstar,he,ht,z.1.1,z.1.2]); exact (by simp [redstar,z.2.1,he])
private lemma ruby_relate (A:Ruby)(p:Slot)(h:p∈modes A):setRuby A p∈modes (redstar A) ∧ setRuby (redstar A) (setRuby A p)=p:=by
 rcases p with ⟨a,b⟩; have he:A.1=(a,b.isLeft):=(mem_filter.mp h).2.symm; exact ⟨mem_filter.mpr ⟨mem_univ _,show (A.2,b.isLeft)= _ from (by unfold redstar; rw [he])⟩,by unfold setRuby redstar; rw [he]⟩
lemma current_sign : depictionC Z [i,j] D= if (Z j).1=redstar (Z i).1 then (numberX (Z i).1.1)* ((-lawC Z D i j)* lawC Z D j i) else 0:=by
 change (∑ v∈modes (Z i).1,∑ u∈modes (Z j).1, runes (ρ) (gang Z (gang Z [] i v) j u))= _
 simp_rw [salt]
 by_cases h:(Z j).1=redstar (Z i).1
 · rw [if_pos h]; let t:= -(lawC Z D i j)* lawC Z D j i
   have he(p:Slot)(u:p∈modes (Z i).1): (∑ v∈modes (Z j).1, if setRuby (Z i).1 p=v ∧ setRuby (Z j).1 v=p then t else 0)=t:=by
      let V:= setRuby (Z i).1 p; obtain ⟨P,Q⟩:=ruby_relate _ p u; rw [h,sum_eq_single_of_mem V P]
      · rw [if_pos ⟨rfl,Q⟩]
      intro z _ i; rw [if_neg (fun x=> i x.1.symm)]
   rw [sum_congr rfl he,sum_const]; simp only [modes,numberX,colors_card,nsmul_eq_mul,t]
 rw [if_neg h]; apply sum_eq_zero; intro p t; apply sum_eq_zero; intro q v; exact if_neg fun x=> h (sheet t v x)
variable {S:I→ℝ}
local notation "θ"=> Window.corner ∘ S
lemma vertical {r:ℝ} (p:0<r)(s:r=S j-S i): depictionC Z [i,j] (corner ∘ S)= if Z j=stones (Z i) then (numberX (Z i).1.1)*(Window.kernel r*Window.kernel r) else 0:=by
 rw [current_sign]
 let x:= Z i; let y:= Z j
 have he:lawC Z (θ) i j = if x.2.2=y.2.1 then -Window.kernel r else 0:=by change pencil (corner (S i)-_) (dnSpin x.2.2) (upSpin y.2.1)=_; change pencil (corner (S i) - corner (S j)) _ _ = _; rw [corner_sub,pencil_time, show S i-S j= -r from (by linarith), Window.kernel_neg]
 have ht:lawC Z (θ) j i= if y.2.2=x.2.1 then Window.kernel r else 0:=by change pencil (corner (S j)-corner (S i)) _ _= _; rw [corner_sub,pencil_time]; rw [s]; rfl -- adjust rw
 rw [he,ht]; change (if y.1=redstar x.1 then _ else _) =(if y=stones x then _ else _)
 by_cases b:y.1=redstar x.1
 · have e:y=stones x ↔ x.2.2=y.2.1 ∧ y.2.2=x.2.1:= by
      constructor
      · intro h; exact ⟨(congrArg (fun t:Stone=>t.2.1) h).symm,congrArg (fun t:Stone=>t.2.2) h⟩
      intro h; apply Prod.ext b; exact Prod.ext h.1.symm h.2
   rw [if_pos b] -- beware
   simp only [e]; split_ifs <;> simp_all
 rw [if_neg b, if_neg fun t=> b (congrArg Prod.fst t)] -- t uses x'
end Chalice
end YM.CF.Buffered.Ballad
