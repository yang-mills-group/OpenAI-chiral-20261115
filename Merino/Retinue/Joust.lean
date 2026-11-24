import Merino.Retinue.Saddle
import Merino.Brooch.Revenue

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Retinue

open Function Finset Fock Scroll Spire Sault
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Lattice Cube Scree Skye Sour Drapes Tulip Lat Branch Swell
open Thera Hest Levier RG Salt Mew Stax
open Dial Vow Brooch

open Paige Vault Roots
open Py Rate LocalLimit Preparation Filter Buffered.Afterglow.Tower.VacuumSelection
set_option maxHeartbeats 800000
open Vale Rive
variable (P:Spine)(s i k:ℕ)
local notation "L"=> P.par.R.L
local notation "N"=> RegNum P s i
local notation "R"=> LedgerM P s i k
local notation "x"=> scaleM P s
local notation "Q"=>Qprice P s
local notation "h"=>P.par.h
local notation "K"=>LoomM P s i
local notation "M"=> priceTick P
local notation "A"=>P.par.U
local notation "J"=>P.par.J
variable (p:Bolts)


variable (f u d:ℕ)

abbrev pip :=bit d (scaleM P s)*Qprice P s
structure Court (d f u:ℕ):Prop where
 granted:∃ cost:ℝ,
  Strong A R K (J).n h cost cost L (Corolla.cur L f x) u∧
  ∀ o o₀:Site N,∀ b:Dress P s i k p M o₀, ∀ t:Sweep N,∀ j:Axis,
   inReach (R).p o t b.y →
   ∃ F,Office A R K (J).n h cost cost o
     (visage b.y K (R).p t j (pip P s d))
     (lance b.y K (R).p t j (pip P s d)) F

open BPress QuadClock



abbrev Dressage(P:Spine)(p:Bolts):Prop:=∀ f u:ℕ,∃ d:ℕ,
 onReg P (fun s' i' k'=>Court P s' i' k' p d f u)
variable {C:P.Register}{z:P.Spectrum0 3}{Mc:ℕ}

lemma sets (T:BudgetPoint)(a c:ℝ)(f m:ℕ)(V:ℝ→ℝ)(l:NPL fun x'=>V x'/pinpr L x'):
 ∃ d:ℕ,∀ᶠ x' in atTop,
   let m0:=tonic (saddle L T h a c p.c x') (bit d x')
   ∃ g, ∀ Y:BudgetPoint,Y.B=Pressure.radiusB x'→Y.supportExponent=1→Y.power=2→Y.order=6→
      Corolla.Tuning Y (L).val h (|bit d x' * saddle L T h a c p.c x' *pinpr L x'|)
      (m0*pinpr L x') (V x') g (Corolla.cur L f x') m:= by
 let H:=fun (x' y:ℝ) =>
   let m0:=tonic (saddle L T h a c p.c x') y
   ∃ g, ∀ Y:BudgetPoint,Y.B=Pressure.radiusB x'→Y.supportExponent=1→Y.power=2→Y.order=6→
      Corolla.Tuning Y (L).val h (|y * saddle L T h a c p.c x' *pinpr L x'|)
      (m0*pinpr L x') (V x') g (Corolla.cur L f x') m
 apply bridle H
 intro v e
 have Z:=e.mul (bills L T h a c p.c)
 exact Corolla.seasons 2 6 (L).val f m L h P.par.height (Z.mul (nq L).pl) Z l

lemma charged
 (g:Gala P C z Mc):Dressage P p:=by
 obtain ⟨_,_,_,_,_,w⟩:=g.forward
 obtain ⟨e,_,c,_,_,he,_,hc,_,_,plan⟩:=statements P.run g.roster.prepared g.hears g.pleases M
 obtain ⟨Z,W,V,Vf,b0,post⟩:=w.scene
 have pc0:BPress.NPL fun x'=>Vf x'/pinpr L x':=⟨b0.mint⟩

 let a:=min e p.a
 have ha:0<a:=lt_min he p.decay
 let T:=P.run.meter.a 0
 intro f u
 obtain ⟨d,t⟩:=sets P p T a c f u Vf pc0
 refine ⟨d,?_⟩
 have pay:=(turnover P.par).eventually t
 have ht:=Work.E01.radiusB_tendsto.comp (turnover P.par)
 have late:=((tendsto_natCast_atTop_atTop |>.comp ht).const_mul_atTop ha).eventually_ge_atTop (2*32*↑(Fief.tileN 24))
 have zap:=fired P g.pleases M
 unfold onReg at zap ⊢
 filter_upwards [pay,post,plan,(turnover P.par).eventually (draft_π L), ht.eventually_ge_atTop 12,late,zap] with
   s' e1 e2 e3 e4 e5 e6 e7
 let z1:=2 * (Corolla.postL (L).val * (radiusM P s'))
 filter_upwards [e2,e3,e7,P.run.ir_grows.tendsto_atTop.eventually_gt_atTop z1] with i' t1 t2 t3 t4 k' adm
 obtain ⟨pr,pw,U,_,n,s0,r,j,o,v,_,q,rho,_⟩:=t2 k' adm.2


 obtain ⟨wide,lease⟩:=(t1 k' adm.2).radius -- reducible whnf
 obtain ⟨z',Tg⟩:=e1
 let Rz:=LedgerM P s' i' k'
 have A1:=Tg Rz.p j q v o
 let zz:=scaleM P s'
 have nudge:2 * (Corolla.postL (L).val * Rz.p.B)< (More (RegNum P s' i')).val:=by
    rw [show Rz.p.B=radiusM P s' from j]
    exact (t4.trans_le (Vale.amplit ..)).trans_le (Nat.le_mul_of_pos_right (RegNum P s' i').val two_pos)
 have Q0:0<pinpr L zz:=pow_pos e4.2.1 _
 let hb:12≤Rz.p.B :=j ▸ e5
 let cost:= tonic (saddle L T h a c p.c zz) (bit d zz)*pinpr L zz
 rw [abs_mul _ (pinpr ..), abs_of_pos Q0] at A1
 refine ⟨cost,⟨⟨Vf zz,z',A1,lease⟩,wide,(t3 k' adm).usable,nudge,hb⟩,?_⟩


 let l1:DockPulse Rz.p (LoomM P s' i') (J).k P.par.d a h 32 24 (J).n:={U with
    hint:=ha
    goal:=by rw [show Rz.p.B=radiusM P s' from j]; exact e6}
 have em:a≤ e:=min_le_left ..
 have hq:0<Qprice P s':=pow_pos e4.2.1 _
 let l2:License Rz L zz (LoomM P s' i') A a c h (J).k M (J).n:=
    ⟨l1,pr.drop em,pw.drop em,r,rho,
     equips P.par _ Rz (orbitalInterest P.run g.roster.prepared s' i' k' adm.2) n,n,s0,j,hq⟩

 have ord:T.order=Rz.p.order:=((P.run.meter.boot 0).2.2.2.2).trans o.symm
 intro o₁ o₀ b θ j' hrk
 exact credits l2 θ j' b.ticket.hem (min_le_right ..) T ord o₁ hrk hb b.ticket.width

open Rive Neon
lemma solves {f u d:ℕ}(q:Court P s i k p d f u)
 {I:Type}[LinearOrder I][Fintype I]
 {o₀:I→Site N}(o:I→Site N)
 (b:∀j:I,Dress P s i k p M (o₀ j))(t:I→Sweep N)(a:I→Axis)
 (e:Force_M (R).p.B (node∘o) u)(l:∀j,inReach (R).p (o j) (t j) (b j).y):
 ∃ c:ℝ, Fall A R K o (J).n h c c (fun j=>visage (b j).y K (R).p (t j) (a j) (pip P s d)) L (Corolla.cur L f x) u:=by
 obtain ⟨c,g,r⟩:=q.granted
 exact ⟨_,procures g o e _ (fun j=>⟨_, r (o j) _ _ (t j) _ (l j)⟩)⟩
end YM.CF.Merino.Retinue
