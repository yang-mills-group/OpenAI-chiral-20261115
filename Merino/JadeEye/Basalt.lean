import Merino.JadeEye.Cistern
import Merino.Retinue.Saddle
import Merino.Brooch.Revenue

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.JadeEye
open Retinue

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

abbrev pip :=bit d (scaleM P s)*clearM P s
structure Court (d f u:ℕ):Prop where
 granted:∃ cost:ℝ,
  Strong A R K (J).n h cost cost L (Corolla.cur L f x) u∧
  ∀ o o₀:Site N,∀ b:Dress P s i k p M o₀, ∀ t:Sweep N,
   inReach (R).p o t b.y →
   ∃ V F,Office A R K (J).n h cost cost o
      (highZ K (R).p b.y t (pip P s d)) V F

open BPress QuadClock



abbrev Dressage(P:Spine)(p:Bolts):Prop:=∀ f u:ℕ,∃ d:ℕ,
 onReg P (fun s' i' k'=>Court P s' i' k' p d f u)
variable {C:P.Register}{z:P.Spectrum0 3}{Mc:ℕ}

lemma sets (C0 S:ℝ)(f m:ℕ)(V:ℝ→ℝ)(l:NPL fun x'=>V x'/pinpr L x'):
 ∃ d:ℕ,∀ᶠ x' in atTop,
   let m0:=tonic (vat C0 S p.c x') (bit d x')
   ∃ g, ∀ Y:BudgetPoint,Y.B=Pressure.radiusB x'→Y.supportExponent=1→Y.power=2→Y.order=6→
      Corolla.Tuning Y (L).val h (|bit d x' * vat C0 S p.c x' *pinpr L x'|)
      (m0*pinpr L x') (V x') g (Corolla.cur L f x') m:= by
 let H:=fun (x' y:ℝ) =>
   let m0:=tonic (vat C0 S p.c x') y
   ∃ g, ∀ Y:BudgetPoint,Y.B=Pressure.radiusB x'→Y.supportExponent=1→Y.power=2→Y.order=6→
      Corolla.Tuning Y (L).val h (|y * vat C0 S p.c x' *pinpr L x'|)
      (m0*pinpr L x') (V x') g (Corolla.cur L f x') m
 apply bridle H
 intro v e
 have Z:=e.mul (wet C0 S p.c)
 exact Corolla.seasons 2 6 (L).val f m L h P.par.height (Z.mul (nq L).pl) Z l

lemma charged
 (g:Gala P C z Mc):Dressage P p:=by
 obtain ⟨_,_,_,_,_,w⟩:=g.forward
 obtain ⟨_,_,_,_,_,_,_,_,_,_,plan⟩:=statements P.run g.roster.prepared g.hears g.pleases M
 obtain ⟨Z,W,V,Vf,b0,post⟩:=w.scene
 have pc0:BPress.NPL fun x'=>Vf x'/pinpr L x':=⟨b0.mint⟩

 obtain ⟨r,C0,W⟩:=Room.reserve P.par.dpos
 obtain ⟨v0,S,W1⟩:=lip SU.group
 intro f u
 obtain ⟨d,t⟩:=sets P p C0 S f u Vf pc0
 refine ⟨d,?_⟩
 have pay:=(turnover P.par).eventually t
 have ht:=Work.E01.radiusB_tendsto.comp (turnover P.par)
 have lo:=(levee S |>.comp (turnover P.par))
 have zap:=fired P g.pleases M
 unfold onReg at zap ⊢
 filter_upwards [pay,post,plan,(turnover P.par).eventually (draft_π L), ht.eventually_ge_atTop 12,(turnover P.par).eventually (coinback L p.decay),zap, lo.eventually (ge_mem_nhds W1.pos),lo.eventually (gt_mem_nhds W.haveR),lo.eventually (ge_mem_nhds zero_lt_one)] with
   s' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
 let z1:=2 * (Corolla.postL (L).val * (radiusM P s'))
 filter_upwards [e2,e3,e7,P.run.ir_grows.tendsto_atTop.eventually_gt_atTop z1,(Hem.regnum_big P s').eventually_ge_atTop (A).roundZ,(Hem.regnum_big P s').eventually_gt_atTop (2*(radiusM P s'/10+1))] with i' t1 t2 t3 t4 t5 t6 k' adm
 obtain ⟨pr,pw,U,_,n,s0,_,j,o,v,_,q,rho,_⟩:=t2 k' adm.2


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
 let cost:= tonic (vat C0 S p.c zz) (bit d zz)*pinpr L zz
 rw [abs_mul _ (pinpr ..), abs_of_pos Q0] at A1
 refine ⟨cost,⟨⟨Vf zz,z',A1,lease⟩,wide,(t3 k' adm).usable,nudge,hb⟩,?_⟩



 have th:Rz.p.threshold = Pressure.temp zz:=by
   unfold Rz
   rw [(calibrated P adm.2.le).1]
   exact (P.run.meter.boot s').1
 have ml: lime Rz.p S=Pressure.temp zz* cis S zz:=by
   unfold lime cis; rw [th,j]
   unfold zz
   ring
 have pt:Potion Rz.p (RegNum P s' i') P.par.d v0 r C0 S:=
   show Potion Rz.p (RegNum P s' i') _ _ _ _ _ from
   {sail:=W1
    ride:=W
    logx:=by rw [ml];exact e8
    expo:=by rw [ml];exact e9
    cheap:=by rw [ml];exact e10
    high:=(le_trans (by norm_num:2≤12) hb)
    wide:=by rw [j]; exact t6.trans_le (Nat.le_mul_of_pos_right _ two_pos)}


 intro o₁ o₀ b θ hrk
 exact credit (pip P s' d) θ pt b.ticket.hem p.crown.le hb b.ticket.width o hrk
   ((epoint P p M s' i' k' t5 b).trans (mul_le_mul_of_nonneg_right e6 p.crown.le))
   (branchX Rz.p zz C0 S p.c j th L Q0 (bit d zz))

open Rive Neon
lemma solves {f u d:ℕ}(q:Court P s i k p d f u)
 {I:Type}[LinearOrder I][Fintype I]
 {o₀:I→Site N}(o:I→Site N)
 (b:∀j:I,Dress P s i k p M (o₀ j))(t:I→Sweep N)
 (e:Force_M (R).p.B (node∘o) u)(l:∀j,inReach (R).p (o j) (t j) (b j).y):
 ∃ c:ℝ, Fall A R K o (J).n h c c (fun j=>highZ K (R).p (b j).y (t j) (pip P s d)) L (Corolla.cur L f x) u:=by
 obtain ⟨c,g,r⟩:=q.granted
 exact ⟨_,procures g o e _ (fun j=> r (o j) _ _ (t j) (l j))⟩
end YM.CF.Merino.JadeEye

