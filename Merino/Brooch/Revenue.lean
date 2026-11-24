import Merino.Brooch.Price

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 520000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Brooch
open Function Finset Fock Scroll Spire Sault
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Lattice Cube Scree Skye Sour Drapes Tulip Lat Branch Swell
open Thera Hest Levier RG Salt Mew Stax
open Dial Vow TreasuryFog Paige Vault Roots
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

/-- Full pose-normal-input prices on this elected tuple (applied
 as an opening at this height). -/
structure Owned (a b:ℝ):Prop where
 sweep(o₀:Site N)(d:Dress P s i k p M o₀)(t:Sweep N):
   ∃ F:Bag N,Nest A R K (J).n 24 (boxA t d.y.post) h (rScale (R).p)
           (ghost t d.y (R).p K (hueM P s)) F a b

structure Gifts (f u:ℕ)(a b:ℝ):Prop where
 allOwned:Owned P s i k p a b
 buys:Strong A R K (J).n h a b L (Corolla.cur L f x) u

variable {a b:ℝ}{f u:ℕ}

lemma Gifts.hires(y:Gifts P s i k p f u a b)
 {o₀ o:Site N}(d:Dress P s i k p M o₀)(t:Sweep N)
 (l:inReach (R).p o t d.y):
   ∃ V T, Office A R K (J).n h a b o (face t d.y (R).p K (hueM P s)) V T:=by
 obtain ⟨T,g⟩:=y.allOwned.sweep o₀ d t
 exact ⟨_,_, hire _ _ d.ticket.hem g l y.buys.high d.ticket.width⟩


lemma Gifts.earns(y:Gifts P s i k p f u a b)
 {I:Type}[Fintype I][LinearOrder I]
 {o₀:I→Site N}(o:I→Site N)(v:Force_M (R).p.B (node∘o) u)
 (d:∀j:I, Dress P s i k p M (o₀ j))(t:I→Sweep N)
 (l:∀j,inReach (R).p (o j) (t j) (d j).y):
   Fall A R K o (J).n h a b (fun j=>face (t j) (d j).y (R).p K (hueM P s)) L (Corolla.cur L f x) u:=
 procures y.buys o v _ fun j=>Gifts.hires P s i k p y _ _ (l j)

def Conveyed:Prop:=∃ F D:ℝ→ℝ,BPress.NPL F∧ BPress.NPL D∧
 ∀ (f u:ℕ), onReg P (fun s' i' k'=> Gifts P s' i' k' p f u (|F (scaleM P s')|) (|D (scaleM P s')| * Qprice P s'))

open QuadClock

lemma casts {C:P.Register}{z:P.Spectrum0 3}{Mc:ℕ}
 (g:Gala P C z Mc):Conveyed P p:=by
 obtain ⟨_,_,_,_,_,w⟩:=g.forward
 obtain ⟨e,_,c,_,_,he,_,hc,_,_,plan⟩:=statements P.run g.roster.prepared g.hears g.pleases M
 obtain ⟨Z,W,V,Vf,b0,post⟩:=w.scene
 have pc0:BPress.NPL fun x'=>Vf x'/pinpr L x':=⟨b0.mint⟩

 let a:=min e p.a
 have ha:0<a:=lt_min he p.decay
 let T:=P.run.meter.a 0
 let F:= Fcoat L T M h a c p.c p.a
 let D:= Dcoat L T M h a c p.c p.a
 have fees:=fees_npl L T M h a c p.c p.a p.decay
 refine ⟨F,D,fees.1,fees.2,fun f u=>?_⟩
 have pay:=(turnover P.par).eventually (Corolla.seasons 2 6 (L).val f u L h P.par.height fees.1 fees.2 pc0)
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
 refine ⟨⟨?_⟩,⟨Vf zz,z',A1,lease⟩,wide,(t3 k' adm).usable,nudge,j ▸ e5⟩


 let l1:DockPulse Rz.p (LoomM P s' i') (J).k P.par.d a h 32 24 (J).n:={U with
    hint:=ha
    goal:=by rw [show Rz.p.B=radiusM P s' from j]; exact e6}
 have em:a≤ e:=min_le_left ..
 have hq:0<Qprice P s':=pow_pos e4.2.1 _
 let l2:License Rz L zz (LoomM P s' i') A a c h (J).k M (J).n:=
    ⟨l1,pr.drop em,pw.drop em,r,rho,
     equips P.par _ Rz (orbitalInterest P.run g.roster.prepared s' i' k' adm.2) n,n,s0,j,hq⟩
 intro z0 d θ
 have ord:T.order=Rz.p.order:=((P.run.meter.boot 0).2.2.2.2).trans o.symm
 obtain ⟨F',b'⟩:=certs P s' i' k' p a c l2 (min_le_right ..) T ord d θ
 exact ⟨_,nestUp _ _ _ (le_abs_self _) (mul_le_mul_of_nonneg_right (le_abs_self _) hq.le) b'⟩
end YM.CF.Merino.Brooch
