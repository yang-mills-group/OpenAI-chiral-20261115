import Merino.Coin.Row
import Merino.Coin.Disk
import Merino.Silk.Crown

set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 2000
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 700000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Merino.Coin
open Function Finset Lattice Cube RG Scree Skye Fock
open scoped Topology Matrix MatrixOrder Classical Matrix.Norms.L2Operator
open Py Roots QuadClock Oise Mew Neon Waxy
open Vow TreasuryFog Dial Paige Vault
open scoped YM.CF.Mew
open NormedSpace Spire Stax Tulip
attribute [local instance] opCStarAlgebra
open Py Rate LocalLimit Preparation Yoke
open Next SectorNext.Remainder Graph
open Buffered Afterglow Vale Pressure Pressure.Worth Journey Scales
variable {I:Type}[Fintype I][LinearOrder I] {n:Side}
open MeasureTheory Papyrus Papyrus.Franc
open scoped InnerProductSpace

open Tower.VacuumSelection
open Filter
variable (P:Spine)(p:Bolts)
open Brooch
set_option maxHeartbeats 1000000
local notation "L"=> P.par.R.L
variable (s i k:ℕ)
local notation "Γ"=> LedgerM P s i k
local notation "K"=> LoomM P s i
local notation "Ω"=> RegNum P s i
local notation "m"=> priceTick P
local notation "x"=> scaleM P s
local notation "U"=>P.par.U
local notation "z"=>hueM P s


structure Worthy (P:Spine)(s i k:ℕ)(p:Bolts)(f u:ℕ)(a b:ℝ):Prop where
 gift: Gifts P s i k p f u a b
 bought: Coffer P.run s i k (Corolla.cur P.par.R.L f (scaleM P s)) u

variable {f u:ℕ}{a b:ℝ}
-- signed pressure


abbrev trophy {o₀:I→Site Ω}(d:∀i':I,Dress P s i k p m (o₀ i'))(t:I→Sweep Ω):I→BProof.Obs Ω:=
 fun j=>face (t j) (d j).y (Γ).p K z

lemma Worthy.reward (y:Worthy P s i k p f u a b)
 {o₀:I→Site Ω}(o:I→Site Ω)(hp:Force_M (Γ).p.B (node∘o) u)
 (d:∀j:I,Dress P s i k p m (o₀ j))(t:I→Sweep Ω)
 (v:∀j,inReach (Γ).p (o j) (t j) (d j).y)
 (l:List I)(fresh: ψS (node∘o) l):
 ‖Journey.compass P.run i k s (row (trophy P p s i k d t) l)‖≤aroma P.par (Corolla.cur L f x) s Ω (Fintype.card I) l.length:=
 checks P.run s i k y.bought o _ hp (Gifts.earns _ _ _ _ _ y.gift o hp d t v) l fresh

/-- actual regulators on elected tuple. -/
def Windfall:Prop:=∃ F D:ℝ→ℝ,BPress.NPL F∧ BPress.NPL D∧
 ∀ (f' u':ℕ), onReg P (fun s' i' k'=>Worthy P s' i' k' p f' u' (|F (scaleM P s')|) (|D (scaleM P s')| * Qprice P s'))



theorem acquisition {C:P.Register}{w:P.Spectrum0 3}{Mc:ℕ}
 (d:Spine.RibbonCourts P C w Mc):Windfall P p:=by
 have h:= d.gala
 obtain ⟨F,D,u,v,r⟩:=casts P p h
 obtain ⟨S,_,j⟩:=d.fire
 have e:=fired P h.pleases m
 refine ⟨F,D,u,v,fun f u'=>?_⟩
 have w':=(turnover P.par).eventually (profile P.par.R u' f)
 have t:=(turnover P.par).eventually (seats P.par.R u' f)
 unfold onReg at *
 filter_upwards [r f u',j,e,w',t] with s' q b c hp hx
 filter_upwards [q,b,c] with i' u0 v0 p1 k' a'
 have hh:=v0 k' a'.1 a'.2.le
 have h0:=p1 k' a'
 have cost: pinpr L (scaleM P s')=slotFee P.par s':=rfl
 have hw:=hh.load.health
 obtain ⟨a1,a2,a3,a4⟩:=hx
 have b0:=h0.claims
 refine ⟨u0 _ a',a1,a2.trans ((show slotFee P.par s' ≤ 1 from hw.2.2.2.1.trans hw.2.2.2.2)),(le_trans (show 8≤12 from by decide) (u0 _ a').buys.high),?_,?_,?_,?_,?_,h0.cold,h0.usable,S,hh⟩
 · rw [(calibrated P a'.2.le).1]
   exact (P.run.meter.boot s').2.2.1
 · rw [b0];exact hp
 · rw [b0];exact a3

 · rw [b0];exact a4
 rw [(calibrated P a'.2.le).1]
 exact ((P.run.voyage i').paths k').paid.can.isle _
end YM.CF.Merino.Coin

