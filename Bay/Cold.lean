import Bay.Estate
import Bay.Osmosis
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

open Py Py.Rate LocalLimit Preparation Buffered.Afterglow.Tower.VacuumSelection
open Zephyr.Chern
open BPress (PL NPL)
local notation "fluxV"=>Zephyr.Chern.stream
local notation "VΩ"=>Buffered.Afterglow.Tower.VacuumSelection.Spine

open Push.Uniform
open Pitching.Focus QuadClock Preparation.Yoke BScale
open Mew Vow.TreasuryFog
open scoped YM.CF.Mew


-- paid upper fees at Berth x.
section water
variable (P:VΩ)(M:ℕ)(F C D:ℝ→ℝ)
abbrev Ufull  (M:ℕ)(C:ℝ→ℝ):ℝ→ℝ:=Till.spent M C
abbrev Ubirth (P:VΩ)(M:ℕ)(D:ℝ→ℝ):ℝ→ℝ:= Till.spent M (fun x=>D x * Till.qL P.par.R x)
abbrev TopBill (P:VΩ)(M:ℕ)(F D:ℝ→ℝ):ℝ→ℝ:=Till.spells P.par.R M F D
abbrev PinNPL (P:VΩ)(V:ℝ→ℝ):= NPL (fun x=>V x/Till.qL P.par.R x)

namespace Berth
abbrev snowEta (w:Berth):ℝ:=runway w.x
abbrev sloth (w:Berth)(F:ℝ→ℝ):= Dust w.R.K w.p w.H (cipherK w.q) 1 (F w.x)
abbrev gl (w:Berth) (M:ℕ)(F C D:ℝ→ℝ):Prop:=
 Glacier w.p.B w.snowEta (F w.x) (Ufull M C w.x) (Ubirth w.P M D w.x)
    (TopBill w.P M F D w.x)
structure Rails (w:Berth):Prop where
   H6:w.p.order=6
   H2:w.p.power=2
   coin:w.p.supportExponent=1
   size:w.p.B=weeB w.x
structure Chilled (w:Berth)(M:ℕ)(F C D:ℝ→ℝ):Prop where

  funds:w.sloth F
  rail:w.Rails
  crystal:w.gl M F C D
  wide:5 ≤ w.p.B

lemma readyRails {w:Berth}{a c:ℝ}{m:ℕ}(r:w.Rig a c m):w.Rails:=⟨r.order,r.power,r.feeS,r.sizeB⟩
end Berth
structure Ice (P:VΩ)(F:ℝ→ℝ):Prop where
   rate: PinNPL P F
   frost:Dry P (fun w=>w.sloth F)
lemma Hammer.heat {P:VΩ}{Mc:ℕ}{X:TintDemand}(g: Hammer P Mc X): Heater P.par P.run:=by
 obtain ⟨n,Pay,k,G,t,w,z,p,q,o,_,v,u,_,h,τ⟩:=g.cover
 have y:=(RateCover.includes _ _ _ h).fuels (by rw [P.par.kJ]; exact ⟨2,rfl⟩) P.par.kJ.ge z p o q v u
 exact warmDust P.run y g.gate
lemma Hammer.ice {P:VΩ}{Mc:ℕ}{X:TintDemand}(g: Hammer P Mc X):∃ F,Ice P F:=by
 obtain ⟨_,_,_,F,r,k⟩:=g.heat.dust
 refine ⟨F, Till.forgeQ _ r.mint,?_⟩
 filter_upwards [k] with s e
 exact Eventually.of_forall (fun i k t=> e i k t)

structure Icicle (P:VΩ)(M:ℕ)(F C D:ℝ→ℝ):Prop where
 tune:NPL (Ufull M C)
 tick:PinNPL P (Ubirth P M D)
 charge:PinNPL P (TopBill P M F D)
 reserveE:PinNPL P (Till.markEG (TopBill P M F D))
 reserveF:PinNPL P (Till.markFG (TopBill P M F D))

 prepares : Dry P (fun w=>w.Rails→ w.Chilled M F C D)
lemma Ice.castle {P:VΩ}{F C D:ℝ→ℝ}(h:Ice P F)(M:ℕ)(p:NPL C)(q:NPL D):
 Icicle P M F C D:=by
 have t:Quench P.par.R F:=chill_iff.mpr h.rate
 obtain ⟨u,d,r,z,y,l⟩:=Till.epoch P.par.R _ _ _ M t p q
 refine ⟨chill_iff.mp u,Till.forgeQ _ d,Till.forgeQ _ r,Till.forgeQ _ z,Till.forgeQ _ y,?_⟩
 filter_upwards [h.frost, (turnover P.par).eventually l, (Work.E01.radiusB_tendsto.comp
    (turnover P.par)).eventually_ge_atTop 5] with s f k w
 refine f.mono (fun i ζ j v t=> ⟨ζ j v,t,?_,t.size.symm ▸ w⟩)
 let u:=takeUp P s i j
 exact show Glacier u.p.B u.snowEta (F u.x) (Ufull M C u.x) (Ubirth P M D u.x) (TopBill P M F D u.x)
       from t.size.symm ▸ k -- transport rewrite 
end water

namespace Berth

/-- Economic background before layouts. -/
structure Firm (w:Berth)(M:ℕ)(F C D:ℝ→ℝ)(r:blazeK w.side):Prop extends Chilled w M F C D where
   meet: ∃ J,Flame w.R.K w.p w.H (cipherK w.q) 1 (F w.x) J r

lemma readyFirm {w:Berth}{M:ℕ}{F C D:ℝ→ℝ}(g:w.Chilled M F C D):
 ∃ r,w.Firm M F C D r:=by
 obtain ⟨J,r,v⟩:=g.funds
 exact ⟨r,g,J,v⟩
variable (w:Berth) {M:ℕ} {F C D:ℝ→ℝ} {r:blazeK w.side}
abbrev coincert (e:w.Firm M F C D r): Occlus w.p:=Glacier.oc w.p e.crystal
/-- C,D fees always open the "normal" marked currency by a fresh purchase.
 Occlus uses bandwidth >= positive α, spare in reserve. -/
lemma caratOf (e:w.Firm M F C D r):
 let v:=w.coincert e
 let γ:=TopBill w.P M F D
 v.η=w.snowEta∧v.κ=1∧v.γ=γ w.x∧
   yσE w.p v = Till.markEG γ w.x ∧ yσF w.p v=Till.markFG γ w.x:=by
 refine ⟨rfl,rfl,rfl,?_,?_⟩
 · change Nor.reserveT w.p.power w.p.order w.p.B w.snowEta *
     θG w.p.B w.snowEta (TopBill w.P M F D w.x) = _
   rw [e.rail.H2,e.rail.H6,e.rail.size]

 change Nor.reserveT w.p.power w.p.order w.p.B w.snowEta * (1⁻¹ *
    (TopBill w.P M F D w.x * 200)) = _
 rw [e.rail.H2,e.rail.H6,e.rail.size,inv_one,one_mul]

section corn
variable {I:Type}[LinearOrder I][Fintype I]
abbrev Estate (A:I→Support (More w.side))(v:I→ Sour.Bag w.side)
   (E B: I→Aura w.side→ℝ) (C D:ℝ→ℝ):Prop:=
 Grounds w.p w.q A w.H v E B (rScale w.p) (C w.x) (D w.x*w.Q)

variable {w}{A:I→Support (More w.side)}
 {v:I→ Sour.Bag w.side}{E B:I→Aura w.side→ℝ}

/-- On assignment from Grounds (possibly reassign a birth column witness first).
CONSTANTS INDEPENDENT OF I, BIRTH COUNTS INCLUDING UNSPACED BARRAGE.
-/
lemma farm (e:w.Firm M F C D r)
 (σ:I→Seat w.side)(h:Multiplicity σ M)(p:∀ i,σ i∈ A i)
 (g:w.Estate A v E B C D) :
 OrbitRack (w.coincert e) σ w.q w.R.K w.H (flare g.bill) (riseF E)
                   (riseF B) r (flareM v) :=by
 have hK:lipG w.p w.snowEta + w.snowEta ≤ rScale w.p:=by
    unfold lipG rScale snowEta BScale.runway
    rw [e.rail.coin,e.rail.size]
    apply le_of_eq; unfold weeB; ring
 obtain ⟨z,k⟩:= g.grants hK σ p h e.crystal.pos
 obtain ⟨J,a⟩:=e.meet


 have zz:∀ i,tallB (riseF E) w.p.B (lipG w.p w.snowEta) i ≤ Ufull M C w.x:=by
    intro i
    apply le_trans (z i)
    rw [e.rail.size]
    exact le_rfl
 have kk:∀ i,tallB (riseF B) w.p.B (lipG w.p w.snowEta) i ≤ Ubirth w.P M D w.x:=by
    intro i
    apply le_trans (k i)
    rw [e.rail.size]
    exact le_rfl
 exact Glacier.dressed (P:=w.p) (f:=F w.x) e.crystal a
    (zero_le_one.trans w.P.par.height)
    ((by norm_num:3 ≤ (5:ℕ)).trans e.wide) σ v E B g.bill (g.tie σ p) zz kk

end corn
end Berth
end YM.CF.Bay
#print axioms YM.CF.Bay.Berth.farm
