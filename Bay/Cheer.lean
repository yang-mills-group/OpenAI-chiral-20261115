import Bay.Bunk
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

open Roots


namespace Berth
variable (w:Berth)
abbrev meterBillU:=serviceCost w.P.run.meter w.s
abbrev cusps := dleaf w.P.par.R.L w.x / 1000
abbrev stepIndex := w.P.run.uv w.k-w.s

structure SlotShot: Prop where
 plan : w.p=w.P.run.meter.a w.s
 path : w.R.path=w.P.par.V.L.path w.stepIndex
 funds : w.R.funds=w.P.par.K.top.clip
 staff : Hom.InterestX w.P.par.W.C _ w.R.J
 core : LotR w.R w.H w.cusps w.cusps
 beta : 0≤ w.R.beta ∧ w.R.beta≤ 2*w.x

lemma slew (h:w.s ≤ w.P.run.uv w.k):w.SlotShot:=by
 let Y:= w.P
 let X:= Y.run
 let A:= (X.voyage w.i).X (X.uv w.k)
 obtain ⟨u,b,p,t,_⟩:= (X.voyage w.i).paths (X.uv w.k)
 have e : w.R= Rate.Branch.gram _ _ b w.s := congrFun t w.s
 have hb:= A.pull.sift w.s h
 have hβ:0 ≤ w.R.beta :=
    le_trans (le_trans (div_nonneg (le_trans (zero_le_one.trans X.oneP) (Vale.crown ..)) (by norm_num)) hb.1) le_rfl
 have g:=u.charged w.P.par.H p.toRealQ w.s h
 refine ⟨?_,?_,?_,?_,?_,hβ,hb.2⟩
 · unfold Berth.p; rw [e]
 · rw [e]
 · rw [e]
 · rw [e]; exact (w.P.par.W.arm ..).sound w.s
 rw [e]
 exact g.toCost.lot _ _

abbrev craved :=
  Real.exp (w.meterBillU*Rate.sites w.side)
abbrev renormal (Q:ℝ):=
  w.sigma * Real.exp ((3*Q)*Rate.sites w.side)

variable {w}{m:ℕ}{t c Q:ℝ}
-- exponential volume stipend
lemma noticeable (h:w.Rig t c m)
 {A: RegBudget w.side}{B: ForceBudget w.side}
 (a:IncX primeU A w.p w.H Q)(d:Dark primeU B w.p w.H Q):
 Envelope (w.swipe A B) ∧ ∀ x, ‖Complex.exp (-w.R.v) • w.swipe A B x‖ ≤
  Real.exp ((w.meterBillU + (3*Q))*Rate.sites w.side):= by
 have s:=slew w h.high.le
 let G:=construct w.p (w.P.par.V.L.path w.stepIndex) w.P.par.K.top.clip w.R.J w.R.beta
   (w.R.F+A,w.R.K+B) w.R.v
 have kg: w.offsetR A B=G:=by dsimp only [offsetR,G]; rw [←s.path,←s.funds,h.slip]
 have v: w.swipe A B = denZ G w.U w.K:= by rw [swipe,kg]
 have hp: LotR G w.H (w.cusps+Q) (w.cusps+Q) :=
   ⟨ Larch.add_v w.p _ _ s.core.val a, rfl,Fixed.Voltage.cloudy w.p primeU s.core.wear d⟩
 rw [v]
 refine ⟨Rate.denInt w.P.par.W h.pulse.roof w.stepIndex h.deep _ _ hp,fun x=>?_⟩

 have prices:
   w.meterBillU+3*Q=
     Rate.earnings w.P.par.W w.p (2*w.x) (w.cusps+Q):=by
      unfold meterBillU cusps Berth.x serviceCost Rate.earnings xTop
      rw[s.plan];ring
 rw [prices]
 exact Rate.extensive w.P.par.W s.staff h.pulse.roof w.stepIndex h.deep w.P.par.height
    w.R.beta w.R.v hp s.beta.1 s.beta.2 x

lemma netGain {A: RegBudget w.side}{B: ForceBudget w.side}
 (l:w.levy)
 {x:Orbit w.side}
 (v:‖Complex.exp (-w.R.v) • w.swipe A B x‖ ≤
  Real.exp ((w.meterBillU+3*Q)*Rate.sites w.side)):
 ‖w.swipe A B x‖ ≤ ‖w.cap‖ * w.renormal Q:=by
 let Z:=‖Complex.exp (-w.R.v)‖
 have hz: 0 < Z:=norm_pos_iff.mpr (Complex.exp_ne_zero _)
 let N:=Rate.sites w.side
 have hN:0≤N:=zero_le_one.trans (sites_pos _)
 apply le_of_mul_le_mul_left _ hz
 rw [norm_smul] at v
 refine le_trans v ?_
 let a:= w.P.run.charge w.s
 have hz' : Real.exp (-a*N) ≤ Z * ‖w.cap‖:=by have h:=l.lower; rw[compensated,norm_mul] at h; exact h
 rw[mul_comm ‖w.cap‖, mul_left_comm]
 refine le_trans ?_ (mul_le_mul_of_nonneg_left hz' (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le))
 unfold renormal sigma Course.debt
 rw [←Real.exp_add, ←Real.exp_add]
 apply Real.exp_le_exp.mpr
 change (w.meterBillU+3*Q)*N ≤ ((a+|w.meterBillU|)*N +3*Q*N) + -a*N
 linarith only [mul_le_mul_of_nonneg_right (le_abs_self w.meterBillU) hN]
end Berth

namespace Berth
open Buffered
variable {w:Berth} {I:Type}[LinearOrder I][Fintype I]
lemma emptyLaw {E:Type}[NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E]
 {f:Mew.Key I→ E}(σ:I→Seat w.side)
 (q:Differentiable ℂ f):Law_C σ 0 [] f f:=by
 have h:River f:=⟨q.continuous.continuousOn,fun z _ i x _=> (q _).comp _ ?_⟩
 refine ⟨h,h,fun c w=>?_⟩
 rw[List.sublist_nil.mp w, fuelΦ,Roots.snow]
 rw [differentiableAt_pi]
 intro j;by_cases h:i=j
 · subst i; simpa using (differentiableAt_id (𝕜:=ℂ) (x:=x))
 simp [Ne.symm h]


-- River.
variable {T σ:I→Seat w.side}
 {V:Mew.Key I→ RegBudget w.side} {W:Mew.Key I→ ForceBudget w.side}

abbrev carrier (w:Berth)
 (U:Mew.Key I→ RegBudget w.side)(V:Mew.Key I→ ForceBudget w.side)
 (z:Mew.Key I):Orbit w.side→Phys w.side:=w.swipe (U z) (V z)

lemma ventilated (g:BillRoll σ V W)
 (u:Orbit w.side): River (fun z=>w.carrier V W z u):=by
 let X(z:Mew.Key I):=w.R.F+V z
 let Y(z:Mew.Key I):=w.R.K+W z
 exact (pulse_H (N:=Vale.mesh (w.P.run.ir w.i) w.P.par.R.L w.s)
    w.P.par.V (U:=w.U) σ 0 [] (by simp[ψS]) w.R w.K
    X X (fun _=>w.R.slip) (fun _=>w.R.slip) Y Y
    (fun _=>w.R.v) (fun _=>w.R.v) u

    (fun i x=> emptyLaw σ (differentiable_const _ |>.add (g.varE i x)))
    (fun i x=> emptyLaw σ (differentiable_const _))
    (fun i x=> emptyLaw σ (differentiable_const _ |>.add (g.varF i x)))
    (emptyLaw σ (differentiable_const _))).1

variable (w:Berth)
structure Shrewd (V:Mew.Key I→ RegBudget w.side)(W:Mew.Key I→ ForceBudget w.side)
 (C:ℝ):Prop where
   charged:w.levy
   river(u:Orbit w.side):River (fun z=>w.carrier V W z u)
   stroke (z:Mew.Key I) (p:z∈hill I):
     RG.Envelope (w.carrier V W z) ∧
     ∀u, ‖w.carrier V W z u‖ ≤ ‖w.cap‖ * w.renormal C

variable {w} {c t C:ℝ} {L m:ℕ} {σ:I→Seat w.side}
 {V:Mew.Key I→ RegBudget w.side} {W:Mew.Key I→ ForceBudget w.side}
lemma shrewd (h:w.Rig t c m)(k:w.kick)
  (u:Receives w.p L σ V W w.H C): w.Shrewd V W C:=by
 obtain ⟨_,_,g,_,d⟩:=u
 have l:=charges h k
 refine ⟨l, ventilated g,fun z y=>?_⟩
 have h0 (i:I):‖z i‖ ≤ 2:=(norm_le_pi_norm z i).trans ((mem_closedBall_zero_iff.mp y).trans (by norm_num))
 obtain ⟨p,q⟩:=d z h0
 obtain ⟨a,b⟩:=noticeable h p q
 exact ⟨a,fun x=>netGain l (b x)⟩

end Berth
