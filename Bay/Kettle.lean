import Bay.Armature
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


open Buffered
variable {N:Side}
lemma Accompanies.waltz {S T:footprint N}{f:Stencil N}{y:phy N}{b:Bool}{c:ℝ}(h:Accompanies S c f y) {Z:Mark N}(z:AtSupport b T Z) (p:Disjoint S T) (K:Scree.Loom N)(x:Orbit N)(v:Phys N):
 letterRead ((toMark f * Z) (Advance.drawn K x)) v = letterRead (Z (Advance.drawn K x)) (acts (y x) v):=by
 let X:=Z (Advance.drawn K x)
 have t:Sector (modesIn N T) b X:=(z.allV _).sector
 have d:Disjoint (modesIn N S) (modesIn N T):=
   disjoint_left.mpr fun _ g v=>disjoint_left.mp p (modes_ch.mp g) (modes_ch.mp v)
 have u: y x*X=X*y x:=by
   rw [Sector.apart (h.lives x) t d];simp [Sector.grainB]
 change inner ℂ (mateK _) (acts (f x.1 * X) v)= inner ℂ (mateK _) (acts X (acts (y x) v))
 rw [act_mul,← act_inner,←h.mate,act_inner,← act_mul,u,act_mul]
namespace Berth
variable (w:Berth)
abbrev supportY (m:ℕ)(o:Site w.side):footprint w.side:=areaY w.p (node o) m
def kick:Prop:=(w.P.run.voyage w.i).kick≤w.k
def sigma : ℝ:=Real.exp (w.P.run.debt w.s * Rate.sites w.side)
abbrev U:=w.P.par.U
abbrev cap:=partitionZ w.R w.U w.K
abbrev sig:=w.P.par.V

abbrev levy:= FullBill.Priced w.sig w.R w.U w.K (w.P.run.charge w.s) (w.P.run.debt w.s)
abbrev volume:=denZ w.R w.U w.K
def sharp (F:Mark w.side):ℂ:=
 markedRead F w.K w.volume / w.cap
abbrev emblem(x:Orbit w.side):= spar w.P.par.K.j w.R.J.M (w.K x)
abbrev pilot (x:Orbit w.side)(t:IsStarProjection (w.emblem x)) :=
 TreasuryFog.pilotH w.U w.R w.K x t

abbrev tickets (x:Orbit w.side):Wave (Dwell w.side):=
 Cadre.poseL _ (fueled w.p w.R.K x)
lemma pilot_value (x:Orbit w.side)(t:IsStarProjection (w.emblem x)):
 w.volume x=w.pilot x t (w.tickets x):=by
 have hr:= TreasuryFog.showUp w.U w.K x t 0 w.R.K
 have hp:exponentL w.p 0 x.1=0:=by simp [exponentL,numbE]
 rw [hp,exp_zero,one_mul,add_zero] at hr
 exact hr

variable {w}{m:ℕ}{S T:footprint w.side}{a c:ℝ}
lemma charges (r:w.Rig a c m)(g:w.kick):w.levy:=
 w.P.run.each_level _ _ _ g r.high.le
lemma emblem_pure (r:w.Rig a c m)(x: Orbit w.side) :
 IsStarProjection (w.emblem x):=
 r.stride.projection _ (r.pulse.roof.paid x)
lemma sharp_sup (r:w.Rig a c m)(g:w.kick)(F:Mark w.side)
 {d:ℝ}(p:∀ t,‖F t‖ ≤ d):‖w.sharp F‖≤d*w.sigma :=
 Marks.upper w.sig w.U w.R w.K (fun x=>F (Advance.drawn w.K x)) (charges r g) (fun _=>p _)

-- denominator integrable. price signs against probes of either grading
abbrev supportProd {N:Side}{b:Bool}{S T:footprint N}{W:Stencil N}{c:ℝ}
 {V:Mark N}(h:Fits S c W)(g:AtSupport b T V): RG.Envelope (Buffered.toMark W * V):=Buffered.env_mult h.basis.env g.env

def yank (w:Berth)(v:Sour.Bag w.side)
 (u:∀ x,IsStarProjection (w.emblem x))(x:Orbit w.side):Phys w.side:=
   (w.pilot x (u x)) (acts (∑ i,v i x) (w.tickets x))

structure Reading (w:Berth) (V:Mark w.side)(Y:Orbit w.side→ℂ)(d:ℝ):Prop where
 cost:w.levy
 priced:‖w.sharp V‖≤d*w.sigma
 isLit (x):letterRead (V (Advance.drawn w.K x)) (w.volume x)=Y x
 int:Integrable Y (city w.side)
 paid:w.sharp V=(∫x,Y x∂city w.side)/w.cap

lemma readBuy
 {b0:ℝ}{o:Seat w.side}{y:phy w.side}{v:Sour.Bag w.side}{C D:ℝ→ℝ}{f:Stencil w.side}{t:Bool}
 (r:w.Rig a c m)(g:w.kick)
 (h:w.charge129 y o v C D)
 (p:Accompanies S b0 f y)
 {V:Mark w.side}(z:AtSupport t T V)
 (q:Disjoint S T)
 (b:ℝ)(gV:∀ t,‖V t‖≤b):
  w.Reading (Buffered.toMark f*V)
    (fun x=>letterRead (V (Advance.drawn w.K x)) (w.yank v (emblem_pure r) x)) (b0*b):=by

 let Z:=Buffered.toMark f *V
 have e (x): letterRead (Z (Advance.drawn w.K x)) (w.volume x)=letterRead (V (Advance.drawn w.K x)) (w.yank v (emblem_pure r) x):=by
    unfold yank
    rw [p.waltz z q, pilot_value w x (emblem_pure r x)]
    exact congrArg _ (h.science x (emblem_pure r x) _).symm
 let u:Fields w.side:=Classical.arbitrary _
 have Q:= charges r g
 refine ⟨Q,sharp_sup r g Z (fun a=>?_), e,?_,?_⟩
 · refine (norm_mul_le ..).trans (mul_le_mul (p.pay.purse a.1) (gV a) (norm_nonneg _) ((norm_nonneg _).trans (p.pay.purse u.1)))
 · rw [←funext e]
   exact mark_integrable r.pulse.roof.bill (supportProd p.pay z) (Marks.can_read w.sig w.U w.R w.K Q)
 rw [←funext e];rfl

variable {o: Site w.side}{d δ W:ℝ}{f:w.First}{v:Sour.Bag w.side}
-- exact comparison of (129)-brand input with true signed certificate.
def SignY (w:Berth) (m:ℕ)(o:Site w.side)(f:w.First)(v:Sour.Bag w.side)(d:ℝ):Prop:=
 ∀ (e:w.kick)(u:∀ x,IsStarProjection (w.emblem x))(b:Bool)(T:footprint w.side)
   (V:Mark w.side)(z:AtSupport b T V)
   (q:Disjoint (w.supportY m o) T)
   (j:ℝ)(g:∀ t,‖V t‖≤j),
     w.Reading (Buffered.toMark (w.marked129 o f m)*V)
       (fun x=>letterRead (V (Advance.drawn w.K x)) (w.yank v u x))
       (w.hue *costY d*j)
lemma wearSign (r:w.Rig a c m)(p:w.WearY m o f a c d v): w.SignY m o f v d:=by
 intro g u b T V z q j h
 have t:= readBuy r g p.stitch p.fit z q j h
 rw [show u=emblem_pure r from rfl]
 exact t
end Berth
end YM.CF.Bay
#print axioms YM.CF.Bay.Berth.wearSign
