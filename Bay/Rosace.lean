import Bay.Alcove
import Bay.Slip
import YM.SU5.Exchange.Pace.Cult
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


/-- Half-block, in matter units. Gauge displacement 2m between Y position and a current. -/
def tabW (P:VΩ):ℕ:=8 *P.par.block.val
abbrev xTop (P:VΩ)(s:ℕ):ℝ:=Vale.hat P.par.R.L P.par.x s
abbrev pStart (P:VΩ):= P.run.meter.a 0

/-- Datum index, within ONE V/V. Height, period and cutoff *indices*;
    usually bought with w.s < w.P.run.uv w.k, not endpoint. -/
structure Berth where
 P:VΩ
 s:ℕ
 i:ℕ
 k:ℕ
namespace Berth
variable (w:Berth)
abbrev side:=age w.P.run w.i w.s
abbrev K:Scree.Loom w.side:=(w.P.run.voyage w.i).CapeT w.s
abbrev R:=RootBook w.P.run w.i w.k w.s
abbrev p:= w.R.p
abbrev L:=w.P.par.R.L
abbrev x:=xTop w.P w.s
abbrev Q:=pinpr w.L w.x
abbrev th:=Pressure.temp w.x
abbrev price:ℝ:=w.Q/w.th^2
abbrev boost:=stemS w.x
abbrev hue:=hueW w.L w.x
abbrev wid (a b:ℝ):=Real.exp (-a*(↑(w.p.B/10:ℕ):ℝ))*b
abbrev d:=w.P.par.d
abbrev M:SOp w.side:=funde w.P.par.K.j w.R.J.M w.side
abbrev T:SOp w.side:=Moire.bloom w.R.J.P
abbrev q:=w.P.par.J.n
abbrev H:=w.P.par.h

structure Rig (w:Berth)(a c:ℝ)(m:ℕ): Prop where
  high:w.s < w.P.run.uv w.k
  full: Tulip.Solo a c w.M w.d
  tonic:Tulip.Solo a c w.T w.d
  pulse: DockPulse w.p w.K w.P.par.J.k w.d a w.H 32 24 w.q
  stride:Staffer w.M w.T w.d
  deep:w.P.par.U.roundZ≤ w.side.val
  slip:w.R.slip=0
  shift:w.p.B+2*m≤ 24*w.p.B
  sizes:24*m≤ w.p.B ∧ w.q+(w.p.B/10)≤w.p.B
  sizeB:w.p.B=Pressure.radiusB w.x
  order:w.p.order=6
  power:w.p.power=2
  threshold:w.p.threshold=w.th
  feeS:w.p.supportExponent=1
  xp: 0<w.x
  charge:Sectoral w.p w.q (scald w.p (Ione.head_L w.R.F)) w.H (rScale w.p+(w.p.B:ℝ)⁻¹) (RΓK w.p w.L w.x)
  qq: 0<w.Q

/-- Split of stencil specification, BEFORE mask; expose tail for derivatives on chord-germ
 etc., no dependence on ambient field. -/
structure First (w:Berth) where
  J:Axis→SOp w.side
  outside:Axis→ SOp w.side
  X:SOp w.side
  endX:SOp w.side

abbrev tracePay (a b:ℝ)(o:Site w.side)(v:SOp w.side):Prop:= Trunk (node o) v (w.p.B/10) a b w.d
abbrev tail (a b:ℝ)(o:Site w.side)(v:SOp w.side):Prop:= Soak (node o) v a (w.wid a b) w.d

structure Before (w:Berth)(a b:ℝ)(m:ℕ)(o:Site w.side)(f:w.First):Prop where
  arm: ∀ i, w.tracePay a b o (f.J i)
  endArm: ∀ i,w.tail a b o (f.outside i)
  stone: w.tracePay a b o f.X
  endStone: w.tail a b o f.endX
  line: ∀ i z, spur (millIntro w.M w.T) o i m (z:Openc (More w.side) w.d).val=f.J i z.val+f.outside i z.val
  lump: ∀ z, (w.M (z:Openc (More w.side) w.d).val - tickA w.side)*windmill o m=f.X z.val+f.endX z.val

-- pin openings
abbrev charge129 (X:phy w.side)(o:Seat w.side)(G: Sour.Bag w.side)(C D:ℝ→ℝ):Prop:= Nest w.P.par.U w.R w.K w.q 24 o w.H (rScale w.p) X G (C w.x) (D w.x*w.Q)
variable {w}{a b c δ t:ℝ}{m:ℕ}
lemma clearance (r:w.Rig a c m):Clearance w.p w.K (w.p.B/10) w.d:=
 ⟨r.pulse.pos,w.q,w.P.par.J.k,w.d,r.pulse.roof,r.pulse.reach,le_refl _,r.sizes.2⟩
lemma boostPos (w:Berth):0<w.boost:=Real.rpow_pos_of_pos (BPress.drift_pos _) _
lemma huePos (r:w.Rig a c m):0<w.price ∧ 0<w.hue:=by
 have ht:0<w.th:=r.threshold ▸ w.p.threshold_pos
 have h:=div_pos r.qq (pow_pos ht 2)
 exact ⟨h,mul_pos h w.boostPos⟩

variable {o:Seat w.side}
-- Elevate a fence along Fee delta.
lemma buyRig (r:w.Rig a c m) {Y:phy w.side}{e t:ℝ}
 (g:Fence w.M w.T w.K w.p w.q 24 o w.H 32 Y e t) :
 ∃ G, Nest w.P.par.U w.R w.K w.q 24 o w.H (rScale w.p)
   Y G (e+τΓK w.p w.L w.x e) (t+τΓK w.p w.L w.x e):=by
 let B:ℝ:=w.p.B
 have hb:0<B:=Nat.cast_pos.mpr w.p.B_pos
 have h:= downFence (m:=0) g (rateEx w.p)
 have z:= knock w.P.par.U w.R w.K r.pulse.roof r.deep r.slip 
     (show 0≤rScale w.p from by unfold rScale;positivity) (inv_pos.mpr hb) h r.charge
 dsimp only at z
 simpa only [B,inv_inv] using z

end Berth

abbrev till129 (P:VΩ)(a c b:ℝ)(m:ℕ):ℝ→ℝ:=
 coatFull P.par.R.L (pStart P) m P.par.h a c b
abbrev reserve129 (P:VΩ)(a c b:ℝ)(m:ℕ):ℝ→ℝ:=
 coatVoid P.par.R.L (pStart P) m P.par.h a c b

namespace Berth
variable {w:Berth}{a c b b₁:ℝ}{m:ℕ}{o:Seat w.side}

lemma buyCore (r:w.Rig a c m)
  {Y:phy w.side} {e t C D:ℝ→ℝ}
  (h:Fence w.M w.T w.K w.p w.q 24 o w.H 32 Y (e w.x) (t w.x))
  (gC:w.hue*(e w.x+ZxT w.L (pStart w.P) w.x (e w.x)) ≤ C w.x)
  (gD:w.hue*(t w.x+ZxT w.L (pStart w.P) w.x (e w.x)) / w.Q ≤ D w.x) :
  ∃ G,w.charge129 ((w.hue:ℂ) • Y) o G C D :=by
 obtain ⟨G,b⟩:= buyRig r h
 have hp:w.p.order = (pStart w.P).order := r.order.trans (w.P.run.meter.boot 0).2.2.2.2.symm
 have eqL:= (lifeS w.L w.H a c m w.p (pStart w.P) hp w.x r.sizeB (e w.x) c).1
 refine ⟨_,nestUp w.P.par.U w.R w.K ?_ ?_ (nestScale w.P.par.U w.R w.K _ b)⟩ <;>
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (huePos r).2,eqL]
 · exact gC
 exact (div_le_iff₀ r.qq).mp gD

variable {x:Site w.side}{f:w.First}
abbrev bareOpen (w:Berth)(x:Site w.side)(f:w.First)(m:ℕ): phy w.side:=puffLine w.K w.p x f.J f.X m
abbrev cloth (w:Berth)(x:Site w.side)(f:w.First)(m:ℕ):phy w.side:=
 (w.hue:ℂ) • w.bareOpen x f m

lemma sews (r:w.Rig a c m)(h:w.Before a b m x f):
  ∃ G,w.charge129 (w.cloth x f m) (node x) G (till129 w.P a c b m)
     (reserve129 w.P a c b m):=by
 let u:=pStart w.P
 let V:=coverT0 u m w.H a c b w.x
 let W:=coverT1 u m w.H a c b w.x
 have hp:w.p.order = u.order := r.order.trans (w.P.run.meter.boot 0).2.2.2.2.symm
 obtain ⟨_,g,z⟩:=lifeS w.L w.H a c m w.p u hp w.x r.sizeB c b
 have k: V= tailPay 24 w.p 32 w.H a c (w.wid a b) m:=by
   unfold V; rw [g]; unfold wid;rw [tail_linear]; simp only [coverT0,exponentialR,r.sizeB]
 have q:= taught r.pulse r.stride h.arm h.endArm h.stone h.endStone h.line h.lump r.full r.tonic r.shift
 dsimp only at q
 have c0:W = κfront 24 w.p 32 w.H a c m+ V + primT w.H w.p m a c b w.x:= by
    unfold W V; rw [z,g]
 refine buyCore (e:=coverT1 u m w.H a c b) (t:=coverT0 u m w.H a c b) r ?_ le_rfl le_rfl
 rw [show coverT1 u m w.H a c b w.x=_ from c0,show coverT0 u m w.H a c b w.x=_ from k,k]
 exact q

abbrev Y128 (w:Berth)(x:Site w.side)(f:w.First)(m:ℕ):Stencil w.side:=
  (w.price:ℂ) • pressY w.K w.p x f.J f.X m
abbrev Z130 (w:Berth)(x:Site w.side)(f:w.First):Stencil w.side:=
  (w.price:ℂ) • blankS w.K w.p x f.X
abbrev Jpose (w:Berth)(x:Site w.side)(f:w.First)(a:Axis)(z:Site w.side) :Stencil w.side:=
  (w.Q:ℂ) • tooth w.K w.p x z (f.J a)
/-- Native current, J^s. Bond anchored between, or simply at x in the pricing rule. -/
abbrev J130 (w:Berth)(x:Site w.side)(f:w.First)(a:Axis) :Stencil w.side:=
  (w.Q:ℂ) • toothAt w.K w.p x (f.J a)

/-- Stencil equation with native Y versus native divergence (physical and scaled). -/
lemma splitsY (w:Berth)(x:Site w.side)(m:ℕ)(f:w.First):
  w.Y128 x f m = w.Z130 x f +
    (((w.th^2)⁻¹:ℝ):ℂ) • (∑ a:Axis,
    (w.Jpose x f a (x+gapPlus a m)-w.Jpose x f a (x-gapPlus a m))) :=by
 simp_rw [Y128,Z130,Jpose,pressY,toothSum,price,smul_add,←smul_sub,←smul_sum, smul_smul,←Complex.ofReal_mul, div_eq_inv_mul]

lemma JposeTip (r:w.Rig a c m)(h:w.Before a b m x f)
    (i:Axis)(y:Site w.side)(V:Pane w.side):
    let s:=taxiPlus (y-x)
    twist (quantU (γS s)) (w.Jpose x f i y V)=w.J130 x f i (flashA s V) :=by
 intro s
 rw [Jpose, J130,Pi.smul_apply,Pi.smul_apply,twist_scalar]
 exact congrArg _ (toothMoves x y (clearance r) (boxSeal (h.arm i) r.pulse.hint.le) V)

abbrev marked129 (w:Berth)(x:Site w.side)(f:w.First)(m:ℕ):Stencil w.side:=
 (w.boost:ℂ) • w.Y128 x f m
lemma markedFits (r:w.Rig a c m)(h:w.Before a b m x f): 
 Accompanies (areaY w.p (node x) m) (w.hue * costY b)
   (w.marked129 x f m) (w.cloth x f m):=by
 have g:= (baked (clearance r) h.arm h.stone r.sizes.1 r.pulse.hint.le).scalar (w.hue:ℂ)
 rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (huePos r).2] at g
 rw [marked129, Y128, smul_smul, ←Complex.ofReal_mul, show w.boost * w.price = w.hue from mul_comm ..]
 exact g

-- (128) plus priced.

abbrev pearlZ (w:Berth)(x:Site w.side)(f:w.First)(V:Pane w.side):ℂ:=
 (w.price:ℂ)*pearl w.K w.p (node x) f.X V
lemma zPearl (w:Berth)(x:Site w.side)(f:w.First)(V:Pane w.side):
 w.Z130 x f V = w.pearlZ x f V • 1:=by
 rw [Z130,blankS,Pi.smul_apply,glint,smul_smul]

abbrev priceFlow (w:Berth)(x:Site w.side)(f:w.First):ℝ→ℂ:=
 fun r=>w.pearlZ x f (Zephyr.Chern.petals (fluxV _) r)
abbrev fluxBare (w:Berth)(x:Site w.side)(m:ℕ):ℝ→ℂ:=
 spout (fun y=>(w.M y-tickA w.side)* windmill x m) (fluxV _)
abbrev smallFlow (w:Berth)(x:Site w.side)(f:w.First):ℝ→ℂ:=
 dach w.K w.p (node x) f.X (fluxV _)

lemma flowRate (r:w.Rig a c m){δ v:ℝ}(t: Beau (w.smallFlow x f) (w.fluxBare x m) δ v):
 gem (w.priceFlow x f) (w.price*δ):=by
 have u:=t.pays.1.bloom.scale (w.price:ℂ)
 refine ⟨u.1,?_⟩
 change w.price * δ < (bud (fun r=>(w.price:ℂ)*w.smallFlow x f r) _).re
 rw [u.bud_eq,Pi.smul_apply,smul_eq_mul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
 exact mul_lt_mul_of_pos_left t.pays.2 (huePos r).1

-- For the so-obtained economic layer, no uniformity lost when inspecting
-- failing masks or choosing tails on the same Rig.
structure WearY (w:Berth)(m:ℕ)(o:Site w.side)(f:w.First)(a c b:ℝ)
   (V:Sour.Bag w.side) : Prop where
  fit: Accompanies (areaY w.p (node o) m) (w.hue * costY b)
       (w.marked129 o f m) (w.cloth o f m)
  stitch: w.charge129 (w.cloth o f m) (node o) V (till129 w.P a c b m) (reserve129 w.P a c b m)

lemma weft (r:w.Rig a c m)(h:w.Before a b m x f):
 ∃ V,w.WearY m x f a c b V:=by
 obtain ⟨V,p⟩:=sews r h
 exact ⟨V, markedFits r h, p⟩
end Berth
end YM.CF.Bay
#print axioms YM.CF.Bay.Berth.weft
#print axioms YM.CF.Bay.Berth.splitsY
#print axioms YM.CF.Bay.Berth.flowRate
