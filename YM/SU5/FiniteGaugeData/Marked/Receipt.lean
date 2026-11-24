import YM.SU5.FiniteGaugeData.Marked.Lantern
import YM.SU5.FiniteGaugeData.SameHistory1102

/-!
# Interface to the other assignments

`Schedule` & (if identifying both collections of parcels level-by-level)
`Both` are IDs/inputs of calibration, NOT assertions that the election or
meter buys a Printed or includes these IDs! This assignment buys convergence
on that same Printed history, for the FiniteGaugeData choice of Loom law. We actually
need of the IDs only the level-0 size, admission of the periods used,
and identity of their sharp densities & Looms, transferring the Nimbus
field and identifying the signed denominator and numerator. Spell a stronger
level-wise version in terms of the input parameters to the densities too.

`Concert.gram` then uses exactly resulting `listener`, no need to assume that
this functional already exists. We do NOT conclude microscopic or continuum
interaction (that bill and especially vacuum selection not tackled here).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py.Rate Py.Rate.LocalLimit Burn
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra

namespace Coupling
open Preparation
variable {K: Calibration} {C:Conveyor K}{J:Tiling K}{V:SpanCal K}(W:Printed K C J V)
local notation "H"=> W.narrative.hist
variable (Λ : Preparation)(l:ℕ)(Y:Course Λ (VolumeCape.Dream.Nimbus l))(u π:ℕ→ℕ)

/- Minimal ID for this level-0 convergence application. Allow supplying
identities of the ket densities themselves rather than the Gram etc.; see
also stronger package below. Each mask equality is on all configurations. -/
structure Schedule (K:Calibration)(C:Conveyor K)(Λ : Preparation){l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(u π:ℕ→ℕ) : Prop where
  per (i): K.takes (Y.ir (u i))
  scale (i): K.c (Y.ir (u i)) = Λ.Ctor (Y.ir (u i)) 0
  mask (i): HEq (C.loom (Y.ir (u i)) 0) ((Y.voyage (u i)).CapeT 0)
  stream (i k)(p:(Y.voyage (u i)).kick ≤ π k)
    (a:K.Allowed (Y.ir (u i)) (Y.uv (π k))):
    HEq (denZ (C.sharp (Y.ir (u i)) (Y.uv (π k)) 0) K.P (C.loom (Y.ir (u i)) 0))
      (denZ (((Y.voyage (u i)).X (Y.uv (π k))).gram 0) Λ.U ((Y.voyage (u i)).CapeT 0))
-- Heat match not needed for the reading equality: heat is used as partner
-- on W only. When electing that SAME collection as required in interface,
-- provide also these IDs for provenance. All are input, including terminal
-- pivot & AP basis/scale ID (same `Mate`, etc result by density/size ID,
-- no extra twists on those operators).
structure Both (K:Calibration)(C:Conveyor K)(Λ : Preparation){l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(u π:ℕ→ℕ):Prop where
  preparationK : K.K=Λ.K
  patch : K.R=Λ.R
  chart : K.L=Λ.L
  grace : HEq K.V Λ.V
  exponent : K.b₀=Λ.b
  e : K.e=Λ.d
  grasp : HEq K.P Λ.U
  givenK : HEq K.W Λ.W
  robes : HEq K.J Λ.J
  pivot : K.x=Λ.x
  meter : HEq K.T Y.meter
  chi : K.η=Push.SectorMeasure.Chi.canonical
  h : K.h=Λ.h
  -- Exact radius of the FiniteGaugeData law. (No claim that every application wants
  -- the rest of these auxiliary calibrations identical between packages.)
  radius : K.w=YM.SU5.FiniteGaugeData.Audit1102.lawRadius (VolumeCape.Dream.plot l).C
  per (i): K.takes (Y.ir (u i))
  warp (i j): HEq (C.loom (Y.ir (u i)) j) ((Y.voyage (u i)).CapeT j)
  oil(i k)(p:(Y.voyage (u i)).kick ≤ π k)(a:K.Allowed (Y.ir (u i)) (Y.uv (π k)))(j)(g:j ≤ Y.uv (π k)):
    HEq (C.sharp (Y.ir (u i)) (Y.uv (π k)) j) (((Y.voyage (u i)).X (Y.uv (π k))).gram j)
  glow(i k)(p:(Y.voyage (u i)).kick ≤ π k)(a:K.Allowed (Y.ir (u i)) (Y.uv (π k)))(j)(g:j ≤ Y.uv (π k)):
    HEq (C.warm (Y.ir (u i)) (Y.uv (π k)) j) (((Y.voyage (u i)).Q (π k) p).gram j)
  -- step data on overlaps, optional stronger than needed at level zero
  wave_ (i k j:ℕ)(p:(Y.voyage (u i)).kick ≤ π k)(a:K.Allowed (Y.ir (u i)) (Y.uv (π k)))(g:j < Y.uv (π k)):
    C.wave (Y.uv (π k)) j=((Y.voyage (u i)).X (Y.uv (π k))).wave j
  hotwave (i k j:ℕ)(p:(Y.voyage (u i)).kick ≤ π k)(a:K.Allowed (Y.ir (u i)) (Y.uv (π k)))(g:j < Y.uv (π k)):
    C.wave' (Y.uv (π k)) j=((Y.voyage (u i)).Q (π k) p).wave j
  fare (i k j:ℕ)(p:(Y.voyage (u i)).kick ≤ π k)(a:K.Allowed (Y.ir (u i)) (Y.uv (π k)))(g:j < Y.uv (π k)):
    C.tilt (Y.uv (π k)) j=((Y.voyage (u i)).X (Y.uv (π k))).fee j
  hotfare (i k j:ℕ)(p:(Y.voyage (u i)).kick ≤ π k)(a:K.Allowed (Y.ir (u i)) (Y.uv (π k)))(g:j < Y.uv (π k)):
    C.tilt' (Y.uv (π k)) j=((Y.voyage (u i)).Q (π k) p).tilt j
  pilot(i k j:ℕ)(p:(Y.voyage (u i)).kick ≤ π k)(a:K.Allowed (Y.ir (u i)) (Y.uv (π k)))(g:j ≤ Y.uv (π k)):
    C.B₀ (Y.uv (π k)) j=((Y.voyage (u i)).X (Y.uv (π k))).pilot j


namespace Both
variable {Λ l Y u π}(p:Both K C Λ Y u π)
include p
omit p in
private lemma denSame {s t n m b a :Side} {j i:ℕ}{e d:ℝ}{h:Odd t.val}{u:Odd s.val}
    {P : Paige.Pricing i t h (Vault.Thread i)} {Q : Paige.Pricing j s u (Vault.Thread j)}
    {X:GramM (mid m a)}{Y:GramM (mid n b)} {A:Paige.Grasp P a d}{B:Paige.Grasp Q b e}
    {W:Loom (mid m a)}{Z:Loom (mid n b)}
    (h1:j=i)(h2:a=b)(h3:m=n)(h4:t=s)(h5:d=e)(hq:HEq P Q)(hx:HEq X Y)(ha:HEq A B)(hw:HEq W Z):HEq (denZ X A W) (denZ Y B Z):=by
  subst_vars; rfl
-- remove include
private lemma purchase : HEq K.V.U Λ.V.U:= by
  suffices he:∀{K K':Pressure.Teller group}{R R':RG.Patch}{L L':Precision.ChartRatio group}{V:Grace K R L}{V':Grace K' R' L'}, K=K'→R=R'→L=L'→HEq V V'→HEq V.U V'.U from
    he p.preparationK p.patch p.chart p.grace
  intro _ _ _ _ _ _ _ _ h v t w; subst_vars; rfl
lemma scaleAll (i j:ℕ):cell (Y.ir (u i)) K.B K.R.L j=Λ.Ctor (Y.ir (u i)) j:= by rw [K.shape,p.patch,p.exponent]
lemma ticket : Schedule K C Λ (l:=l) Y u π:=by
  refine ⟨p.per,fun i=>p.scaleAll i 0,fun i=>p.warp i 0,fun i k h a=>?_⟩
  exact denSame (congrArg Pressure.Teller.j p.preparationK.symm) (K.shape.trans (by rw [p.patch,p.exponent])) (by unfold mesh; simp) (congrArg RG.Patch.L p.patch) p.e p.purchase (p.oil i k h a 0 (by omega)) p.grasp (p.warp i 0)
end Both

namespace Schedule
variable {Λ l u π} {Y:Course Λ (VolumeCape.Dream.Nimbus l)} (p:Schedule K C Λ Y u π) (i k j:ℕ)
include p
lemma law : VolumeCape.Dream.Nimbus l (K.c (Y.ir (u i))) (C.loom (Y.ir (u i)) 0):=by
  suffices he:∀ {n m:Side}{l p:ℕ}{X:Loom n}{A:Loom m}, n=m→l=p→ HEq X A→ VolumeCape.Dream.Nimbus p m A→VolumeCape.Dream.Nimbus l n X from he (p.scale i) rfl (p.mask i) ((Y.voyage (u i)).craft 0)
  intro _ _ _ _ _ _ h v e; subst_vars; tauto

def carried (hi:StrictMono u)(hj:StrictMono π): Circuit K W.narrative.hist l :=⟨Y.ir ∘ u,p.per,Y.ir_grows.comp hi,Y.uv ∘ π,Y.uv_grows.comp hj,p.law⟩

local notation "mY" => Y.ir (u i)
local notation "m₀" => K.c mY
local notation "A₀" => Λ.Ctor mY 0
local notation "nY" => Y.uv (π k)
local notation "IC"=> Y.voyage (u i)

/- Exact comparison of (bra,ket,reconstruction,measure) after identifying
size. Thus the denominator is the same too, phase included. -/
omit p in
lemma cashbook {s t:Side}{R:Loom s}{r:Loom t}{X:Orbit s→Phys s}{Y':Orbit t→Phys t}
    (h:s=t)(w:HEq R r)(e:HEq X Y'):
    (∫ x, beamZ s (X x) ∂city s)=(∫ x,beamZ t (Y' x) ∂city t) ∧
    ∀ f:Buffered.Mark s,let g:Buffered.Mark t:=h ▸ f
                      markedRead f R X=markedRead g r Y' ∧
                      (Integrable (fun z=>letterRead (f (drawn R z)) (X z)) (city s) ↔
                       Integrable (fun z=>letterRead (g (drawn r z)) (Y' z)) (city t)) := by
  subst_vars; exact ⟨rfl,fun _=>⟨rfl,Iff.rfl⟩⟩

lemma fuses (h:(IC).kick ≤ π k) (a:K.Allowed mY nY):
    let D:= (C.sharp mY nY 0); let F:=C.loom mY 0
    let X:= ((IC).X nY).gram 0; let R:=(IC).CapeT 0
    partitionZ D K.P F=partitionZ X Λ.U R ∧ ∀ f:Buffered.Mark m₀,
      let g:Buffered.Mark A₀:= (p.scale i) ▸ f
      markedRead f F (denZ D K.P F) = Py.Rate.LocalLimit.Marks.evaluate (denZ X Λ.U R) (fun x=> g (drawn R x)) ∧
        (Integrable (fun x=>letterRead (f (drawn F x)) (denZ D K.P F x)) (city m₀) ↔ Integrable (fun x=> inner ℂ (Dial.mateK A₀) (acts (g (drawn R x)) (denZ X Λ.U R x))) (city A₀)) := cashbook (p.scale i) (p.mask i) (p.stream i k h a)

/-- One selected participating entry, all supported tests including wide
Borel. Includes integrability on the actual city, identifies
`cap` before any limit; denominator *not* silently replaced by a real partner.
`h`, `v` will both be paid on the cone of the array returned by `marquee`,
hence also eventually in each fixed selected period. -/
theorem mains (h:(IC).kick ≤ π k)(v:Wick H mY nY) :
    let X:= ((IC).X nY).gram 0; let R:=(IC).CapeT 0
    partitionZ (C.sharp mY nY 0) K.P (C.loom mY 0)=partitionZ X Λ.U R ∧ partitionZ X Λ.U R≠0 ∧
    ∀(f:Family K),TestFamily K true f→let g:Buffered.Mark A₀:= (p.scale i) ▸ f mY
       Integrable (fun x=> inner ℂ (Dial.mateK A₀) (acts (g (drawn R x)) (denZ X Λ.U R x))) (city A₀) ∧
       (Histories.cap W.narrative.hist nY (f mY)=
         (∫ x,inner ℂ (Dial.mateK A₀) (acts (g (drawn R x)) (denZ X Λ.U R x)) ∂city A₀)/partitionZ X Λ.U R) := by
  intro X R
  obtain ⟨he,u'⟩:= p.fuses i k h v.allowed
  refine ⟨he,(Y.each_level (u i) (π k) 0 h (by omega)).valid,fun f a=>?_⟩
  obtain ⟨s,a⟩:= a.paid; intro g
  refine ⟨(u' (f mY)).2.mp (mark_integrable v.loom_m (a.support mY).env (v.shot.cap_grant.paid 0 v.step).1),?_⟩
  unfold Histories.cap atZero; change markedRead (f mY) (C.loom mY 0) (denZ (C.sharp mY nY 0) K.P (C.loom mY 0)) / partitionZ (C.sharp mY nY 0) K.P (C.loom mY 0) = _
  rw [he,(u' (f mY)).1]; rfl
end Schedule
end Coupling
end YM.CF.Buffered.Afterglow
