import VerifiedSatinWidthAndUVNovember4
import YM.SU5.Six.Polarized
import YM.SU5.Voyager.Canyon
import YM.SU5.Reconstruct.Chiral
set_option autoImplicit false
set_option maxHeartbeats 480000
set_option synthInstance.maxSize 28000
set_option linter.unusedSectionVars false
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
/-!
Six-channel experiment: one character with all purchases, on an actual
Supplied physical Spine. Use the EXISTING Prototype.summit. No hypotheses
from a fixed-stencil alternative election (or a purported rotation guarantee).
The prefix chosen to prove the movement theorem here need not also solve other
tasks, e.g. the Glass co-election or Microcollapse of the source manuscript.
-/
namespace Spine
structure Experiment (P:Spine)(K:P.Register)(c r:ℕ→ℕ)(x:P.Spectrum0 3) (J:P.Ellis 3 x) : Prop where
  launch : Launch P c r
  ready : readyUV P c r x Twah.keyV
  ground : P.party 3 K x
  realPos : P.LowerDeck x K J
  top : Summit x

variable (P:Spine)(K:P.Register)
/-- The same fixed terminal coupling. `Y` the supplier request. -/
lemma terminalBeta {L M:ℝ} {Y:Supplier}(h:uniform P K Y L M)(i k:ℕ) :
    (((P.run.voyage i).X (P.run.uv k)).gram 0).beta = P.par.x :=
  ((h.1.terraces).pivot i k).1

open Dial Reed Pastry
-- normalized finite-volume input and sign check
variable (i k s:ℕ)
local notation "N"=>side P.run i s
local notation "R"=>((P.run.voyage i).X (P.run.uv k)).gram s
local notation "l"=>(P.run.voyage i).CapeT s
lemma input_formula (f:P.Test)(t:(P.run.voyage i).kick≤ k)(v:s≤P.run.uv k) :
    let F:=exhibit P.run P.large s i f.val
    let C:=fun z:Orbit (side P.run i s) => inner ℂ (mateK N) (acts (F (z.1,(l) z)) (denZ R P.par.U (l) z))
    let D:=partitionZ R P.par.U (l)
    Integrable C (city N) ∧ D≠0 ∧ Journey.sharp P.run P.large s i k f.val=(∫ z,C z∂city N)/D:= by
  intro F C D
  obtain ⟨T,h⟩:=findsBay P.calibration f
  obtain ⟨e,g,m⟩:=Tapestry.funds P.run s i k ((exhibited P.run P.large s i T (f:=f.val) (show InTest P.calibration true T false f.val from h)).env) t v
  exact ⟨e,g,(Tapestry.actualRead ..).trans m⟩
lemma input_partition_unit : markedRead (1:Mark N) (l) (denZ R P.par.U (l))=partitionZ R P.par.U (l):=
  markvac (l) _
lemma input_paid : ∀ᶠ n:ℕ in atTop, (P.run.voyage i).kick≤ P.cutoff n ∧ s≤P.run.uv (P.cutoff n):= by
  filter_upwards [P.law.pick.pass _ _ s i] with n t
  exact ⟨t.depth,t.enters⟩
-- Only the unselected readings have these regulator limits.
lemma input_order (f:P.Test) :
    (∀ i:ℕ, Tendsto (fun k=>Journey.sharp P.run P.large s i (P.cutoff k) f.val) atTop
      (𝓝 (P.ultraviolet s f.val i))) ∧
    Tendsto ((P.ultraviolet s f.val) ∘ P.period) atTop (𝓝 (P.E s f.val)) :=
  let T:= P.law.together _ _ f.property
  ⟨T.inner,T.periods⟩

local notation "mₖ"=>P.run.uv k
local notation "N'"=>side P.run i (P.run.uv k)
lemma bare_density (z:Orbit N') :
    let L:=((P.run.voyage i).X (P.run.uv k)).gram mₖ
    denZ L P.par.U ((P.run.voyage i).CapeT mₖ) z=
      Vale.capP (K:=P.par.K) P.par.U L.beta (P.run.meter.a mₖ) z.1:=
  P.run.whole i k z
-- Left-handed in the EXACT FiniteGaugeData chiral source dictionary, not a reconstruction
-- claim. At the top of the same course, on the empty-flags sector: Sea of this
-- antiperiodic Wilson projector for ONE SU.matter with one gauge field, safe,
-- overlap agrees with projection to upper half on its columns. See also
-- Chiral.lean Reconstruct*.action_at for the Grassmann-integral version.
lemma bare_chiral (U:Pane N')(h: flags (P.run.meter.a mₖ).threshold U=∅) :
    let W:=Lat.frame SU.matter (Cube.links U) (anticut N')
    let D:=spar P.par.K.j Vale.babyM U
    Safe W.H ∧ D=portW (Tulip.helix _).symm (projector W.H) ∧
      Sea D (changeM (m:=Vale.mesh (P.run.ir i) P.par.R.L (P.run.uv k)) P.par.U U Vale.babyM) ∧
      portW (Tulip.helix _).symm W.overlap * D=cutM (Tset N') * D ∧
      ∀ (x:Site N') (a:SpinIdx) (g:Fin 3) (t:SU.Ten ⊕ SU.F), (think (Tset N')).term ((x,a),g,t)=
        if a∈plusHalf then Fock.put ((x,a),g,t) else -Fock.takeF ((x,a),g,t) :=
  ⟨Reconstruction.safeCutoff P.run i k U h,(P.run.equity i k U h).1,
    (P.run.equity i k U h).2,Reconstruction.exponent_column P.run i k U h,
    Reconstruction.microscopic_letter P.run i k⟩
lemma six_families (g:SU.E)(j:Fin 3) :
    (SU.matter g).val=(1:Op (Fin 3)) ⊗ₖ Join.both (ExTwo.wedgeOp (SU.fund g)) (cc (SU.fund g)) ∧
    Fintype.card Lead.Clan=6 ∧
    (∀ i:SU.Ten, Window.family (j,Sum.inl i)=(j,true)) ∧
    (∀ i:SU.F, Window.family (j,Sum.inr i)=(j,false)) ∧
    (Window.colors (j,true)).card=10 ∧ (Window.colors (j,false)).card=5:=
  ⟨Reconstruction.microscopic_multiplet g,by decide,fun _=>rfl,fun _=>rfl,
    Window.colors_card _,Window.colors_card _⟩

lemma common_reading (x:P.Spectrum0 3)(f:P.Test)(j:Axis) :
    inner ℂ (P.groundZero 3) (P.compressed 3 s f (P.groundZero 3))=P.E s f.val ∧
    P.chi 3 x (P.reading 3 s f)=P.singleState j s (P.advocate 3 x j) f ∧
    P.singleState 3 s x (P.reflectTest j f)=star (P.singleState 3 s x f) ∧
    P.singleState 3 s x 1=1 := by
  let u:=P.otherSpectrum 3 j x
  refine ⟨P.occupied 3 s f,(P.single_agrees 3 j x s f).symm,?_,?_⟩
  · rw [← P.single_agrees 3 j x s f,← P.single_agrees 3 j x s (P.reflectTest j f),
      P.single_state,P.single_state,← P.reading_star,map_star]
  · rw [P.single_state,P.reading_unit,map_one]

end Spine
open Spine
lemma experiment_exists (L M:ℝ)(p:0<M)(Y:Supplier)(z:ℕ→ℕ) :
    ∃ (P:Spine)(K:P.Register), uniform P K Y L M ∧
      ∃ (c r:ℕ→ℕ)(x:P.Spectrum0 3), z≤r ∧ ∃ J:P.Ellis 3 x, Experiment P K c r x J:= by
  obtain ⟨P,K,h,r,e,c,B,q,y,m',α,t,a,b,g,R,w⟩:= Prototype.summit L M 1 Y p one_pos z
  obtain ⟨n,x,H,U,V,T,G,J,A,E,F⟩ := w.exists
  exact ⟨P,K,h,c,r,x,e,J,B,T,H,A,E⟩

-- First checkpoint: all of l:zoommat including entrywise moving measure estimates
-- and uniform-in-channel spectral projection positivity (all late i),
-- on THIS x and on the supplied course. Give a name collision safe prefix.
namespace Spine.Experiment
variable {P:Spine}{K:P.Register}{c r:ℕ→ℕ}{x:P.Spectrum0 3}{J:P.Ellis 3 x}(B:Experiment P K c r x J)
open scoped BoundedContinuousFunction
local notation "H"=> P.ManyF 3 (P.otherSpectrum 3 3 x)
include B
theorem zoommat :
    (∀ z:SixCoefficients,Tendsto (fun i=>P.zoomMatrix x (c i) (r i) z) atTop (𝓝 (diagonalLimit z))) ∧
    (∀ (Z W:Lead.Clan)(f:ℕ→↥TimeHalf→ᵇ ℂ)(g:↥TimeHalf→ᵇ ℂ)(M:ℝ),
        (∀ i,‖f i‖≤ M) → (∀ T:Set ↥TimeHalf, IsCompact T→TendstoUniformlyOn (fun i=>f i) g atTop T) →
        Tendsto (fun i=>crossTest (P.zoomMatrix x (c i) (r i)) (onHalf (f i)) Z W) atTop
          (𝓝 (if Z=W then ∫ w,onHalf g w ∂(promenade Z:Measure E4) else 0))) ∧
    (∀ V:Set E4, IsOpen V→ (Mink.inside∩V).Nonempty→ ∃ d:ℝ,0<d∧∀ᶠ i in atTop,
      FrameBound.Coercive Lead.Clan H (P.spectralRoster x (c i) (r i) V) d) :=
  let p:=B.ground.2.1.accepted 3
  ⟨fun z=>zoomMatrix_limit z B.launch B.ready Twah.keyV_go p,
    cross_march B.launch B.ready Twah.keyV_go p,zoomMatrix_floor B.launch B.ready Twah.keyV_go p⟩
end Spine.Experiment
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
