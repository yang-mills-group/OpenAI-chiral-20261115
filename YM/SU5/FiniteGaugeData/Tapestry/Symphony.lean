import YM.SU5.FiniteGaugeData.Tapestry.Equivariant
import YM.SU5.FiniteGaugeData.Tapestry.Levels
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra

/-!
# Local gauge invariance on the actual torus steps and the functional
-/
set_option quotPrecheck false
open Haro Tap Cascade Dial Mir Girt Nacre Pastry
open Reed (Fine think)
open Phase RP

section
variable {N P:Side}

/-- Frame covariance on ONE torus. Use relation not twisted arguments (no
choice operators). -/
def Harmony (T:Seat N→ SU.E)(f g: Mark N):Prop:=∀ x:Fields N, f (simultaneous T x)= twist (quantU (tradew N T)) (g x)
lemma ensembleColors {f:Mark N} : covariant f ↔ ∀ T,Harmony T f f:=Iff.rfl
lemma harmonyMeasured (T:Seat N→SU.E) : MeasurePreserving (Girt.gird T) (city _) (city _):= (Wilson.prior_gauge T).prod (threads T)
abbrev harmonyMotion (T:Seat N→ SU.E) : MeasurableEquiv (Orbit N) (Orbit N):=
   ⟨⟨gird T,gird T⁻¹,Pyx.gird_inv T,fun i=>by simpa only [inv_inv] using Pyx.gird_inv T⁻¹ i⟩,(harmonyMeasured T).measurable,(harmonyMeasured T⁻¹).measurable⟩
lemma harmonyDraw {l:Loom N} {k:ℕ}{x y:ℝ}(p:Roof _ x y k l)(T:Seat N→ SU.E)(v) : drawn l (harmonyMotion T v) = simultaneous T (drawn l v):= Prod.ext rfl (p.rev _ _ _)
lemma invariantLetters (T:Seat N→ SU.E)(x:FC (Single N))(z:Phys N): letterRead (twist (quantU (tradew N T)) x) (acts (quantU (tradew N T)).val z)=letterRead x z := by
  let U:=quantU (tradew N T); change inner ℂ (Dial.mateK _) (acts (twist U x) (acts U.val z))=_; rw [←Fock.swivel]; nth_rw 1 [←show acts U.val (Dial.mateK N)=Dial.mateK N from Girt.mastC T]; exact act_unit_inner ..
variable (G:Ratio N P)(A: StepData (More N) (More P))(j:ℕ)(Q:Haro.SpaceM)(M:Male)
  (ho:Odd G.count.val)(q:Chi)(d β:ℝ)(l:Loom N)
local notation "run"=> gathered G j Q.val M ho q d
local notation "push"=> pushMark G A j Q.val M ho q d β l
variable {r:ℕ}(p:LaurentRadius j G.count r) {k:ℕ}{x y:ℝ}(t:Roof _ x y k l)
  (B:A.patch.Branches A.kernel SU.group)(a:0<d)(b:2*d<firstRadius SU.group)
  (c:A.ratio=ratio G)
variable {S:Support (More N)} {b':Bool} {f g:Mark N} (hf:Envelope f)
  (hg:AtSupport b' S g)(W:Seat P→SU.E) (h: Harmony (scaleG G W) f g)
include h hg p ho
local notation "T"=> scaleG G W
local notation "Λ"=> quantU (tradew P W)
lemma gatherCov (x:Fields P)(y:Fields N): run f (simultaneous W x) (simultaneous T y)=twist Λ (run g x y):=by
  have he(x y F): middle G q d F (simultaneous W x) (simultaneous T y)=Peaks.july G W (middle G q d F x y):= Prod.ext (brake_g G q d F ho x.2 y.2 W) rfl
  unfold gathered avgF before; have ht:=h y
  have hz (z:ℝ)(f:FC (Single P)): twist Λ (z • f)=z • twist Λ f :=by rw [← Complex.coe_smul,twist_scalar,Complex.coe_smul]
  rw [hz,map_sum]; apply congrArg; refine sum_congr rfl fun F _ => ?_; rw [ht]; dsimp only; rw [he]; exact subGauge G W j p ho M Q _ (hg.allV y)
include hf a b c t B
lemma pushHarmony : Harmony W (push f) (push g) := by
  let C':FC (Single P)→L[ℝ] FC (Single P):= (LinearMap.toContinuousLinearMap (twist Λ).toAlgEquiv.toLinearEquiv.toLinearMap).restrictScalars ℝ
  intro U; rw [outright G A j Q.val M ho q d β l p t.bill B a b _ hf, outright G A j Q.val M ho q d β l p t.bill B a b _ hg.env]
  let L:= harmonyMotion (scaleG G W)
  let X(v:Orbit N):= A.density β U.1 v.1 • run g U (drawn l v)
  let Y(v:Orbit N):= A.density β (simultaneous W U).1 v.1 • run f (simultaneous W U) (drawn l v)
  change (∫ v,Y v∂city _)= C' (∫ v,X v∂city _); rw [← (show MeasurePreserving L (city N) (city N) from harmonyMeasured _).integral_comp' Y,← C'.integral_comp_comm (pushIntegrable G A j Q.val M ho q d β l _ p t.bill B a b hg.env _ _)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun i=>?_); change Y (harmonyMotion T i)=_
  unfold Y; dsimp only; rw [harmonyDraw t,gatherCov G j Q M ho q d p hg W h,map_smul]
  have H : scaleG G W=W ∘ A.ratio.embed := by rw [c]; rfl
  have ht:A.density (G:=SU.group) β (Lattice.gauge W U.1) (Lattice.gauge (scaleG G W) i.1)= A.density β U.1 i.1:=by rw [H]; exact A.covary B W β ..
  rw [show A.density (G:=SU.group) β (simultaneous W U).1 (harmonyMotion T i).1= _ from ht]; rfl
end

open Py Py.Rate LocalLimit Preparation Journey Vale FullBill
open Py.Period -- for carousel
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l)) (H: Real.exp 1 ≤ Λ.x)
variable (S:Finset Cover)(s i k:ℕ)
local notation "Ω"=> side Y i s
local notation "Ω'"=>side Y i (s+1)
variable (p:Satin.PairIdx Y s i k) {f F: Mark (side Y i s)} {b':Bool} {S':Support (More (side Y i s))} (g: AtSupport b' S' f)
local notation "T"=> Vale.apt (Y.ir i) Λ.block Λ.R.L s
local notation "U"=> (Y.voyage i).CapeT
local notation "A"=> (((Y.voyage i).X (Y.uv k)).gram s)
include p g
lemma ascendHarmony (s':Seat Ω' → SU.E) (pf:Envelope F) (w:Harmony (scaleG T s') F f) : Harmony s' (ascender Y s i k F) (ascender Y s i k f):=by
  let a:= (fullness Y i k p.1).cap_grant
  exact pushHarmony T (patternA Y s i k) Λ.K.j (patternQ Y s i k) _ Λ.R.odd_side Chi.canonical Λ.J.d (patternβ Y s i k) _ (Journey.legal _) ((Y.voyage i).ownership s).paid (a.branch s p.2) (threshold Y).1 (threshold Y).2 (a.aligned s p.2) pf g s' w
lemma ascendGauge (t:covariant f) : covariant (ascender Y s i k f):=fun s=> ascendHarmony Y _ _ _ p g s g.env (t _)
omit g p
local notation "Q"=> Carousel.standard Λ.V 1 2 6 Λ.N0 Λ.J Chi.canonical Λ.h Λ.R0 Λ.δ (Y.visit i k)
-- even without `kick`. Care: the normalized ratio is NOT claimed paid with just this h.
lemma shadeYE (t:s≤ Y.uv k)(u)(g:Seat Ω→ SU.E):
   denZ A Λ.U (U s) (harmonyMotion g u) = acts (quantU (tradew Ω g)).val (denZ A Λ.U (U s) u):=by
  let Q':= Q; have e:= Q'.legal s t -- field order uses grace?
  have h:= (Carousel.credit_rule Λ.V 1 2 6 Λ.N0 Λ.J Chi.canonical Λ.h Λ.R0 Λ.δ Q' s t).leanJ.1
  have k':= (Carousel.loomActs Λ.V 1 2 6 Λ.N0 Λ.J Chi.canonical Λ.h Λ.R0 Λ.δ Q' s)
  have v:1≤ Λ.K.j:=by have h:= Λ.V.L.lobby; have h':= Λ.R.order_cut; omega
  exact Girt.sweep A e h (U s) Λ.J.n k' u g Λ.W.pearl Λ.V.note (Λ.J.gran.trans (Q'.roof s).size) v

lemma trueHarmony (h: Pay Y s i k)(u: Seat (side Y i s)→ SU.E) (v:Harmony u F f): Journey.compass Y i k s F=Journey.compass Y i k s f:=by
  let l:=U s; let z:=denZ A Λ.U l; let t(x:Orbit Ω):=letterRead (F (drawn l x)) (z x)
  have he(x:Orbit Ω): t (harmonyMotion u x)=letterRead (f (drawn l x)) (z x):=by
    have W':=quantU (tradew (side Y i s) u)
    have hs : drawn l (harmonyMotion u x)=simultaneous u (drawn l x):= harmonyDraw ((Y.voyage i).ownership s).paid u x
    unfold t; rw [hs,v _, show z (harmonyMotion u x)=_ from shadeYE Y s i k h.2 x u]
    exact invariantLetters u _ _
  have e:(∫ x,t x∂city Ω)=markedRead f l z:=by
    rw [←(show MeasurePreserving (harmonyMotion u) (city Ω) (city Ω) from harmonyMeasured _).integral_comp' t]
    exact integral_congr_ae (Filter.Eventually.of_forall he)
  exact congrArg (fun (x:ℂ)=> x/partitionZ A Λ.U l) e

lemma prescribed_pivot : (((Y.voyage i).X (Y.uv k)).gram 0).beta=Λ.x:= (Q).color
end YM.CF.Buffered.Afterglow.Tapestry
#print axioms YM.CF.Buffered.Afterglow.Tapestry.trueHarmony
#print axioms YM.CF.Buffered.Afterglow.Tapestry.ascendGauge
