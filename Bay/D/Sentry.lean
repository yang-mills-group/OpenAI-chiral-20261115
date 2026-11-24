import Bay.D.Pith
import Bay.D.Regatta
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

namespace D
open Exterior Precision Nacre
open scoped ContDiff
open Regis Regis.Head Etch Gleam Next.SectorChange Next.SectorChange.Gaussian
open Pressure Work.F03 ProbabilityTheory
local notation "T4"=>SU.group
open Buffered Lamour.Bridge.Celeste.Clock Fabric
open Py Py.Rate LocalLimit Preparation Buffered.Afterglow Papal
open Vale clocks
open YM.CF.Pannier.Chancel Journey Tower Tower.SlabMark VacuumSelection Tapestry
open scoped ComplexOrder NNReal ENNReal
local notation "VΩ"=>VacuumSelection.Spine


open BPress (NPL)
-- common terms for Y & Z payments
structure Armor where
  a:ℝ
  c:ℝ
  b:ℝ
  W:ℝ
  η:ℝ
  F:ℝ→ℝ
  r:ℝ
  fee:ℝ
  δ:ℝ
structure Diadem (w:Berth) where
  f:w.First
  jade:Icey (Cella (More w.side))
instance (w:Berth):Inhabited (Diadem w):= ⟨⟨⟨fun _=>0,fun _=>0,0,0⟩,0⟩⟩
open Zephyr.Chern

abbrev centerC(w:Berth):Site w.side:= w.home corner
local notation "m₀" w:max=>tabW (Berth.P w)
structure Seamew (w:Berth)(A:Armor)(x:Diadem w):Prop where
  cradle:w.Rig A.a A.c (tabW w.P)
  swell: w.Before A.a A.b (tabW w.P) (centerC w) x.f ∧
      Beau (w.smallFlow (centerC w) x.f) (w.fluxBare (centerC w) (tabW w.P))
         A.η (A.W*w.wid A.a A.b) ∧
      gem (w.priceFlow (centerC w) x.f) (w.price*A.η) ∧
      ∃ V,w.WearY (tabW w.P) (centerC w) x.f A.a A.c A.b V ∧
           w.SignY (tabW w.P) (centerC w) x.f V A.b
  monte : Phoenix w (centerC w) x.f x.jade A.r A.fee A.δ

namespace Armor
variable (A:Armor)
abbrev cape(A:Armor)(w:Berth):Prop:=w.Rig A.a A.c (tabW w.P)→∀f,
  w.Before A.a A.b (tabW w.P) (centerC w) f → ∃X, Phoenix w (centerC w) f X A.r A.fee A.δ
abbrev doses(A:Armor)(w:Berth)(M L:ℕ):=
 Sediment w A.a A.c A.b A.W A.η (tabW w.P) M L A.F
def Strong (P:VΩ) (A:Armor):Prop:=
 let m:=tabW P
 0<A.a ∧ 0<A.c ∧ 0<A.b ∧ 0<A.W ∧ 0<A.η ∧ Ice P A.F ∧
 NPL (till129 P A.a A.c A.b m) ∧ NPL (reserve129 P A.a A.c A.b m)∧
 0<A.r ∧ 0≤A.fee ∧ 0<A.δ ∧
 ∀ M L:ℕ,PinNPL P (Berth.ceremony P M L A.F A.a A.c A.b m) ∧
   Dry P (fun w=> A.doses w M L ∧ A.cape w)
lemma punct {P:VΩ}(B:OfBay2 P):∃A,Strong P A:=by
 obtain ⟨a,c,b,W,e,F,t,h,u,v,d,I,J,K,S⟩:=B
 have tuP:0<tabW P:=tabW0 P
 obtain ⟨r,L,δ,l,q,y,p⟩:= regatta (P:=P) a c b _ corner tuP t u.le
 exact ⟨⟨a,c,b,W,e,F,r,L,δ⟩,t,h,u,v,d,I,J,K,l,q,y,fun M m=> ⟨(S M m).1,Filter.Eventually.mono (Filter.Eventually.and (S M m).2 p) (fun i y=>(y.1.and y.2).mono fun v g t h=>⟨g.1 _ h,g.2 _ h⟩)⟩⟩

lemma mews{A:Armor}{w:Berth}{M L:ℕ}(p:A.doses w M L)(q:A.cape w): ∃x, Seamew w A x:=by
 have r:=p.old.cradle.1
 obtain ⟨f,V,s,t,g,k,h⟩:=p.old.swell
 obtain ⟨X,u⟩:=q r f s
 exact ⟨⟨f,X⟩,r,⟨s,t,g,V,k,h⟩,u⟩
end Armor
lemma centerL(w:Berth):node (centerC w) = startL w.side:=by
 rw[centerC,Berth.home,node_wrap,←Buffered.Region.wrap_one,← map_add]
 change wrap _ ((2:ℕ) • corner+1) = wrap _ inletO 
 congr 1

namespace Diadem
variable {w:Berth}(x:Diadem w)
abbrev bén (w:Berth) :=(gram w.P.run w.s w.i w.k).beta
-- gauge scaled measurement c_t at origin
abbrev get (x:Diadem w) := tuneZ w (centerC w) x.f
abbrev signal (x:Diadem w) := wheel (Real.sqrt w.x) x.get
abbrev leading(x:Diadem w):= lscore (Real.sqrt w.x * coupling (bén w)) x.jade
variable {A:Armor}

lemma per_tick(g:Seamew w A x):matchedX w.x (bén w):=
 (prices_plot w.P.run w.s w.i w.k g.cradle.high.le).2.2.2.1
lemma score_mass(g:Seamew w A x):x.leading∈Set.Icc (lbott A.δ) (lcap A.fee):=
  lcosts g.monte.phoenix.skin.rake g.monte.sweat
     (railB (x.per_tick g).1 (x.per_tick g).2 g.cradle.xp)
lemma spruces(g:Seamew w A x):Sprucy inletO (radiusB w.x) w.th w.d (w.x*A.fee) x.signal:=by
 have u:=(g.monte.phoenix.vinyl.scale (w.x:ℂ))
 rw[centerL,Complex.norm_real, Real.norm_eq_abs,abs_of_pos g.cradle.xp] at u
 refine ⟨w.p,g.cradle.sizeB,g.cradle.threshold,?_⟩
 rw[signal, wheel,Real.sq_sqrt g.cradle.xp.le]
 rw [g.cradle.sizeB] at u
 simpa using u


end Diadem
variable {P:VΩ}{s i k:ℕ}{A:Armor}
local notation "Y"=>P.run
local notation "K"=>P.calibration
local notation "Ω"=>D.scale P s
local notation "N" i:max=>Papal.count P.run s i

abbrev Hermes(P:VΩ)(A:Armor)(ε:ℝ)(s m:ℕ):=
   Mist P.par.K.top.clip P.par.V.W.parcel P.par.K.η P.par.K.C A.r A.fee ε (D.scale P s) m

variable {m d r:ℕ}{ε:ℝ}
local notation "SΩ"=> Band inletO (radiusB Ω)
-- general witness predicate
lemma radiant {T:Lake K SΩ}
  {x:Diadem (takeUp P s i k)}
  (v:Seamew _ A x)
  (y:BigBang P s i r T x.signal)
  (sd:Styx K Ω m d)
  (q:VeryFine (N i) K m d)
  (z:Hermes P A ε s m) :
 ∃W:Group3,lbott A.δ≤x.leading∧ CrownRank Ω (wholeD K d :ℝ) ε x.leading W ∧
    Light P s i k r T d W:=by
 let n:=P.run.uv k-s
 have h:=v.cradle
 have hz:=x.per_tick v
 have hx:=v.monte.phoenix
 rw [centerL] at hx
 have ho: Bore (More (N i)) m ((takeUp P s i k).p.B/10) (wholeD K d) (startL (N i)) (prepL K _ d) (tailL K _ d):=by rw [h.sizeB]; exact lineBore sd.high q
 let H:=P.par.V.L
 have hp:=z.2 (H.mood n) (H.tied n) (H.roof n).1 ((H.roof n).2.1 _)
      h.sizeB h.threshold hz.1 hz.2 hx ho sd.in_
 exact ⟨_,(x.score_mass v).1,hp.2,⟨_,_,y,placed.1,placed.2,hp.1⟩⟩
end YM.CF.Bay.D
