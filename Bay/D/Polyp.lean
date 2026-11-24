import Bay.D.Sentry
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

variable (P:VΩ)(s:ℕ)
local notation "K"=>P.calibration
local notation "N" i:max=>Papal.count P.run s i
local notation "Ω"=>D.scale P s
local notation "SΩ"=> Band inletO (radiusB Ω)
local notation "τ"=>temp (D.scale P s)


variable (i k:ℕ→ℕ)(A:Armor)
abbrev qSet(P:VΩ)(s:ℕ):= pinpr P.par.R.L (D.scale P s)

abbrev campZ (A:Armor):= Gather inletO (radiusB Ω) τ P.par.d (Ω*A.fee)
abbrev port(P:VΩ)(s:ℕ)(i k:ℕ→ℕ)(j:ℕ):=takeUp P s (i j) (k j) -- change j

abbrev Mission :=(r:ℕ)→Diadem (port P s i k r)

def NamedCrew (t:Mission P s i k):Prop:=∀ᶠ r:ℕ in atTop,Seamew _ A (t r)

/-- any extracted cluster of paid stencils (even tail-aligned) -/
structure Setpiece (P:VΩ)(A:Armor)(s:ℕ)(i k:ℕ→ℕ) where
 t:Mission P s i k
 sold:NamedCrew P s i k A t
 chart:campZ P s A
 settle:∀ᶠ r in atTop, (t r).signal=chart.fleet r ∘ Lifted.onC (Papal.count P.run s (i r))
 finalβ:ℝ
 reachedβ:Tendsto (fun r=> Diadem.bén (port P s i k r)) atTop (𝓝 finalβ)
 helm:ℝ
 priceinc:Tendsto (fun r=> (t r).leading) atTop (𝓝 helm)

abbrev Stretch := matchedX
namespace Setpiece
variable {P s A i k}
variable (u:Setpiece P A s i k)
def test : P.Test:= (u.chart.atK K).allLake
abbrev led:=fun r=>(u.t r).leading
abbrev α:=(r:ℕ)→Pane (N (i r)) →ℂ
abbrev measure (u:Setpiece P A s i k): α (P:=P) (s:=s) (i:=i):= fun r=> (u.t r).signal
lemma burstβ: u.finalβ ∈ Set.Icc (Ω/2) (2*Ω):=
 isClosed_Icc.mem_of_tendsto u.reachedβ (u.sold.mono fun _ t=>Diadem.per_tick _ t)
lemma burstC:u.helm∈Set.Icc (lbott A.δ) (lcap A.fee):=
 isClosed_Icc.mem_of_tendsto u.priceinc (u.sold.mono fun _ t=>Diadem.score_mass _ t)

variable {m d:ℕ}{ε:ℝ}
lemma sealed:∀ᶠ r in atTop, BigBang P s (i r) r (u.chart.atK K) (u.measure r):=
 u.settle.mono fun r p=>u.chart.stamp K _ _ _ _ p

include u in lemma sold_more: 0<Ω∧ 0<τ ∧ 0<qSet P s:=by
 obtain ⟨r,p⟩:=u.sold.exists
 exact ⟨p.cradle.xp,lt_of_lt_of_eq (port P s i k r).p.threshold_pos p.cradle.threshold,p.cradle.qq⟩

/-- signed scaled-back price as c_s -/
def spendL (u:Setpiece P A s i k)(d:ℕ):=floorPrice K d u.finalβ τ (qSet P s)
/-- P_* Z'_s shifted by d -/
def poleX (u:Setpiece P A s i k)(d:ℕ):= splashZ P d (Dollar Ω τ (qSet P s)) u.test
lemma pole_exp (n:ℕ) (p:Seamew _ A (u.t n)):
 (Dollar Ω τ (qSet P s):ℂ) • u.measure n =
    ((port P s i k n).price:ℂ) • (u.t n).get:=by
 have t:=p.cradle.xp
 have d:0<Ω:=t
 change (_:ℂ) • wheel (Real.sqrt Ω) _ = ((qSet P s / τ^2 : ℝ):ℂ) • _
 rw[wheel,Real.sq_sqrt d.le]
 change (↑(qSet P s/(Ω*τ^2)):ℂ) • ((↑Ω:ℂ) • (u.t n).get) = _
 rw[smul_smul,← Complex.ofReal_mul]
 congr 2
 have y:=τ
 field_simp


-- Track real gauge price with estimated complex readings (and actual measured finite prices)
structure Cheered (u:Setpiece P A s i k)(ε:ℝ)(d:ℕ):Prop where
   tune:Clang P s i k u.measure u.test d u.led τ (qSet P s) A.δ ε
   helm_eq(y:Guest P):
     ‖ranked (wholeD K d) (Corsair P s d y u.test)-u.helm‖≤ε
   plane(y:Guest P):0 < floorC A.δ / 2 * spendL u d ∧
    floorC A.δ / 2 * spendL u d ≤ Real.sqrt (fires P s y (u.poleX d))

variable (g:P.Register)(e:Encore P s i k)
  (y:Styx P.calibration (D.scale P s) m d)(v: Hermes P A ε s m)
  (h:ε≤lbott A.δ/2)(hp:0<ε)(t:0<A.δ)

include u g e y v hp h t
lemma fires_up: Cheered u ε d:=by
 have w:Tendsto (fun r=>(N (i r)).val) atTop atTop:= (ageFar P s).comp e.1.growing
 have l:Tendsto (fun r=>(More (N (i r))).val) atTop atTop:=tendsto_atTop_mono (fun r=>by
     change (N (i r)).val≤(N (i r)).val*2; omega) w
 have p:=u.sold_more
 have c:=clangs P s d g e y ε A.δ hp t h p.2.2.le («τ»:=temp Ω)
       u.sealed (z:=u.led)
       ((u.sold.and (u.sealed.and (fencesF l K d m))).mono fun r q=>
           radiant q.1 q.2.1 y q.2.2 v)
 refine ⟨c,?_,?_⟩
 · intro a
   let j:ℂ:= ranked (wholeD K d) (Corsair P s d a u.test)
   exact le_of_tendsto ((tendsto_const_nhds (x:=j)).sub (Complex.continuous_ofReal
       |>.continuousAt |>.tendsto |>.comp u.priceinc) |>.norm)
       (c.near.mono fun r w=>w.1 _)
 intro a
 have r:=u.burstβ.1
 have pv:= (half_pos p.1).trans_le r
 have tu:0<halfSteps K d:=by
    have h':0< rightD K d:=by have:=y.right; unfold Cowl at this; omega
    unfold halfSteps;positivity
 have tk:=floorCp A.δ t
 obtain ⟨ø,te,tr⟩:= p
 refine ⟨?_,le_trans ?_ (c.fire a)⟩
 · unfold spendL floorPrice; positivity
 -- a/2*(b/(j*t))=a*(b/((2*j)*t))
 let a := floorC A.δ
 let b := qSet P s
 let j := u.finalβ
 let t₀ := τ^2*halfSteps K d^4
 have ht:0<t₀:=by unfold t₀;positivity
 have hx:Ω≤2*j := by unfold j; linarith only [r]
 unfold spendL floorPrice
 rw [mul_assoc u.finalβ,mul_assoc Ω]
 change a/2*(b/(j*t₀)) ≤ a*(b/(Ω*t₀))
 rw [show a/2*(b/(j*t₀))=a*(b/((2*j)*t₀)) from by ring_nf; -- via div_mul_eq_mul_div
      ]
 -- avoid gcongr
 exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left tr.le (mul_pos ø ht)
     (mul_le_mul_of_nonneg_right hx ht.le)) tk.le
