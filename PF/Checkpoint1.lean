import PF.Sensor
set_option autoImplicit false
set_option maxHeartbeats 380000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set

-- Physical gating on a single LP satellite
namespace PureForce
open Lattice
namespace Native
/-!
CP one of the PureForce undertaking; open proof manuscript pressure/rank/
interaction goals, see the pairing estimates. Here at all charged physical Seals BEFORE
LK clock/thermal refinement or IC final s election:

* one new-source allocation furnishing the nLeaf clover & stamped rates &
  L.2 wall, as well as P,Register and conull-selected x licences, etc.
* actual charged singular checker Ward prices on that very enrollment. Time
  placements P.shifts at zero s-footprint step, include real dressing/masks
  and encourage further frame accrual. **Before** making the key price comparison
  with the Point fields. No SO(4) or nonzero correlation proof at this checkpoint.
* preserve the common bare prescription & along-path link, on those same prices.

See also `PF/Taps.lean` `tap_epoch`, stronger LP Loom receipt on ANY list of
kept first-Pane comparisons and arbitrary sized angle integrations. Here in
this statement instantiate on the literal pure gauge **divergence** Mark purchase
for all the kept operands (would work also with other first-pane & other
poses).

Upcoming lemmas need a *larger* geometry Stamp cap and power-3 etc.; can enlarge
directly inside the preparation receipt. None are being silently commissioned
here. When only requiring a substencil from the older labelled comparator,
check the obstruction before assuming descent to the actual physical state.
-/
set_option quotPrecheck false
variable (P : Spine)
local notation "K0"=>P.calibration
local notation "W0"=>P.width
local notation "Y"=> P.run
local notation "ζ(" s ")"=> ((Y).meter.a s).threshold
local notation "Ω(" s ")"=> hat P.par.R.L P.par.x s
local notation "𝒢"=> SU.group

-- bundle layouts to expose exact support criteria. Layout data **can depend
-- on s**, prices uniform for all that pass. Not asserting h support vs C etc
-- without fitting; InTest part of Mark registration; actual Pose price.
structure Divergence where
  S : Finset Cover -- paid, may be buffer-expanded
  C : Finset Cover -- mask
  f : Axis→Axis→Ruler 0
  h : ∀ i j,∀ d∈ f i j, planted S d.2
  e : outfit C S
  n : ℕ -- typically b_s
  c : ℤ → ℂ
  pc : ∑ i ∈ Finset.Icc (-(n:ℤ)) (n:ℤ),c i=0
  index : Axis

def Divergence.stencil (V:Divergence) (s:ℕ)(z:ℤ): P.Test := P.shifts 3 z (DivM P V.f V.h V.e ζ(s) V.index V.n V.c)
def Divergence.cost (V:Divergence)(z:ℤ) := plow (K0) 3 z (Native.strictExpense P V.S V.n)

structure Offered (N : Side) (Q:Type) (T:Type) [MeasurableSpace T] (r:ℕ) where
 S : Q→Support (More N)
 edge : Q→ PureForce.gaugeLink N
 center : Q→ Seat N
 clearRoots : Q → ℕ
 back : Q→ Bool
 -- positive at initial vertex edge.1, mirror at the other end so specify as desired.
 anchor : Q → Seat N
 rotor : (q:Q)→ Tap N (anchor q)
 weight : Q→ Fin 24→ ℝ
 dirs : T → Q → (𝒢).Color
 marked : ∀ q,∀ p∈rotor q, Fits (S q) p.2
 core : ∀ q,testRegion (edge q).1 (4*r+24) ⊆ S q
 shade : ∀ q,testRegion (center q) (clearRoots q)⊆ S q
 inside : ∀ q,rotorWindow r (edge q)⊆ Lattice.halo (clearRoots q) {center q}
 apart : Pairwise (Disjoint on S)
 seen : ∀ q, Measurable fun θ=>dirs θ q
 bounded : ∀ θ q, ‖dirs θ q‖ ≤ 1

variable {P}
def ConsultsBare (s:ℕ)(T:Finset Cover)(Z:P.Test):Prop:=
   let n := fun u=> side P.run (iPath P u) (depth P u)
   ∃ A:(u:ℕ)→ Evaluation (n u),
    (∀ᶠ u in atTop, let H:= toMark (A u); let i:=iPath P u; let k:=kPath P u;
      W P i k 1 ≠0 ∧ covariant H ∧ AtSupport false (Satin.region ((followBox («Λ»:=P.par) (l:=P.width))^[depth P u-s] T) _) H ∧
      Integrable (bareWeight P i k (bareBeta P (depth P u)) (A u)) (prior SU.group (More (n u))) ∧
      Journey.compass P.run i k s (exhibit P.run P.large s i Z.val)= W P i k (A u)/W P i k 1) ∧
    Tendsto (fun u=> let i:=iPath P u; let k:=kPath P u; W P i k (A u)/W P i k 1) atTop (𝓝 (P.E s Z.val))
-- use covariant directly
structure Plated (V:Divergence)(s:ℕ)(z:ℤ)(x:P.Spectrum0 3): Prop where
  fitting : let Z:= V.stencil P s z
            Z∈ bay (K0) (V.cost P z) true ∧ Z∈enclave (K0)
  calibration : First (K0) (V.stencil P s z)
  mirrored : First (K0) (P.reflectTest 3 (V.stencil P s z))
  centered : let Z:= V.stencil P s z; P.singleState 3 s x Z=0∧P.E s Z.val=0
  asksAlso : ConsultsBare s (V.cost P z) (V.stencil P s z)
  sectorRP : Tower.region 3 0 P.calibration.ℓ (V.cost P z)→
     let Z := V.stencil P s z; ∃ w:P.birthF 3 s Z,
     (P.singleState 3 s x) ((P.reflectTest 3) Z * Z) = ↑(‖P.viewF 3 x s w‖^2:ℝ) ∧
     P.E s ((P.reflectTest 3) Z * Z).val=(∫ y, (↑(‖P.viewF 3 y s w‖^2:ℝ):ℂ)∂P.pillars 3)

variable (P)
lemma licensed(V:Divergence)(s:ℕ)(z:ℤ)(x:P.Spectrum0 3): Plated V s z x:=by
 obtain ⟨b,q,h,_,l,c,hF,he,d⟩:= ticket P s V.n V.f ζ(s) V.index V.h V.e V.c V.pc z x
 refine ⟨⟨b,q⟩,h,l,⟨hF,he⟩,?_,d⟩
 obtain ⟨A,t,hA⟩:= PureForce.chartWithBareLaw P s (V.cost P z) (Tapestry.locates _ _ _ |>.1 b) q
 refine ⟨A,?_,hA⟩
 exact t -- lets position?

variable (s i k:ℕ){Q T:Type} [DecidableEq Q] [Fintype Q][MeasurableSpace T]
    (ν:Measure T)[IsProbabilityMeasure ν]

abbrev testX (D:Offered (side P.run i s) Q T P.par.J.n)(β:ℝ) (q:Q)(t:T) :=
    watch (rotorEps β) (D.rotor q) (Lattice.halo (D.clearRoots q) {D.center q}) (ζ(s)/3) (D.dirs t q)

variable (D:Offered (side P.run i s) Q T P.par.J.n)(β:ℝ)

abbrev stencilComp (p t:List Q)(F:Q→Evaluation (side P.run i s))(u:Q→Angle): T×Orbit (side P.run i s)→ℂ:=Function.uncurry (fun x=>assayShift p t D.edge (fun q t=>rotorLeft (D.back q) (nodes t) β (D.dirs x q)) (fun q t=>rotorRight (D.back q) (nodes t) β (D.dirs x q)) (fun q=>polarWeight (D.weight q)) (fun q U=>testX P s i D β q x U) F (Psi P i k s) u)

local notation "Θ"=> Scree.city (side P.run i s)
structure HasShifts (p t L:List Q)(F:Q→Evaluation (side P.run i s)):Prop where
 jointly : ∀ u, Integrable (stencilComp P s i k D β p t F u) (ν.prod (Θ))
 reading : Integrable (startPrice L F (Psi P i k s)) (Θ) ∧ denom P i k s≠0 ∧
      Journey.compass P.run i k s (toMark (keptMarks L F))=
        ((∫ x,startPrice L F (Psi P i k s) x∂(Θ))+∫ x,(∑ u:Q→Angle,∫ t', stencilComp P s i k D β p t F u (t',x) ∂ν) ∂(Θ))/denom P i k s

set_option linter.unusedSectionVars false in
lemma funded : ∀ᶠ s:ℕ in atTop,∀ i k:ℕ, Pay P.run s i k→
    ∀ {Q T:Type} [DecidableEq Q] [Fintype Q] [MeasurableSpace T], ∀ (ν: Measure T) [_h:IsProbabilityMeasure ν],
      ∀ (D:Offered (side P.run i s) Q T P.par.J.n),∀ β∈ Set.Icc (Ω(s)/2) (2*Ω(s)),
      ∀ (v:Q→ Divergence)(z:Q→ℤ),
      (∀ q,Satin.region ((v q).cost P (z q)) _ ⊆ D.S q) →
        ∃ F:Q→Evaluation (side P.run i s),
          (∀ q,Tapestry.exhibit P.run P.large s i ((v q).stencil P s (z q)).val=toMark (F q)∧ AtSupport false (D.S q) (toMark (F q))∧ covariant (toMark (F q))) ∧
          ∀ (p t L:List Q),p.Nodup→p ≠ []→(∀ i∈t,i∉p) → HasShifts P s i k ν D β p t L F:=by
  filter_upwards [tap_epoch.{0} P] with s a i k p
  intro Q T inst inst' instM ν hν D β h v z hz
  have hc(q:Q):∃ F:Evaluation (side P.run i s), Tapestry.exhibit P.run P.large s i ((v q).stencil P s (z q)).val=toMark F∧ AtSupport false (D.S q) (toMark F) ∧ covariant (toMark F):=by
    -- sector individual x not needed; extract from ticket after choosing any x there
    let x : P.Spectrum0 3 := Classical.arbitrary _
    let V:=v q
    obtain ⟨_,_,_,_,_,g,-⟩:= ticket P s V.n V.f ζ(s) V.index V.h V.e V.c V.pc (z q) x
    obtain ⟨A,l,c,b⟩:= g i
    exact ⟨A,l, c.mono (hz _), b⟩
  choose F w using hc
  refine ⟨F,w,fun p' t L hp he d=>?_⟩
  have hs:= a i k p β h ν D.S D.edge D.center D.clearRoots D.back D.anchor D.rotor D.dirs D.weight F D.seen D.bounded D.marked D.core D.shade D.inside D.apart (fun q=> (w q).2.1)
  have he := hs L t p' (p'.head he) (List.head_mem _) hp d
  exact ⟨he.2.1,he.1,he.2.2.2.1,he.2.2.2.2.1⟩

section elected
abbrev EarnedEpoch (s i k:ℕ): Prop:=
    ∀ {Q T:Type} [DecidableEq Q] [Fintype Q] [MeasurableSpace T], ∀ (ν: Measure T) [_h:IsProbabilityMeasure ν],
      ∀ (D:Offered (side P.run i s) Q T P.par.J.n),∀ β∈ Set.Icc (Ω(s)/2) (2*Ω(s)),
      ∀ (v:Q→ Divergence)(z:Q→ℤ),
      (∀ q,Satin.region ((v q).cost P (z q)) _ ⊆ D.S q) →
        ∃ F:Q→Evaluation (side P.run i s),
          (∀ q,Tapestry.exhibit P.run P.large s i ((v q).stencil P s (z q)).val=toMark (F q)∧ AtSupport false (D.S q) (toMark (F q))∧ covariant (toMark (F q))) ∧
          ∀ (p t L:List Q),p.Nodup→p ≠ []→(∀ i∈t,i∉p) → HasShifts P s i k ν D β p t L F

structure GradientGrant (K:P.Register) (D:TintDemand) (n:ℕ):Prop where
 elected : uniform P K thinRequest_LocalFieldBounds 1 1
 roster : P.Roster
 solvent : TintRateCommercial n (crayon D) P.par ∧ Solstitial P.par
 clock : ∃ A, Chronicle P.run A
 wall : Meritorious P.par
 stride : P.par.R.L.val %16=1
 terminal : ∀ i k, eff P i k 0=P.par.x
 sequence : (Tendsto (depth P) atTop atTop ∧ Tendsto (periodSize P) atTop atTop) ∧
   (∀ v:ℕ,0<bareBeta P v) ∧ ∀ x:ℕ, bareBeta P (depth P x)=eff P (iPath P x) (kPath P x) (depth P x)
 denominator : ∀ a:ℝ,0<a→∀ᶠ s in atTop,∀ i k :ℕ, Pay P.run s i k →
    Real.exp (sod (Y) k s i - (a* Ω(s)^(-(1/4:ℝ))) * sites (side P.run i s)) ≤ ‖denom P i k s‖
 -- Pressure support already in project on this P! not same alpha; see notes. doesn't include Fock.
 bleed : ∀ C:ℝ,∀ᶠ s in atTop,∀ i k:ℕ,s≤P.run.uv k → Papal.pressureLean P.run C s i k
 epoch : ∀ᶠ s in atTop,∀ i k:ℕ, Pay P.run s i k → EarnedEpoch P s i k
 plate : ∀ (x:P.Spectrum0 3) (V:Divergence) (s:ℕ) (z:ℤ), Plated V s z x
 installation : ∀ A:P.Spectrum0 3→Prop,(∀ᵐ x ∂P.pillars 3,A x) →
      ∃ x:P.Spectrum0 3,A x ∧ Nonempty (P.Ellis 3 x) ∧ P.lodestar 3 x ∧ P.party 3 K x
 -- the EXACT E→x link for this first comparison/future agenda; conditional E margin on actual P
 conditional_joint : ∀ (V:Divergence)(xAgenda:P.Spectrum0 3→Prop), (∀ᵐ x ∂P.pillars 3,xAgenda x)→
    ∀ (s:ℕ)(z:ℤ)(B:P.Test)(c:ℝ), let A:=V.stencil P s z;
    c< ‖P.E s (A*B).val‖→ ∃ x,xAgenda x∧ P.lodestar 3 x ∧ P.party 3 K x ∧ c<‖P.singleState 3 s x (A*B)-P.singleState 3 s x A * P.singleState 3 s x B‖

set_option linter.unusedSectionVars false in
theorem GradientSupply (D:TintDemand)(n:ℕ)(hn: (2:ℝ)*Ione.strive_E 6 ≤ (n:ℝ)):
    ∃ (P:Spine)(K:P.Register), GradientGrant P K D n:=by
  obtain ⟨Q,K,e,r,_,a,m,-,w,-,-,-,c⟩:= Spine.bookedS n hn D thinRequest_LocalFieldBounds 1 1 one_pos
  have hparty(x)(b:Q.lodestar 3 x):Q.party 3 K x:= Q.parting _ _ _ (Q.homes_weather _ _ (Q.all_phases _ _ b))
  have hg: ∀ᵐ x ∂Q.pillars 3,Q.lodestar 3 x ∧ Q.party 3 K x:= (Q.many_stars 3 K).mono fun x v=>⟨v,hparty x v⟩
  refine ⟨Q,K,e,r,a,c,m,w,PureForce.terminal Q e,⟨path_limits Q,beta_pos Q,beta_match Q⟩,
    Ldenominator Q m,Papal.prong_first Q.run,funded Q,(fun x V s z=>licensed Q V s z x),?_,?_⟩
  · intro A p; obtain ⟨x,g,t,b⟩:= (p.and hg).exists; exact ⟨x,g,Q.ellisP 3 x K,t,b⟩
  intro V A p s z B c X hc
  obtain ⟨x,⟨a,d,e⟩,b⟩:= canChoose Q s X B (fun x=>A x ∧ Q.lodestar 3 x ∧ Q.party 3 K x) (p.and hg) (fun x=>Or.inl ((licensed Q V s z x).centered.1)) c hc
  exact ⟨x,a,d,e,b⟩
#check @GradientSupply
end elected
end Native
end PureForce
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
