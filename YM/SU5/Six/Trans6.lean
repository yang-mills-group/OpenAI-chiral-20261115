import VerifiedSatinWidthAndUVNovember4
import YM.SU5.Six.Encounters
import YM.SU5.Six.SpectralBudget
import YM.SU5.Six.ResolutionBills
import YM.SU5.Six.PairChoices
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
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht

/-!
# Macroscopic six-family transport (standalone)

One supplied physical Spine, one Register, one route, one character. It suffices
that character's purchases are `Experiment`; these are actually attained
here in `uniform`, before the `i` threshold of the conclusion. Does NOT
require CP1/CP2 additional co-election(s) like Glass. Applies alike if
$x$ is being assumed with additional coexistence grants elsewhere in the
manuscript. Does not prove those other theorems here.

`#print Spine.Meters`, `Spine.ReflectMeter`, `Spine.AllOpens`, `Spine.ReturnsSix`
for reading. In particular `exposure` and `reading` give actual limits of the
`signed / partition`-normalized, *selected* joint measurements (operations
`prepared`, `arrayFine`), not the period/cutoff limit of the unselected inputs
without compression and vacuum choice. `point_density` is for Euclidean poses;
don't interpret it as a Lorentzian real-time measurement.

The indices name `Window.Family` not color or spin. See Elected.lean
for exact normalization and chiral source dictionary on this course.
Prices use all stencils/gauge nodes in the prescribed geometry; arbitrary
variations must still honor that geometry and the wall conditions in
`Encounters`, unless (as in (ii)) already paid up to the closure.
All of the statements support arbitrary *fixed* mac separations.

Interface names:
- `experiment_exists`, `macroscopicSatin`: construct/pick the course, x.
- `Spine.trans6`: take those choices as fixed data, perform.
- `Spine.bare_density, bare_chiral, terminalBeta, input_order,
  input_partition_unit, input_formula, input_paid,
  common_reading, P.returns_reading, comparator, fineReading, six_families`: how to read the
  source, election and normalization (Elected on Prototype.summit side).
  `P.transports_cap` extends across ALL the Euclidean axes by intertwining in
  the ground vacuum spaces. Don’t require/claim an intertwiner of ColorHil at
  different axes in the vacuum point continuation; our coherence uses equality of
  readings, the very same prepared marks across the axes for this x. No change
  of realizing rooms/GNS data.
  `input_order` is the input data ordered **mean**; see also `P.recovery`.
  Do not put a character price on the same RHS alone.
- `ReflectMeter.recorder`, `ReflectMeter.diminished`, `supports_ordered`,
  `Transmission.zoomVar`, `packs_within_rectangles` in Spine: some more
  explicit bounds and checks: also weak cross-measure testing with a varying
  bounded Borel test (bounded continuous limit test). Resolution price floors
  (t tending to infinity, the SAME P) with arbitrarily small slack in the
  reflected case. Cross-test footprints even if requiring the overall physical
  questions confined within the rectangles. `ReturnsSix` and its support and
  comparison results only use axis 3 gaps; the open rectangle case
  qualifies all axes.
- `Spine.cross_borel`: computation on any projected set of the matrix
  by polarization (genuine off-diagonal testing). `Spine.poseMirror,
  prepared_opposition, prepared_literal, prepared_at`, for placement rules.
- `Spine.msplit`, rich form incl products of not just 2 factors
  (use any order qualifying there; in fact all but first can pay even at
  mutual overlaps). `P.body_senses`, `P.sensor_mirror`, `extent` in Meters.
  `Spine.pocket_gap`, `P.issuance_senses`: stays charged throughout promotion.
  `ReturnsSix.disqualifies`: its consequence for macro smears.
  For the version where given arbitrary *independent* unital choices
  of raw marginals, not yet joint predictions, see Six.any_marginal_pair,
  Six.marginal_matter/gauge in PairChoices.
  For stability within fixed compact layouts see `Perturbative`.
- Does not define a new fully local continuum field algebra; isn't addressing
  the finite-width covariance/spacelike retest problem. No reliance on
  transferring `cantabile` (not assuming its fixed-stencil estimate suffices!)
  or `Wallpaper`; all mixed/diagonal estimates use the purchased `x`
  here. Elected limits on regulator sums come BEFORE the ordinary position
  smearing limit; not making a uniform assertion in changing cutoffs. The
  matrix lower bounds are for the elected measurements, not a bare-regulator
  phase or uniform over moving UV resolutions.
-/
namespace Spine
open Aria Casting Six Set
open Spectral Caino Spectral.Orbit.Prairie
open scoped BoundedContinuousFunction
variable (P:Spine)(x:P.Spectrum0 3)(s n:ℕ)
local notation "ξ"=> P.advocate 3 x 3
local notation "H"=> P.ManyF 3 ξ
-- bodies & how to read at height `t`, even when predicting a comparison instead
structure Meters (A:Set E4):Prop where
 extent : P.calibration.ℓ<n -- endpoint separation
 mirror (U:Dose AlleySpace)(G:Dose ℝ)(p:U.Normalized)(u:G.Normalized)(t:tsupport G.val ⊆ Set.Ioi (P.probeWidth s n 3)): P.ReflectMeter x s n (upperTest U G) A
 mixed (X Y:Doorway)(b:Orders)(h: Doorway.Later X Y b (P.probeWidth s n)): P.AllOpens x s n X Y b

-- heights can be cofinanced now, even if charging some very narrow moment window.
structure Transmission (c r:ℕ→ℕ):Prop where
 zoommat (z:SixCoefficients) : Tendsto (fun i=> P.zoomMatrix x (c i) (r i) z) atTop (𝓝 (diagonalLimit z))
 zoomCross (Z W:Lead.Clan)(f:ℕ→↥TimeHalf→ᵇ ℂ)(g:↥TimeHalf→ᵇ ℂ)(M:ℝ) (v:∀ i,‖f i‖≤ M) (p:∀ T:Set ↥TimeHalf, IsCompact T→TendstoUniformlyOn (fun i=>f i) g atTop T):
        Tendsto (fun i=>crossTest (P.zoomMatrix x (c i) (r i)) (onHalf (f i)) Z W) atTop
          (𝓝 (if Z=W then ∫ w,onHalf g w ∂(promenade Z:Measure E4) else 0))
 zoomVar (Z W:Lead.Clan)(f:ℕ→↥TimeHalf→ℂ)(g:↥TimeHalf→ᵇ ℂ)(M:ℝ) (m:∀ i,Measurable (f i)) (v:∀ i p,‖f i p‖≤ M) (p:∀ T:Set ↥TimeHalf, IsCompact T→TendstoUniformlyOn f g atTop T):
        Tendsto (fun i=>crossCost (P.zoomMatrix x (c i) (r i)) (f i) Z W) atTop
          (𝓝 (if Z=W then ∫ w,onHalf g w ∂(promenade Z:Measure E4) else 0))
 window(A:Set E4)(h:IsOpen A)(u:(Mink.inside∩A).Nonempty): ∃ d:ℝ,0<d∧∀ᶠ i in atTop,
      FrameBound.Coercive Lead.Clan H (P.spectralRoster x (c i) (r i) A) d
-- pay 1 vs 2 dimensions separately
 widths(j:Axis): Tendsto (fun i=>P.probeWidth (c i) (r i) j) atTop (𝓝 0)
 prescribe (X Y:Doorway)(b:Orders)(p: X.Later Y b 0): ∀ᶠ i in atTop, X.Later Y b (P.probeWidth (c i) (r i))
 prescribe_time(G:Dose ℝ)(w:tsupport G.val ⊆ Set.Ioi 0): ∀ᶠ i in atTop, tsupport G.val ⊆ Set.Ioi (P.probeWidth (c i) (r i) 3)

 charges (A:Set E4)(b:Fin 3→Bool)(w:WindowCost A b): ∀ᶠ i in atTop,P.Meters x (c i) (r i) A
 predicts (s:ℕ): ∃ X, Comparison P.calibration (P.singleState 3 s x) X ∧ X 1=1 ∧ GaugeWard P.calibration X ∧ MatterWard P.calibration X
 -- even not using any comparison oracle beyond the raw t measurement X
 every_split (s:ℕ)(B:P.Apron)(W:Bool)(X:P.Test→ₗ[ℂ]ℂ)(i:Cover) (v:P.Sensor B W)(u:B.s ≤ s)(h:Factors P.calibration X)(g:MatterWard P.calibration X∨GaugeWard P.calibration X) (L:List (P.Apron × Cover)) (t:∀ a∈ L,a.1.s ≤ s ∧ Disjoint (P.Aperture B (P.meshPose s i)) (P.Aperture a.1 (P.meshPose s a.2))) :
     X (P.issuing s B i * (L.map (fun a=>P.issuing s a.1 a.2)).prod)=0

-- `window` and `charge` strengthen in A compared to balls. One can take balls.
lemma authorize(V:Fin 3→Bool) : ∃ p:E4,∃ e>0, closure (Metric.ball p e) ⊆ (Mink.inside∩ terrain tracks3 ⁻¹' alley V) ∧ WindowCost (Metric.ball p e) V := by
 let U:=terrain tracks3 ⁻¹' alley V
 let X:=Mink.inside∩U
 let w:Space3:= WithLp.toLp 2 (fun i:Fin 3=> if V i then (1:ℝ) else -1)
 let p:= YM.position w (‖w‖+1)
 have hp:p∈X:= by
   constructor
   · change ‖YM.spatial p‖ < YM.time p; simp [p]
   change terrain tracks3 (YM.position w _)∈ alley V
   rw [Spine.gazed,YM.spatial_position]
   intro i; cases e:V i<;>simp [e,w]
 obtain ⟨e,h,t⟩:= Metric.mem_nhds_iff.mp ((Mink.open_inside.inter ((alley_open V).preimage (terrain_cont tracks3))).mem_nhds hp)
 have hu:0<e/2:= half_pos h
 have ht: closure (Metric.ball p (e/2))⊆ X:= subset_trans Metric.closure_ball_subset_closedBall ((Metric.closedBall_subset_ball (half_lt_self h)).trans t)
 exact ⟨p,e/2,hu,ht,isOpen_ball,⟨p, mem_ball_self hu⟩,(subset_trans subset_closure ht).trans Set.inter_subset_left,(subset_trans subset_closure ht).trans Set.inter_subset_right⟩

variable {P x}{K:P.Register}{c r:ℕ→ℕ}{J:P.Ellis 3 x}(B:Experiment P K c r x J)
include B
private lemma mirrorCharge(A:Set E4)(b:Fin 3→Bool)(w:WindowCost A b): ∀ᶠ i:ℕ in atTop,∀ (U:Dose AlleySpace)(G:Dose ℝ), U.Normalized→G.Normalized→ tsupport G.val⊆Set.Ioi (P.probeWidth (c i) (r i) 3)→ P.ReflectMeter x (c i) (r i) (upperTest U G) A:= by
 filter_upwards [lateRoster B A b w, B.launch.eager.tendsto_atTop.eventually (eventually_gt_atTop P.calibration.ℓ)] with i p g
 intro U G a h t
 let v:=p U G a h
 exact P.meter_odds x J (c i) (r i) _ (upper_weight U G a h) (upper_width U G t) g _ v.choose v.choose_spec.1 v.choose_spec.2.1 v.choose_spec.2.2
lemma atDoors : ∀ᶠ i:ℕ in atTop,∀ (X Y:Doorway)(b:Orders), X.Later Y b (P.probeWidth (c i) (r i)) → P.AllOpens x (c i) (r i) X Y b:= by
 have e:∀ᶠ i:ℕ in atTop,∀ b:Orders,∃ p∈ OrderChamber b (P.probeWidth (c i) (r i)), ReadsSix (P.pointMatrix x (c i) (r i) p):= by
    apply eventually_all.mpr
    intro b; filter_upwards [anchor_in b B, vary_pose_live b B] with i p v; exact ⟨_,p,v⟩
 filter_upwards [e,B.launch.eager.tendsto_atTop.eventually (eventually_gt_atTop P.calibration.ℓ)] with i p w
 exact fun X Y b a=> P.allClear x J (c i) (r i) X Y b a w (p b)
private lemma time_chooses (G:Dose ℝ)(p:tsupport G.val⊆ Set.Ioi 0) : ∀ᶠ i in atTop,tsupport G.val⊆ Set.Ioi (P.probeWidth (c i) (r i) 3):= by
 let X:=tsupport G.val; by_cases h:Set.Nonempty X; swap; · rw [show tsupport G.val=∅ from Set.not_nonempty_iff_eq_empty.mp h]; exact Eventually.of_forall (fun i=> Set.empty_subset _)
 obtain ⟨v,y,hx⟩:= G.budget.exists_isMinOn h continuous_id.continuousOn
 filter_upwards [(limit_width B.launch 3).eventually (gt_mem_nhds (show 0<v from p y))] with i u
 intro x h; exact lt_of_lt_of_le u (hx h)
theorem trans6 : P.Transmission x c r :=
 { zoommat:= B.zoommat.1
   zoomCross:= B.zoommat.2.1
   zoomVar:= P.zoom_borel_budget x c r B.zoommat.1
   window:= B.zoommat.2.2
   widths:=limit_width B.launch
   prescribe:= Doorway.affordable_margins B.launch
   prescribe_time := time_chooses B
   charges A b w:=((mirrorCharge B A b w).and ((atDoors B).and (B.launch.eager.tendsto_atTop.eventually (eventually_gt_atTop P.calibration.ℓ)))).mono fun i p=>⟨p.2.2,p.1,p.2.1⟩
   predicts s:= P.comparator s x
   every_split s B W X i v u h p L e:= P.msplit W s h p B i v u L e }
omit B

-- Corollary if the provided rectangles are meant also for the *region of the
-- entire experiments*, thus restricting even the body footprints with these
-- widths. Apply after requiring that P.Meters be attained for one desired
-- window (use `authorize` for one). Tests F,G fixed from then on; at t≥s all
-- pose support claims verified WITHOUT requiring any further change of F,G.
lemma packs_within_rectangles (T:P.Transmission x c r)(U:Set E4)(V:Fin 3→Bool)(w:WindowCost U V)(X Y:Doorway)(σ:Orders)(q:X.Later Y σ 0):
    ∀ᶠ i:ℕ in atTop,P.AllOpens x (c i) (r i) X Y σ ∧
       ∃ (a:ℝ) (F G:SampleDose), F.Normalized∧G.Normalized ∧ P.ReturnsSix x (c i) (r i) a F G ∧ tsupport F.val ⊆ X.invites ∧ tsupport G.val ⊆ Y.invites ∧
         (∀ m, P.spacePrice (P.RTest m (c i) (r i)) F ⊆ X.invites) ∧ (∀ m,P.spacePrice (P.FTest m (c i) (r i)) G ⊆Y.invites):= by
 let R(i:ℕ):= P.probeWidth (c i) (r i)
 filter_upwards [T.charges U V w,T.prescribe X Y σ q,X.spareCosts R T.widths, Y.spareCosts R T.widths] with i M h hx hy
 obtain ⟨a,p,t,u,_⟩:=(M.mixed X.spare Y.spare σ (X.spareLater h)).reading
 obtain ⟨F,G,x,y,f,g,l⟩:= u
 exact ⟨M.mixed X Y σ h, a,F,G,x,y,l,f.trans (subset_trans subset_closure X.sparesDoor),g.trans (subset_trans subset_closure Y.sparesDoor), fun m=> bounded_within (P.RTest ..) F f hx, fun m=> bounded_within (P.FTest ..) G g hy⟩
end Spine
open Spine
/-- Six-family macroscopic transport on a supplied Satin course. `L` lower
parameter on `P.par.x`, `M` upper on `P.par.d`; `d` and `x` then fixed.
`s=c i`, internal family length `n=r i≥z i`, at heights t≥s use the one
P.run and these readings, then let t go independently to infinity. -/
theorem macroscopicSatin (Y:Supplier)(L M:ℝ)(p:0<M)(z:ℕ→ℕ):
    ∃ (P:Spine)(K:P.Register), uniform P K Y L M ∧ ∃ (c r:ℕ→ℕ)(x:P.Spectrum0 3),z≤r ∧ ∃ J:P.Ellis 3 x, Experiment P K c r x J ∧ Transmission P x c r:= by
 obtain ⟨P,K,h,c,r,x,e,J,B⟩:= experiment_exists L M p Y z
 exact ⟨P,K,h,c,r,x,e,J,B,trans6 B⟩
#check @macroscopicSatin
#check @Spine.ReflectMeter.exposure
#check @Spine.ReflectMeter.bounded_below
#check @Spine.ReturnsSix.disqualifies
#check @Spine.Transmission.charges
#print axioms macroscopicSatin
#print axioms Spine.cross_borel
#print axioms Spine.fineReading
#print axioms Spine.common_reading
#print axioms Spine.input_formula
#print axioms Spine.input_order
#print axioms Spine.bare_chiral
#print axioms Spine.six_families -- in Spine
#print axioms Spine.front_charge
#print axioms Spine.issued_central
#print axioms Spine.body_senses
#print axioms Spine.prepared_opposition
#print axioms Spine.prepared_literal
#print axioms Spine.prepared_at
#print axioms Spine.prepared_color
#print axioms Spine.authorize
#print axioms Six.any_marginal_pair
#print axioms Spine.packs_within_rectangles
#print axioms Spine.ReflectMeter.recorder
#print axioms Spine.ReflectMeter.diminished
#print axioms Spine.cost_isCompact
#print axioms Spine.supports_ordered
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
