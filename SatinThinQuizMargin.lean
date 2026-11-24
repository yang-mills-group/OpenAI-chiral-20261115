import SatinFixedContrastNovember4
import SatinThinQuizPair
/-!
# Milestone 15.V. On the SAME experiment as the verified one: thin-field discrepancy.

Read `FullPrismLab`: NEW signal. The thin and unthinned-stencil measurements are each
on the same elected character, orientation, plane, positions and smears; no identification of
*different fields* or their numerical readings made. The earlier measurement is re-applied
and kept. Price a *new margin* from the profile rank on this very election.

In particular all later aperture/grid purchases actually report a FULL RANK
DISCREPANCY in these tests. Not by rescaling either state nor redefining the
opponent in terms of the fields after projection. The limit test that has this
signal is exactly identified. See `-QuizPair`.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set
variable (P:Spine)(x:P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "H"=> P.ColorHil 3 ξ
local notation "G"=> P.ManyF 3 ξ
local notation "Ω"=> P.heaven 3 ξ
local notation "λ'"=> P.enter 3 ξ
local notation "ℒ"=> Lead.Clan
local notation "k'"=> P.calibration
local notation "p[" t "]"=> P.singleState 3 t x
local notation "σ[" t "]"=> P.thinSplit x t
variable (A:ℕ→P.Apron)(c r n:ℕ→ℕ)(w:Lead.Clan→ Prism)(V : ∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))(g h:ℕ)
local notation "W"=> P.soldTrumpet A c r n w
variable (T:P.HandleWith x c r A n)
local notation "B[" z "," i "]"=> P.sold_birth x A c r n w z i T
local notation "l₀" => ([false,true]:List Bool)
local notation "I₁" a:max i:max => ((W a i).kiss P 3)
variable (R:P.ThinArmada x A c r n w T V g h)(J:P.Ellis 3 x) (μ:ℝ)(a b:Lead.Clan)
variable (F U: SampleDose)
local notation "Φ" a:max t:max i:max=> P.prepared t (I₁ a i) F
local notation "Ψ" b:max t:max i:max=> P.prepared t (W b i) U
local notation "X'" t:max i:max a:max=> P.thinGridKet x t (W a i) B[a,i] (flipDose F 3)
local notation "Y'" t:max i:max a:max=> P.thinGridKet x t (W a i) B[a,i] U
local notation "R₁" a:max=> DoseTravel.beam (G) F (P.earlierProfile x V w μ a)
local notation "R₂" a:max=> DoseTravel.beam (G) U (P.laterProfile x V w μ a)
local notation "X!" => P.readPrism x V w μ F U
local notation "X△" p:max q:max=> P.pointPrism x V w (q-p)
section constants
variable (M:CrossRead)
/-- dimensionless in the given normalization -- not comparing determinants in an external
scale. Lower bound for paid gap on fixed tests. Can be made as small as necessary for this use. -/
def LoudMargin(d:ℝ) : Prop:= d< ‖M.det‖ ∧ ∀ z, d < ‖M z z‖
lemma loud_fullrank(d:ℝ)(v:LoudMargin M d)(p:0<d) : ReadsSix M:=
    ⟨norm_pos_iff.mp (p.trans v.1),fun _=> norm_pos_iff.mp (p.trans (v.2 _))⟩
lemma loud_choose (h:ReadsSix M):∃ d:ℝ, 0<d ∧ LoudMargin M d:=by
 have ht:0 < ‖M.det‖:= norm_pos_iff.mpr h.1; have hq(z):0<‖M z z‖:= norm_pos_iff.mpr (h.2 z)
 exact (Eventually.and (self_mem_nhdsWithin (a:=0) (s:=Set.Ioi (0:ℝ))) (((gt_mem_nhds ht).and (eventually_all.mpr fun i:Lead.Clan=> gt_mem_nhds (hq i))).filter_mono nhdsWithin_le_nhds)).exists
lemma loud_near(d:ℝ)(v:LoudMargin M d): {N| LoudMargin N d} ∈ 𝓝 M :=
 (Eventually.and (((continuous_id (X:=CrossRead)).matrix_det.norm.tendsto M).eventually (lt_mem_nhds v.1))
                (show ∀ᶠ N:CrossRead in 𝓝 M, ∀ z, d< ‖N z z‖ from eventually_all.mpr fun i:Lead.Clan=> (((continuous_id (X:=Matrix Lead.Clan Lead.Clan ℂ)).matrix_elem i i).norm.tendsto M).eventually (lt_mem_nhds (v.2 i))))

private lemma allSeen{a:ℕ → ℕ}{t:ℕ → ℕ →  Prop}(q:∀ f:ℕ → ℕ, (∀ᶠ i in atTop,a i  ≤  f i) → ∀ᶠ i in atTop,t i (f i)): ∀ᶠ i in atTop,∀ s:ℕ, a i ≤ s →  t i s:=by
 choose f h u using (show ∀ i,∃ s, a i ≤  s ∧ (t i s  → ∀ m:ℕ,a i ≤ m → t i m) from fun i=>by
   by_cases p:∀ s:ℕ,a i ≤ s →  t i s; · exact ⟨a i,le_refl _,fun _=> p⟩
   obtain ⟨s,g,h⟩:= show ∃ s:ℕ, a i ≤  s∧ ¬t i s from by push Not at p; exact p
   exact ⟨s,g,fun e=>(h e).elim⟩)
 exact (q f (Eventually.of_forall h)).mono u
end constants

local notation "χ'"=> P.reportPrism A c r n w F U
local notation "X☷"=> P.thinJournal x A c r n w T F U
local notation "t!" i:max => c (n i)
variable (C L: Doorway)(s k:ℕ)(K:P.Register)
variable (u:C.Later L thinAlongOrder 0)(v:C.upper 3≤ -μ)(p:μ≤ L.lower 3)

section reports
variable (E:P.AuthorizedPair x A c r n w V T μ F U)
include E
lemma report_six_all (d:Set CrossRead)(z:d∈𝓝 X!) : ∀ᶠ i in atTop,∀ t:ℕ,t! i ≤ t→ χ' i t p[t]∈ d:= allSeen fun f h=> (E.during f h).eventually z
-- expose iterated price (finite all t eventually) of gap: X☷ priced from actual vs pure split on stencils.
lemma report_width_gap : ∀ᶠ i:ℕ in atTop, Tendsto (fun t=> χ' i t p[t] - χ' i t σ[t]) atTop (𝓝 (X☷ i)):=by
 filter_upwards [E.grid,E.comparison] with i h y; refine h.congr' ((eventually_ge_atTop (t! i)).mono fun t v=>?_); dsimp only; rw [(y t v).2,sub_zero]
lemma report_exact_gap(d:ℝ)(h:LoudMargin X! d) : ∀ᶠ i in atTop,∀ t:ℕ,t! i ≤ t→ LoudMargin (χ' i t p[t] - χ' i t σ[t]) d:= by
 filter_upwards [E.comparison,P.report_six_all x A c r n w V T μ F U E _ (loud_near _ d h)] with i r f t e
 rw [(r t e).2,sub_zero]; exact f t e
omit E
end reports

structure FullPrismLab : Prop where
 -- Ancillary limiting ceremony, estimates of the previous milestones
 supports : tsupport F.val ⊆ C.invites ∧ tsupport U.val ⊆ L.invites
 keeps : P.OnceHere x V w μ s k F U K C L -- old measurements! normalization, ranks, points
 order : C.Later L thinAlongOrder 0 ∧ C.upper 3 ≤ -μ ∧ μ ≤ L.lower 3
 armada : P.ThinArmada x A c r n w T V g h
 -- paid caps beyond a width-index, including all-grid capture within the selected boxes
 under_boxes : ∀ᶠ i:ℕ in atTop,∀ a:ℒ,P.spacePrice (I₁ a i) F ⊆ C.invites ∧ P.spacePrice (W a i) U ⊆ L.invites
 -- Plenum-style precision for points (stronger than ThinSeam)
 cut : ∀ᶠ i in atTop,∀ a b:ℒ,∀ x∈closure C.invites,∀ y∈closure L.invites,∀ j:Axis,x j+(I₁ a i).realWidth P j < y j - (W b i).realWidth P j
 exact_points : ∀ᶠ i in atTop,∀ a b:ℒ,∀ t:ℕ,c (n i)≤t →∀ p q:Cover,P.meshPose t p∈closure C.invites→ P.meshPose t q∈closure L.invites→
   P.commonWell 3 x (usher (I₁ a i) (W b i)) (usher (P.meshPose t p) (P.meshPose t q)) l₀= P.singleState 3 t x (P.issuing t (I₁ a i) p* P.issuing t (W b i) q)
 then_read : P.AuthorizedPair x A c r n w V T μ F U
 margin : ∃ d:ℝ,0<d ∧ LoudMargin X! d ∧ (∀ᶠ i in atTop,LoudMargin (X☷ i) d) ∧
      (∀ᶠ i in atTop,∀ t:ℕ,t! i ≤ t→ LoudMargin (χ' i t p[t] - χ' i t σ[t]) d)
 first_limit : ∀ᶠ i:ℕ in atTop,Tendsto (fun t=> χ' i t p[t]-χ' i t σ[t]) atTop (𝓝 (X☷ i))
 final_limit : Tendsto X☷ atTop (𝓝 X!)
 all_six : ReadsSix X!
 accepts (V':Set CrossRead)(p:V'∈𝓝 X!): ∀ᶠ i in atTop,∀ t:ℕ,t! i ≤ t→ χ' i t p[t]∈ V'

variable (B:P.OnceHere x V w μ s k F U K C L)
include R J u v p B
lemma honorLab : P.FullPrismLab x A c r n w V g h T μ F U C L s k K:=by
 have f:= B.earlier; have q:= B.laterProbe; have d₀:=B.eps
 have e:backwardSite F μ:= fun a t=>by linarith only [((f t) (3:Axis) (Set.mem_univ _)).2, v]
 have i:forwardSite U μ:= fun a v=> (lt_of_le_of_lt p (((q v) (3:Axis) (Set.mem_univ _)).1)).le
 let G':= P.authorizePair x A c r n w V g h T R J μ F U d₀ e i
 obtain ⟨d,h',z⟩:= loud_choose X! B.read
 exact {
   supports:=⟨f,q⟩
   keeps:= B
   order:= ⟨u,v,p⟩
   armada:= R
   under_boxes:= eventually_all.mpr fun a=> (P.thin_inside (fun i=> I₁ a i) (P.invertWidth _ (R.slender a)) _ C.doorOpen _ f).and (P.thin_inside _ (R.slender a) _ L.doorOpen _ q)
   cut:= eventually_all.mpr fun a=> eventually_all.mpr fun b=> P.illuminate_shrink_boxes x A c r n w V g h T R a b C L u
   exact_points:= eventually_all.mpr fun a=> eventually_all.mpr fun b=> P.illuminate_point_grid x A c r n w V g h T R J a b C L u
   then_read:= G'
   margin:= ⟨d,h',z,G'.width.eventually (loud_near _ d z), P.report_exact_gap x A c r n w V T μ F U G' d z⟩
   first_limit:= P.report_width_gap x A c r n w V T μ F U G'
   final_limit:= G'.width
   all_six:= B.read
   accepts:= P.report_six_all x A c r n w V T μ F U G' }
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.honorLab
