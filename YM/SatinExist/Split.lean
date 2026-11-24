import YM.SatinExist.Twin

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4000
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

variable (P : Spine) (x : P.Spectrum0 3)
local notation "ξ" => P.advocate 3 x 3
local notation "H" => P.ColorHil 3 ξ
local notation "G" => P.ManyF 3 ξ
local notation "κ" => P.calibration
local notation "E[" k "]" => P.singleState 3 k x
local notation "M[" k "]" => P.thinSplit x k
local notation "λ'" => P.enter 3 ξ

/-!
## Quantitative non-determination of the split by these vacuum-field data
-/
section
variable {D₁ : ℕ → P.Apron} (F : SampleDose) {μ : ℝ}
lemma belowWall_late (p : P.thicknessZero D₁) (hp : 0 < μ) (q : backwardSite F μ) :
    ∀ᶠ i in atTop, P.WallBefore (D₁ i) F 0 := by
  filter_upwards [(p 3).eventually (gt_mem_nhds hp)] with i h
  intro a t
  linarith only [q a t, show (D₁ i).realWidth P 3 < μ from h]
lemma aboveWall_late (p : P.thicknessZero D₁) (hp : 0 < μ) (q : forwardSite F μ) :
    ∀ᶠ i in atTop, P.WallAfter (D₁ i) F 0 := by
  filter_upwards [(p 3).eventually (gt_mem_nhds hp)] with i h
  intro a t
  exact (zero_add _).trans_lt ((show (D₁ i).realWidth P 3 < μ from h).trans_le (q a t))
lemma prior_uses (q : backwardSite F μ) : forwardSite (flipDose F 3) μ := by
  intro a h
  rw [flipBudget] at h
  have v := q (poseMirror 3 a) h
  change μ ≤ -(opposeR 3 a 3) at v
  rwa [show opposeR 3 a 3 = -a 3 from if_pos rfl, neg_neg] at v
end

private lemma varying {X : ℕ → ℕ} {p : ℕ → ℕ → Prop}
    (v : ∀ f:ℕ→ℕ, (∀ᶠ i in atTop,X i ≤ f i) → ∀ᶠ i in atTop,p i (f i)) :
    ∀ᶠ i in atTop,∀ s:ℕ,X i ≤ s → p i s := by
  -- as in SatinThinQuizMargin
  choose f h u using (show ∀ i:ℕ, ∃ s:ℕ, X i ≤ s ∧ (p i s → ∀ m:ℕ, X i ≤ m → p i m) from fun i=> by
    by_cases q : ∀ s:ℕ, X i ≤ s → p i s
    · exact ⟨X i, le_rfl, fun _=> q⟩
    obtain ⟨s,a,b⟩ := show ∃ s:ℕ, X i ≤ s ∧ ¬ p i s from by push Not at q; exact q
    exact ⟨s,a,fun e=>(b e).elim⟩)
  exact (v f (Eventually.of_forall h)).mono u

variable (A : ℕ → P.Apron) (c r n : ℕ→ℕ) (w : Lead.Clan→ Prism)
variable (V : ∀ j : Axis, List Axis → ℝ → P.ColorHil j (P.advocate 3 x j))
variable (g h : ℕ) (X : P.HandleWith x c r A n)
local notation "B" => P.bareTwin A w
local notation "Sold" => P.soldTrumpet A c r n w
local notation "B'" D:max a:max i:max => P.bareTwin_birth x A c r n w V g h X D a i
local notation "s'" a:max i:max => P.sold_birth x A c r n w a i X
local notation "Θ" a:max => P.profilesH x w a V
local notation "ΠR" a:max => P.profilesZ x V w a
local notation "s!" i:max => c (n i)
variable (F U : SampleDose)
local notation "R₁" μ:max a:max => DoseTravel.beam G F (P.earlierProfile x V w μ a)
local notation "R₂" μ:max a:max => DoseTravel.beam G U (P.laterProfile x V w μ a)
local notation "W" μ:max => P.readPrism x V w μ F U
local notation "X₁" a:max i:max t:max => P.prepared t ((Sold a i).kiss P 3) F
local notation "X₂" a:max i:max t:max => P.prepared t (Sold a i) U
local notation "Y₁" a:max i:max t:max => P.prepared t ((B a i).kiss P 3) F
local notation "Y₂" a:max i:max t:max => P.prepared t (B a i) U

def twinPrism (Q : ℕ→P.Test→ₗ[ℂ]ℂ) (i t:ℕ) : CrossRead :=
  Matrix.of (fun a b:Lead.Clan => Q t ((Y₁ a i t)*(Y₂ b i t)))

section
variable (D : P.ThinArmada x A c r n w X V g h) (R : P.Ellis 3 x)
include X
lemma twin_split_pays (pc : ∀ i, PureGauge κ (A i).F) (i t : ℕ) (e:s! i≤t) (a b : Lead.Clan) :
    PureGauge κ (Y₁ a i t) ∧ PureGauge κ (Y₂ b i t) ∧
    E[t] (Y₁ a i t)=0 ∧ E[t] (Y₂ b i t)=0 ∧
    M[t] (Y₁ a i t)=0 ∧ M[t] (Y₂ b i t)=0 ∧
    M[t] ((Y₁ a i t)*(Y₂ b i t))=E[t] ((Y₁ a i t)*(Y₂ b i t)) := by
  have hu := (X.already i).trans e
  have h₁ := P.pureTwin_smear _ (P.pureTwin_kiss _ (P.pureTwin_pure A w pc a i) 3) t F
  have h₂ := P.pureTwin_smear _ (P.pureTwin_pure A w pc b i) t U
  have q₁ : ∀ a:Lead.Clan, E[(A i).s] (B a i).F = 0 := fun a=>
    P.trumpets_center (w a) (P.pricedTwinBase (A i) a) x
  have q₂ : E[(A i).s] ((B a i).kiss P 3).F = 0 :=
    ((P.common_reading (A i).s x (B a i).F 3).2.2.1).trans
      ((congrArg star (q₁ a)).trans (star_zero _))
  have e₁ := P.Dose_zero t ((B a i).kiss P 3) F x q₂ hu
  have e₂ := P.Dose_zero t (B b i) U x (q₁ b) hu
  let m := (P.thin_comparator_LocalFieldBounds x t).1
  exact ⟨h₁,h₂,e₁,e₂,(m.link _ h₁).trans e₁,(m.link _ h₂).trans e₂,
    m.link _ (P.pureTwin_mul _ _ h₁ h₂)⟩

variable (μ : ℝ) (hp : 0 < μ) (q : backwardSite F μ) (p : forwardSite U μ)
include D R p q hp
lemma twin_actual_during {t : ℕ→ℕ} (u:∀ᶠ i in atTop, s! i≤ t i) :
    Tendsto (fun i => P.twinPrism A w F U (fun t=> E[t]) i (t i)) atTop (𝓝 (W μ)) := by
  have hv : Tendsto t atTop atTop := tendsto_atTop_mono' _ u D.fusion.high.tendsto_atTop
  refine tendsto_pi_nhds.mpr fun a=> tendsto_pi_nhds.mpr fun b=> ?_
  have h₁ := (P.bareTwin_test x A c r n w V g h X D (flipDose F 3) R a μ hp (prior_uses F q)).2 t hv -- order D F?
  have h₂ := (P.bareTwin_test x A c r n w V g h X D U R b μ hp p).2 t hv
  change Tendsto _ _ (𝓝 (λ' (P.readProfile x (flipDose F 3) μ (ΠR a)))) at h₁
  rw [P.illuminate_flip x w V μ a F] at h₁
  have hx := h₁.inner (𝕜:=ℂ) h₂
  rw [(λ').inner_map_map] at hx
  apply hx.congr'
  have he := P.belowWall_late F (P.bareTwin_slender x A c r n w V g h X D a) hp q
  have hz := P.aboveWall_late U (P.bareTwin_slender x A c r n w V g h X D b) hp p
  filter_upwards [he,hz,u] with i hb hf u1
  have h := (X.already i).trans u1
  exact (P.thin_pair_grid x (t i) (B a i) (B' D a i) F (B b i) (B' D b i) U hb hf h h).symm
end

section
variable {C L : Doorway} {s k : ℕ} {K:P.Register} {μ:ℝ}

/-- The comparison **does not descend** to the current field data. See `TwinSensitivity` for
contexts required. Keep smears, heights of measurements, and both original footprint boxes.
Difference tested in a matrix of exactly the same normalized problem, letting consultation grid
advance and also the width index. -/
structure TwinSensitivity (D : P.FullPrismLab x A c r n w V g h X μ F U C L s k K) : Prop where
  small (a : Lead.Clan) (ε : ℝ) (p : 0 < ε) :
    ∀ᶠ i in atTop, P.ThinFootprints (fun i=> ((P.bareTwin A w) a i).kiss P 3) i ε ∧
      P.ThinFootprints ((P.bareTwin A w) a) i ε
  supports : ∀ᶠ i in atTop,∀ a:Lead.Clan,
    P.spacePrice ((B a i).kiss P 3) F ⊆ C.invites ∧ P.spacePrice (B a i) U ⊆ L.invites
  charged_poses (a b:Lead.Clan) : ∀ᶠ i in atTop,∀ t:ℕ,s! i≤t →
      (∃ y:P.Test,P.reflectTest 3 y=(Y₁ a i t) ∧
        ∃ e:P.birthF 3 t y, P.viewF 3 (P.advocate 3 x 3) t e=
          P.thinGridKet x t (B a i) (B' D.armada a i) (flipDose F 3)) ∧
      ∃ e:P.birthF 3 t (Y₂ b i t), P.viewF 3 (P.advocate 3 x 3) t e=
        P.thinGridKet x t (B b i) (B' D.armada b i) U
  heated (a:Lead.Clan)(t:ℝ)(p:0<t) :
    Tendsto (fun i=> P.cradleH x (B a i) (B' D.armada a i) t) atTop
      (𝓝 (P.profilesH x w a V t)) ∧
    Tendsto (fun i=> P.cradleG x (B a i) (B' D.armada a i) t) atTop
      (𝓝 (P.profilesZ x V w a t))
  pose_test (Z:SampleDose) (a:Lead.Clan)(t:ℝ)(p:0<t) (q:forwardSite Z t) :
    Tendsto (fun i => P.thinKet x (Sold a i) (s' a i) Z - P.thinKet x (B a i) (B' D.armada a i) Z)
      atTop (𝓝 0) ∧ ∀ t:ℕ→ℕ,Tendsto t atTop atTop → Tendsto (fun i=>
        P.thinGridKet x (t i) (Sold a i) (s' a i) Z - P.thinGridKet x (t i) (B a i) (B' D.armada a i) Z)
      atTop (𝓝 0)
  actual (O : Set CrossRead)(p : O ∈ 𝓝 (P.readPrism x V w μ F U)) :
    ∀ᶠ i in atTop,∀ t:ℕ,c (n i) ≤ t → P.twinPrism A w F U (fun t=> E[t]) i t ∈ O
  twin_pure (i t:ℕ)(e:c (n i) ≤ t)(a b:Lead.Clan) :
    PureGauge κ (Y₁ a i t) ∧ PureGauge κ (Y₂ b i t)
  centered_cost (i t:ℕ)(e:c (n i) ≤ t) :
    (∀ a:Lead.Clan,E[t] (Y₁ a i t)=0 ∧ E[t] (Y₂ a i t)=0 ∧
      M[t] (Y₁ a i t)=0 ∧ M[t] (Y₂ a i t)=0) ∧
    P.twinPrism A w F U (P.thinSplit x) i t = P.twinPrism A w F U (fun t=> E[t]) i t
  -- the very gap between two COMPATIBLE purchases using the claimed same split predictor.
  margin : ∃ d : ℝ,0 < d ∧ LoudMargin (P.readPrism x V w μ F U) d ∧
    ∀ᶠ i in atTop,∀ t:ℕ,s! i ≤ t → LoudMargin
      (P.twinPrism A w F U (P.thinSplit x) i t - P.reportPrism A c r n w F U i t M[t]) d
  -- and even if replacing just the LATE measurement with its TWIN on that *SAME* original early choice,
  -- with comparison early normalized to twin (pure clover), impossible to match both split bills.
  crossed : ∃ d:ℝ,0 < d ∧ ∀ᶠ i in atTop,∀ t:ℕ,s! i ≤ t →
    ∀ a:Lead.Clan, M[t] ((X₁ a i t)*(Y₂ a i t))=0 ∧ d < ‖M[t] ((Y₁ a i t)*(Y₂ a i t))‖


private lemma point_comparison (A₁ A₂ : P.Apron) (a : Lead.Clan)
    (b : P.WallBefore A₁ F 0) (p : P.WallAfter A₂ U 0)
    (sa : P.Sensor A₁ a.2) (t:ℕ) (u : A₁.s ≤ t) (v : A₂.s ≤ t) :
    M[t] (P.prepared t (A₁.kiss P 3) F * P.prepared t A₂ U)=0 :=
  P.split_test t _ F _ U (P.test_apart (A₁.kiss P 3) F 0 A₂ U b p) u v a.2
    (P.sensor_mirror a.2 3 A₁ sa) (M[t]) (P.thin_comparator_LocalFieldBounds x t).1.factors (Or.inr (P.thin_comparator_LocalFieldBounds x t).2.2.1)

private lemma earns_cross (D : P.FullPrismLab x A c r n w V g h X μ F U C L s k K)
    {d:ℝ}
    (he : ∀ a:Lead.Clan, ∀ᶠ i in atTop, P.WallBefore (Sold a i) F 0)
    (hv : ∀ a:Lead.Clan, ∀ᶠ i in atTop, P.WallAfter (B a i) U 0)
    (z : ∀ i t:ℕ, s! i ≤ t → P.twinPrism A w F U (P.thinSplit x) i t =
      P.twinPrism A w F U (fun t=> E[t]) i t)
    (ea : ∀ᶠ i in atTop, ∀ t:ℕ, s! i ≤ t → LoudMargin (P.twinPrism A w F U (fun t=> E[t]) i t) d) :
    ∀ᶠ i in atTop,∀ t:ℕ,s! i ≤ t →
    ∀ a:Lead.Clan, M[t] ((X₁ a i t)*(Y₂ a i t))=0 ∧ d < ‖M[t] ((Y₁ a i t)*(Y₂ a i t))‖ := by
  let B₀:= D.armada
  filter_upwards [ea,eventually_all.mpr he,eventually_all.mpr hv] with i pp ht hu t k a
  have hn : LoudMargin (P.twinPrism A w F U (P.thinSplit x) i t) d := by
    rw [z i t k]; exact pp t k
  refine ⟨?_,hn.2 a⟩
  exact point_comparison P x F U (Sold a i) (B a i) a (ht a) (hu a) (D.armada.sensor a i) t k
    ((X.already i).trans k)

private lemma charges (D : P.FullPrismLab x A c r n w V g h X μ F U C L s k K) (a b : Lead.Clan) (hS : backwardSite F μ) (hv' : forwardSite U μ) :
    ∀ᶠ i in atTop,∀ t:ℕ,s! i ≤ t →
      (∃ y:P.Test,P.reflectTest 3 y=(Y₁ a i t) ∧
        ∃ e:P.birthF 3 t y, P.viewF 3 (P.advocate 3 x 3) t e=
          P.thinGridKet x t (B a i) (B' D.armada a i) (flipDose F 3)) ∧
      ∃ e:P.birthF 3 t (Y₂ b i t), P.viewF 3 (P.advocate 3 x 3) t e=
        P.thinGridKet x t (B b i) (B' D.armada b i) U := by
  let B₀ := D.armada
  have h₁ := P.belowWall_late F (P.bareTwin_slender x A c r n w V g h X D.armada a) D.keeps.eps hS
  have h₂ := P.aboveWall_late U (P.bareTwin_slender x A c r n w V g h X D.armada b) D.keeps.eps hv'
  filter_upwards [h₁,h₂] with i p q t e
  have hz := (X.already i).trans e
  exact ⟨P.thin_grid_flip x t (B a i) (B' B₀ a i) F p hz,
    P.thin_grid_view x t (B b i) (B' B₀ b i) U q hz⟩

lemma priceTwinSensitivity (R : P.Ellis 3 x) (p : ∀ i:ℕ,PureGauge κ (A i).F)
    (D : P.FullPrismLab x A c r n w V g h X μ F U C L s k K) :
    P.TwinSensitivity x A c r n w V g h X F U D := by
  have hp : 0 < μ := D.keeps.eps
  have h₁ : backwardSite F μ := fun a t=> by
    linarith only [((D.supports.1 t) (3:Axis) (Set.mem_univ _)).2, D.order.2.1]
  have h₂ : forwardSite U μ := fun a t=>
    le_of_lt (D.order.2.2.trans_lt (((D.supports.2 t) (3:Axis) (Set.mem_univ _)).1))
  let B₀ := D.armada
  have hS(a : Lead.Clan) := P.bareTwin_slender x A c r n w V g h X B₀ a
  have e₀(O:Set CrossRead)(q:O∈𝓝 (W μ)) : ∀ᶠ i in atTop, ∀ t:ℕ, s! i ≤ t → P.twinPrism A w F U (fun t=> E[t]) i t ∈ O :=
    varying fun t e => (P.twin_actual_during x A c r n w V g h X F U D.armada R μ hp h₁ h₂ e).eventually q
  have z(i t:ℕ)(e:s! i ≤ t) : P.twinPrism A w F U (P.thinSplit x) i t=P.twinPrism A w F U (fun t=> E[t]) i t :=
    funext fun a => funext fun b=>
      (P.twin_split_pays x A c r n w X F U p i t e a b).2.2.2.2.2.2
  obtain ⟨d,pd,hd,_⟩ := D.margin
  have ea : ∀ᶠ i in atTop, ∀ t:ℕ, s! i ≤ t → LoudMargin (P.twinPrism A w F U (fun t=> E[t]) i t) d :=
    e₀ _ (loud_near _ d hd)
  have he(a:Lead.Clan) := P.belowWall_late F (B₀.slender a) hp h₁
  have hv(a:Lead.Clan) := P.aboveWall_late U (hS a) hp h₂
  refine {
    small := fun a ε p=>
      (P.thin_qualify _ (P.invertWidth _ (hS a)) ε p).and (P.thin_qualify _ (hS a) ε p)
    supports := eventually_all.mpr fun a=>
      (P.thin_inside _ (P.invertWidth _ (hS a)) _ C.doorOpen _ D.supports.1).and
        (P.thin_inside _ (hS a) _ L.doorOpen _ D.supports.2)
    heated := P.bareTwin_heated x A c r n w V g h X D.armada
    pose_test := fun Z a=> P.same_thin_vacuum_profile x A c r n w V g h X D.armada Z R a
    charged_poses := fun a b => charges P x A c r n w V g h X F U D a b h₁ h₂
    actual := e₀
    twin_pure := fun i t e a b=>
      let k := P.twin_split_pays x A c r n w X F U p i t e a b; ⟨k.1,k.2.1⟩
    centered_cost := fun i t e => ⟨fun a =>
        let k := P.twin_split_pays x A c r n w X F U p i t e a a
        ⟨k.2.2.1,k.2.2.2.1,k.2.2.2.2.1,k.2.2.2.2.2.1⟩, z i t e⟩
    margin := ⟨d,pd,hd,?_⟩
    crossed := ⟨d,pd,earns_cross P x A c r n w V g h X F U D he hv z ea⟩ }
  · filter_upwards [ea,D.then_read.comparison] with i hi hs t k
    rw [(hs t k).2,sub_zero,z i t k]
    exact hi t k
end
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
