import WakeRoad.AtlasArc
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 200000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical ContDiff
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set
open OS.Semigroup YM.OS.Semigroup.Gingham
open Boundary Probe
namespace Spine.NativeSeam
open YM.OS YM.OS.Semigroup SatinRegistration YM.Velour YM.SatinMacro
variable (P:Spine)(x:P.Spectrum0 3)
local notation "jₓ"=> (3:Axis)
local notation "ξ"=> P.advocate 3 x jₓ
local notation "G"=> P.ManyF jₓ ξ
local notation "ℰ"=> P.seasons jₓ ξ
local notation "Ω"=> P.heaven jₓ ξ
local notation "W"=>carry P x
local notation "T"=>(ℰ).E
local notation "q*"=> foldSpace
abbrev coreAt (D:P.Apron): (G).Op:=P.toStageG jₓ ξ (D.engine P jₓ ξ)
abbrev properAt (D:P.Apron)(k:ℝ≥0): (G).Op:=T k * coreAt P x D * T k
lemma native_stage(D:P.Apron)(k:ℝ≥0): properAt P x D k=P.stageG jₓ ξ D (D.allowance P jₓ+k) (D.allowance P jₓ+k):=by
 unfold stageG stageH; rw [add_tsub_cancel_left,P.bank_both]
lemma core_table(D:P.Apron): coreAt P x D=P.tableau jₓ ξ 0 (D.engine P jₓ ξ):=by unfold tableau;rw [neg_zero,P.cart_zero]; rfl
variable (D:P.Apron)(k:ℝ≥0)
lemma core_paid: coreAt P x D Ω=flashY x D jₓ:=by rw [core_table,P.tableMaps,P.cart_zero];rfl
lemma star_paid: (coreAt P x D).adjoint Ω=glareY x D jₓ:=by rw [core_table]; rfl
-- actual strong TRANSLATION smooth smear on G; same as other projects' rasp price; not local assertion on real support
abbrev actor:= (ℰ).rasp (properAt P x D k)
lemma priced_actor (F:SampleDose) : (star (actor P x D k (sachet_LocalFieldBounds F))) Ω= NativeSeam.flash P x D k F ∧ actor P x D k (sachet_LocalFieldBounds F) Ω=strike P x D k F:=by
    unfold actor; rw [(ℰ).rasp_star,sachet_bar]; simp_rw [(ℰ).rasp_apply,integral_sachet]
    constructor
    · unfold flash faded DoseTravel.beam;
      refine integral_congr_ae (ae_of_all _ (fun p=>?_))
      have hp:(sachet_LocalFieldBounds F) (q*.symm p)= (F.val p:ℂ):=rfl
      dsimp only; rw [hp]; refine congrArg _ ?_; unfold dangle properAt; rw [star_mul,star_mul]; simp only [mul_apply_eq_comp,home_flight,ContinuousLinearMap.star_eq_adjoint,(ℰ).sym,P.heaven_hot, star_paid]
    unfold strike sounded DoseTravel.beam;
    refine integral_congr_ae (ae_of_all _ (fun p=>?_))
    have hp:(sachet_LocalFieldBounds F) (q*.symm p)= (F.val p:ℂ):=rfl
    dsimp only; rw [hp]; refine congrArg _ ?_; unfold dangle; simp only [mul_apply_eq_comp,home_flight, P.heaven_hot, properAt,core_paid]
lemma actors_prices (A:P.Apron)(F U:SampleDose): RealCosts P x A D F U k=
    (inner ℂ Ω ((actor P x A k (sachet_LocalFieldBounds F)*actor P x D k (sachet_LocalFieldBounds U)) Ω),inner ℂ Ω ((actor P x A k (sachet_LocalFieldBounds F)) Ω),inner ℂ Ω ((actor P x D k (sachet_LocalFieldBounds U)) Ω)):=by
    unfold RealCosts
    rw [←(priced_actor P x D k U).2,←(priced_actor P x A k F).1,ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]; rfl
-- REAL and Eu support claims: actual occupied boxes vs regions and same test translations (not saying real swap)
lemma spacelike_box {p q v y:Vantage} {B:P.Apron}(h:Cracks P B D p q)(g:v∈P.Aperture B p)(a:y∈P.Aperture D q):(foldSpace.symm y-foldSpace.symm v) ∈ YM.Mink.spacelike:=by
    rw [Mink.lateral]
    let r:= foldSpace.symm y-foldSpace.symm v
    change |y jₓ-v jₓ|<‖spatial r‖
    have he : 0<y jₓ - v jₓ:=by
       linarith only [(abs_le.mp (g jₓ)).2,(abs_le.mp (a jₓ)).1,h.2.2.1 jₓ]
    rw [abs_of_pos he]
    calc
    _ < y 0-v 0:=by linarith only [(abs_le.mp (g jₓ)).1,(abs_le.mp (a jₓ)).2,(abs_le.mp (a (0:Axis))).1,(abs_le.mp (g (0:Axis))).2,h.2.2.2]
    _ ≤ _ := by
       have hv:=PiLp.norm_apply_le (p:=2) (spatial r) (0:Fin 3)
       exact (le_abs_self _).trans hv
lemma boxes_qualify {p q v y:Vantage} {B:P.Apron}(h:Cracks P B D p q)(g:v∈P.Aperture B p)(a:y∈P.Aperture D q)(i:Axis):v i<y i:=by linarith only [(abs_le.mp (g i)).2,(abs_le.mp (a i)).1,h.2.2.1 i]
lemma Hallmark.spacing{B:P.Apron}{F V:SampleDose}{δ:ℝ}(t:Hallmark P x B D F V δ) {p q:Vantage}(a:p∈ P.spacePrice B F)(b:q∈P.spacePrice D V) :
    (∀ i:Axis,p i<q i) ∧ (foldSpace.symm q-foldSpace.symm p)∈YM.Mink.spacelike:=by
    obtain ⟨R,R',-,-,-,-,tA,tB,v⟩:=t.all_regions; obtain ⟨A,g,o⟩:=Set.mem_iUnion₂.mp a; obtain ⟨A',h,l⟩:= Set.mem_iUnion₂.mp b
    exact ⟨boxes_qualify P D (v A (subset_closure (tA g)) A' (subset_closure (tB h))) o l,spacelike_box P D (v A (subset_closure (tA g)) A' (subset_closure (tB h))) o l⟩
lemma site_in (F:SampleDose)(p:E4)(h:p∈tsupport (sachet_LocalFieldBounds F)): foldSpace p∈ P.spacePrice D F:= Set.mem_iUnion₂.mpr ⟨_,sachet_support F ▸ h, fun i=>by simpa only [sub_self,abs_zero] using (D.real_width_pos P i).le⟩ -- field projection args
-- Orbits in real & receipts numerically P x with physical disjoint margins charged
variable (B:P.Apron)(F V:SampleDose)(δ:ℝ)
structure Ballast : Prop extends Hallmark P x B D F V δ where
    spaces (p q:Vantage)(a:p∈ P.spacePrice B F)(b:q∈P.spacePrice D V) :
        (∀ i:Axis,p i<q i) ∧ (foldSpace.symm q-foldSpace.symm p)∈YM.Mink.spacelike
    wear (p q:E4) : p∈tsupport (sachet_LocalFieldBounds F) → q∈ tsupport (sachet_LocalFieldBounds V) → q-p∈YM.Mink.spacelike
    credentials (A:P.Apron)(V':SampleDose) : (A=B∧ V'=F ∨ A=D∧V'=V) → (∀ n:ℕ,A.s ≤ n→ P.asked_at n (P.prepared n A V') (P.spacePrice A V') ∧ P.prepared n A V'∈enclave P.calibration)
    seal0 (y:ℝ≥0): (RealCosts P x B D F V y).2=(native P x B,native P x D)
    calendar: Tendsto (gridValues P x B D F V) atTop (𝓝 (EuCosts P x B D F V)) ∧
          Tendsto (RealCosts P x B D F V) (𝓝[>] 0) (𝓝 (RealCosts P x B D F V 0))
    actors(t:ℝ≥0) : let a:=actor P x B t (sachet_LocalFieldBounds F); let b:=actor P x D t (sachet_LocalFieldBounds V)
                     RealCosts P x B D F V t=(inner ℂ Ω ((a*b) Ω),inner ℂ Ω (a Ω),inner ℂ Ω (b Ω))
    -- conditional provision for actual pure/pure cases at stage n if available. no availability assertion at this milestone
    if_pure(n:ℕ): PureGauge P.calibration (P.prepared n B F) → PureMatter P.calibration (P.prepared n D V) →
            Gingham.guess (gridValues P x B D F V n)= P.thinSplit x n (P.prepared n B F*P.prepared n D V)
theorem ribbons (J:P.Ellis 3 x)(t:Hallmark P x B D F V δ): Ballast P x D B F V δ :=by
    have hp (A:P.Apron)(V:SampleDose)(n:ℕ)(q:A.s≤n) := And.intro (P.prepared_at n A V q) (P.prepared_color n A V)
    have ht := t.admission
    refine ⟨t,fun _ _ a b=>t.spacing P x D a b,fun u v g h=> ?_,fun A U _=> hp A U,fun y=> Prod.ext (PaidOne P x B _ _ ht.unitF J).1 (PaidOne P x D _ _ ht.unitG J).2,⟨seam_income P x B D F V J ht,real_unpad ..⟩,fun t=> actors_prices ..,?_⟩
    · simpa using (t.spacing P x D (site_in P B F _ g) (site_in P D V _ h)).2
    intro n a g; have u:=(P.thin_comparator_LocalFieldBounds x n).1
    rw [u.factors _ _ a g,u.link _ a,u.matter _ g];rfl
#print axioms ribbons
end Spine.NativeSeam
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
