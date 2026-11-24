import GaugeFieldConstruction.ZitherAtlasYL
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxSize 28000
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
namespace Spine
open Aria Casting Six
open CF.Velvet CF.Pannier.Chancel Pitching.Focus
open YM.CF.Oath.BellPrice CF.Fief
open Oath
open Papal AUbard
open Papal FrameP Yoke.Promena WorldJ Frugal CF.Scroll MirrorCost
open Py Yoke.Promena
open CF.Neon CF.XGarden CF.XGarden.MastTin CF.XGarden.MastTin.ArtCart
open CF.TableF CF.TableF.Lenten CF.XGarden CF.XGarden.Shield
open WorldJ
open scoped YM.CF.Mew
open Pitching.Focus.CoeffArc TableF TableF.Lenten TableF.Lenten.Layout TableF.Lenten.Layout.Fren
open Ing Ing.Ivey CF.XGarden.MastTin
open CF.Pastry CF.Hive
open CF.Scroll
namespace RosterJ
namespace BoonsθJ
open JetCurry JetCurry.TrekJ ProbeθJ Yoke SelectionAnalysis
open Repertoire 
variable {P:Spine}
namespace Shower
open SignetS
variable {cost:ℕ→P.Test→ℂ} {j: Axis}(C:Porch P cost j)
open YM.GaugeFieldConstruction YM.GaugeFieldConstruction.Ember YM.GaugeFieldConstruction.Ember.Volumetric FirstPackMars Stage Calibration Phys Calibration.Floor
open NSF.Table.Pairing
attribute [local instance] Ember.iG Ember.iF Ember.iX Ember.iU Ember.iT2 Ember.iW2 Ember.iV Ember.iS
variable {n:ℕ}{S: City} {P0:Axis→Empire.Across} {L:Sheds S P0} {Cu: Supplies L} {u:ℕ→Carat}
-- axis carried thru. CPI covariance proper. Suit has ALL axes declared, no H3 tilt for phase yet
variable (Cw:∀ j:Axis,Porch P cost j)
variable (R:ΧiMars →ₗ[ℂ]ScreensJ P) (G:CloudsL) (t:Ticket u Cu)
open NSF.Boundary NSF.OS.Semigroup -- no OS namespace clash
open NSF.LD
-- (137)-->(138) variant: projection joint on actual POS. norm displacement criterion; everything commutes on same Hil. use E2 costs, no invocation of L1 for chosen x until after L3!
variable (a:Axis)(p: Points n)(v:eastL n a p)(F:Fin n→ ΧiMars)(J:StallLeadMars a p P)
variable (χ:P.Spectrum0 3)(U:CheckΩL R)
open Set Complex
variable (J0: SunlitL P.publicH R G)(f: SurfCheckL.boisterL t G)
variable (E:∀ᵐ x∂P.pillars 3,P.lodestar 3 x) (Z:∀ᵐ x∂P.pillars 3, CriteriaL (P.privateH x) R)
open PlaneL
open MeasureTheory.Measure -- tune hides many
variable {m:ℕ}
section Harbor
variable {X:Type*}[MetricSpace X][MeasurableSpace X][BorelSpace X] [CompactSpace X]
variable (ν:Measure X)[IsFiniteMeasure ν]
variable (A:X→Points n)(w:X→ℂ)(W:Continuous w)(D:Continuous A)(e:∀ x,A x∈conf n)
noncomputable def AtlasOpYL:ChartOpYL:= fun C=>∫ x,w x*C _ F (A x)∂ν
noncomputable abbrev StarBoardYL (χ:P.Spectrum0 3)(x:X):= w x*shineYL R t U χ F (A x) -- param order macro
include W D e U
lemma CapsRateYL : ∃ k:ℝ,0≤k ∧∀ χ:P.Spectrum0 3,PureXYL R t χ→∀ x,‖w x*shineYL R t U χ F (A x)‖≤k:=by
 obtain ⟨k,h⟩:=CrownU_YL R t F U (Set.range A) (isCompact_range D) (Set.range_subset_iff.mpr e)
 obtain ⟨a,v⟩:= (isCompact_range W.norm).bddAbove; let K:=k⊔0; let Z:=a⊔0
 exact ⟨Z*K,mul_nonneg le_sup_right le_sup_right,fun χ p x=> (norm_mul_le ..).trans (mul_le_mul ((v (Set.mem_range_self x)).trans le_sup_left) ((h (A x) (Set.mem_range_self x) χ p).trans le_sup_left) (norm_nonneg _) le_sup_right)⟩ -- tune Set mem
lemma regHalfYL (v:PureXYL R t χ): Continuous (fun x=>w x*shineYL R t U χ F (A x)):= W.mul (continuous_iff_continuousAt.mpr fun x=> (TessLightL (P.privateH χ) R t _ F U v (e x)).tendsto.comp (D.tendsto x))
include f J0 E Z
lemma LedgerEarnYL: CappedYL (ν.prod (P.pillars 3)) (fun q:X× P.Spectrum0 3=> w q.1*shineYL R t U q.2 F (A q.1)) :=by
 let Y:= P.Spectrum0 3; let Q(x:X)(χ:Y):= w x*shineYL R t U χ F (A x); have he:= PureAllL R G t U J0 f E Z
 obtain ⟨k,K,h⟩:= CapsRateYL R t F U A w W D e
 let T:Set Y:={χ| PureXYL R t χ}; have hp: (P.pillars 3) Tᶜ=0:= he
 obtain ⟨J,L,ht,j⟩:= exists_measurable_superset_of_null hp
 let C (x:X):= Jᶜ.indicator (Q x)
 have hu: AEStronglyMeasurable (Function.uncurry C) (ν.prod (P.pillars 3)):=by
    apply StronglyMeasurable.aestronglyMeasurable; refine stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable (fun x=>?_) (fun i=> (stronglyMeasurable_const.mul (TessCarbonL R t _ F U (e i)) |>.indicator ht.compl))
    by_cases h:x∈ Jᶜ
    · simpa only [C,indicator_of_mem h,Q] using regHalfYL R t F (χ:=x) U A w W D e (show PureXYL R t x from by by_contra t; exact h (L t)) -- tune subset
    simp only [C,indicator_of_notMem h]; exact continuous_const
 have hg:∀ᵐ x∂ν.prod (P.pillars 3),x.2∈Jᶜ:= quasiMeasurePreserving_snd.tendsto_ae.eventually (show Jᶜ∈ae (P.pillars 3) from by rw[mem_ae_iff,compl_compl]; exact j) -- tune
 refine cashCoreYL ?_ k ?_ -- syntax
 exact hu.congr (hg.mono fun q h=> indicator_of_mem h _)
 filter_upwards [quasiMeasurePreserving_snd.tendsto_ae.eventually he] with q e using h q.2 e q.1
lemma RateZeroYL : CappedYL (P.pillars 3) (fun χ:P.Spectrum0 3=>AtlasOpYL F ν A w (fun n F x=> shineYL R t U χ F x)) :=by -- tune fun parser
 have he:= LedgerEarnYL R G t F U J0 f E Z ν A w W D e; obtain ⟨k,h,v⟩:=CapsRateYL R t F U A w W D e; exact cashCoreYL (cashI_YL he).integral_prod_right.aestronglyMeasurable _ ((PureAllL R G t U J0 f E Z).mono fun χ d=> norm_integral_le_of_norm_le_const (Eventually.of_forall (v χ d)))
lemma RateTestYL (d:P.Spectrum0 3→ℂ)(r:CappedYL (P.pillars 3) d): AtlasOpYL F ν A w (CensusYL R t U d) = ∫ χ,AtlasOpYL F ν A w (fun n F x=> shineYL R t U χ F x)*d χ ∂ P.pillars 3:=by
 have he:= LedgerEarnYL R G t F U J0 f E Z ν A w W D e; let μ0:=P.pillars 3
 have hp: CappedYL (ν.prod μ0) (fun q:X×P.Spectrum0 3=>d q.2):=by obtain ⟨a,k,t,h⟩:=r; exact cashCoreYL (a.comp_quasiMeasurePreserving quasiMeasurePreserving_snd) _ (quasiMeasurePreserving_snd.tendsto_ae.eventually h)
 let T (x:X)(χ:P.Spectrum0 3):= w x*shineYL R t U χ F (A x)*d χ
 have hu: Integrable (Function.uncurry T) (ν.prod μ0):= cashI_YL (cashM_YL he hp)
 change (∫ x,w x* _ ∂ν)= ∫ χ,(∫ x,w x*shineYL R t U χ F (A x)∂ν)*d χ∂ μ0
 calc
    _ = ∫ x,(∫ χ,T x χ ∂μ0)∂ν:=by unfold CensusYL T; simp_rw [mul_assoc,integral_const_mul]; rfl -- tune pattern
    _ = ∫ χ,(∫ x,T x χ∂ν) ∂μ0:= integral_integral_swap hu
    _ = _:=by unfold T; simp_rw[integral_mul_const]
omit f J0 E Z U W D e
lemma gluesureYL (p: Points m)(z:E4): Continuous (fun i:Points n=> apartYL z i p):=by
 let f':Points n→ Fin (n+m) →E4:=fun i=>Fin.append i.ofLp (NSF.Points.across z p).ofLp
 refine (PiLp.continuous_toLp 2 _).comp (show Continuous f' from continuous_pi ?_)
 intro x; refine Fin.addCases ?_ ?_ x
 · intro i; simp only [f',Fin.append_left]; fun_prop
 intro j; simp only [f',Fin.append_right]; exact continuous_const
include U W D e f J0 E Z
lemma FleetCapYL (cG:∀ n (F:Fin n→ΧiMars),ContinuousOn (fun x=>G n x F) (conf n))(V:Fin m→ΧiMars)(y:Points m)(uy:y∈conf m): Tendsto (fun i:ℕ=>AtlasOpYL F ν A w (DistantC_YL G m V y i)) atTop (𝓝 (∫ χ, AtlasOpYL F ν A w (fun n F x=> shineYL R t U χ F x)* shineYL R t U χ V y∂ P.pillars 3)):=by
 let B(i:ℕ)(x:X):=apartYL (EarYL i) (A x) y
 let J(i:ℕ)(x:X):= w x* G _ (B i x) (Fin.append F V)
 let d(χ:P.Spectrum0 3):= shineYL R t U χ V y
 let T (x:X):= w x * CensusYL R t U d n F (A x) -- tune notation
 obtain ⟨k,e'⟩:= ParcelCapYL R G t F U J0 f E Z y V uy (Set.range A) (isCompact_range D) (Set.range_subset_iff.mpr e)
 have hz:∀ᶠ i in atTop, Continuous (J i):=e'.mono (fun i p=>W.mul (continuous_iff_continuousAt.mpr fun x=> ((((cG _ _) (B i x) (p _ (Set.mem_range_self _)).1).continuousAt ((conf_open _).mem_nhds ((p _ (Set.mem_range_self x)).1))).tendsto.comp (((gluesureYL y (EarYL i)).comp D).tendsto x)))) -- fill isopen, fix lemma ContinuousWithinAt to ContinuousAt
 have hw: Integrable (fun x:X=>‖w x‖*k) ν:= (W.norm.mul continuous_const).integrable_of_hasCompactSupport (by exact isClosed_tsupport .. |>.isCompact) -- tune
 rw [← RateTestYL R G t F U J0 f E Z ν A w W D e d (selectCapYL R G t V U J0 f E Z y uy)]
 refine tendsto_integral_filter_of_dominated_convergence _ (hz.mono fun i u=> u.aestronglyMeasurable) (e'.mono fun i p=> Eventually.of_forall fun x=> (norm_mul_le ..).trans (mul_le_mul_of_nonneg_left (p _ (Set.mem_range_self x)).2 (norm_nonneg (w x)))) hw (Eventually.of_forall fun x=> (tendsto_const_nhds (x:= w x)).mul (MeanStarYL R G t F U J0 f E Z (A x) y V (e x) uy)) -- may infer wrong function
lemma CharterAtlasYL (cG:∀ n (F:Fin n→ΧiMars),ContinuousOn (fun x=>G n x F) (conf n)): AtlasYL R G t U (AtlasOpYL F ν A w) :=⟨RateZeroYL R G t F U J0 f E Z ν A w W D e, RateTestYL R G t F U J0 f E Z ν A w W D e,fun _ v p h=> FleetCapYL R G t F U J0 f E Z ν A w W D e cG v p h,fun C p=>by unfold AtlasOpYL; simp_rw [show ∀ x:X,C n F (A x)=0 from fun x=>p _ _ (e x),mul_zero]; simp⟩
end Harbor
#print axioms CharterAtlasYL
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
