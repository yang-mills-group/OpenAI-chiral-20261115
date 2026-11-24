import GaugeFieldConstruction.MantaCrownYL
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
-- satisfaction operator via spectator-weight correlation. works for tasks with finite measure probes, sampled by bounded supports off diagonals. No limit op Hil needed to pass Ward.
variable {m:ℕ}
abbrev CostsYL := (n:ℕ)→(Fin n→ΧiMars)→Points n→ℂ
abbrev ChartOpYL:=CostsYL→ℂ
noncomputable def ΞYL (χ:P.Spectrum0 3):CostsYL:= fun _=> shineYL R t U χ -- arg tune
noncomputable def DistantC_YL(m:ℕ)(V:Fin m→ΧiMars)(y:Points m)(i:ℕ):CostsYL:= fun n F x=> G (n+m) (apartYL (EarYL i) x y) (Fin.append F V)
noncomputable def EmberYL (Q:ChartOpYL) (χ:P.Spectrum0 3):= Q (ΞYL R t U χ) -- tune Ξ section binder chi earlier
noncomputable def CensusYL (d:P.Spectrum0 3→ℂ):CostsYL:= fun n F y=> ∫ χ,shineYL R t U χ F y*d χ∂ P.pillars 3
abbrev CappedYL {X:Type*}[MeasurableSpace X] (μ:Measure X)(d:X→ℂ):Prop:= AEStronglyMeasurable d μ∧∃ k:ℝ,0≤k∧∀ᵐ x∂μ,‖d x‖≤k
variable {X:Type*}[MeasurableSpace X] {μ:Measure X}{v w:X→ℂ}
lemma cashCoreYL(A:AEStronglyMeasurable v μ)(k:ℝ)(h:∀ᵐ x∂μ,‖v x‖≤k): CappedYL μ v:=⟨A,(k⊔0),le_sup_right,h.mono fun _ t=> t.trans le_sup_left⟩
lemma cashA_YL (s:CappedYL μ v)(u:CappedYL μ w):CappedYL μ (fun x=> v x + w x) := by
 obtain ⟨A,k,h,v⟩:=s; obtain ⟨B,l,g,w⟩:=u; exact cashCoreYL (A.add B) _ ((v.and w).mono fun x z=> (norm_add_le ..).trans (add_le_add z.1 z.2))
lemma cashM_YL(s:CappedYL μ v)(u:CappedYL μ w):CappedYL μ (fun x=>v x*w x):=by
 obtain ⟨A,k,h,z⟩:=s; obtain ⟨B,l,g,y⟩:=u; exact cashCoreYL (A.mul B) _ ((z.and y).mono fun x z=> (norm_mul_le ..).trans (mul_le_mul z.1 z.2 (norm_nonneg _) h))
lemma cashI_YL [IsFiniteMeasure μ](s:CappedYL μ v): Integrable v μ:=by obtain ⟨a,k,t,h⟩:=s; exact (integrable_const k).mono' a h
lemma cashC_YL (μ:Measure X)(k:ℂ): CappedYL μ (fun _=>k):= cashCoreYL aestronglyMeasurable_const _ (Eventually.of_forall fun _=>le_rfl)
lemma cashS_YL (h:CappedYL μ v): CappedYL μ (Star.star ∘ v):=by
 obtain ⟨a,k,t,h⟩:=h; exact cashCoreYL (Complex.continuous_conj.comp_aestronglyMeasurable a) _ (h.mono fun x u=> (Complex.norm_conj ..).le.trans u)
lemma cash0_YL [IsFiniteMeasure μ](h:CappedYL μ v)(p:(∫ x,v x*Star.star (v x) ∂μ)=0): ∀ᵐ x∂μ,v x=0:=by
 have e(x:X):v x*Star.star (v x)= ((‖v x‖^2:ℝ):ℂ):=by rw[← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self, mul_comm]; rfl
 simp_rw[e,integral_complex_ofReal] at p
 obtain ⟨a,k,t,h⟩:=h; have hz: Integrable (fun x=> ‖v x‖^2) μ := (integrable_const (k^2)).mono' (a.norm.pow _) (h.mono (fun x p=>by rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]; exact pow_le_pow_left₀ (norm_nonneg _) p _))
 filter_upwards [(integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun x=>sq_nonneg _) hz).1 (by simpa using p)] with x v; change ‖_‖ ^ 2= (0:ℝ) at v; simpa using v
-- property related mean, fine on selection after. bind to Terra etc.
structure AtlasYL (Q:ChartOpYL):Prop where
 cap : CappedYL (P.pillars 3) (fun χ:P.Spectrum0 3=> Q (fun n F x=> shineYL R t U χ F x))
 credit : ∀ d:P.Spectrum0 3→ℂ,CappedYL (P.pillars 3) d → Q (CensusYL R t U d)= ∫ χ,Q (fun n F x=> shineYL R t U χ F x) * d χ∂P.pillars 3
 voyage : ∀ m (V:Fin m→ΧiMars) (y:Points m) (p:y∈conf m),Tendsto (fun i:ℕ=> Q (DistantC_YL G m V y i)) atTop (𝓝 (∫ χ,Q (fun n F x=> shineYL R t U χ F x)*shineYL R t U χ V y∂P.pillars 3))
 retract : ∀ C:CostsYL,(∀ n F,EqOn (C n F) (fun _=>0) (conf n))→ Q C=0
omit [MeasurableSpace X] -- likely illegal when already omitted? use not
include U E Z J0 f
lemma selectCapYL (p:Points n)(v:p∈conf n): CappedYL (P.pillars 3) (fun χ=>shineYL R t U χ F p):=by
 obtain ⟨k,h⟩:= closeCrownYL R t F U p v; exact cashCoreYL (TessCarbonL R t p F U v).aestronglyMeasurable _ ((PureAllL R G t U J0 f E Z).mono fun x h'=> mem_of_mem_nhds h x h')
lemma focusAtlasYL (h:p∈conf n): AtlasYL R G t U (fun X=> X n F p) :=⟨selectCapYL R G t F U J0 f E Z p h,fun _ _=> rfl,fun m V y u=> MeanStarYL R G t F U J0 f E Z p y V h u, fun V v=> v n F h⟩ -- tune
lemma blankAtlasYL : AtlasYL R G t U (fun _=>0):= ⟨cashC_YL ..,by simp,by simp,by simp⟩
lemma plusAtlasYL {Q T:ChartOpYL}(H:AtlasYL R G t U Q)(J:AtlasYL R G t U T): AtlasYL R G t U (fun W=>Q W+ T W):=by
 refine ⟨cashA_YL H.cap J.cap,?_,?_,fun C u=>by rw[H.retract _ u,J.retract _ u,zero_add]⟩
 · intro d p; rw [H.credit d p,J.credit d p]; simp_rw[add_mul,integral_add (cashI_YL (cashM_YL H.cap p)) (cashI_YL (cashM_YL J.cap p))]
 intro m V y p; have ht:=selectCapYL R G t V U J0 f E Z y p; simp_rw [add_mul,integral_add (cashI_YL (cashM_YL H.cap ht)) (cashI_YL (cashM_YL J.cap ht))]; exact (H.voyage m V y p).add (J.voyage m V y p)
omit J0 E Z f
lemma scalAtlasYL (c:ℂ){Q:ChartOpYL}(H:AtlasYL R G t U Q): AtlasYL R G t U (fun C=> c*Q C):=by
 refine ⟨cashM_YL (cashC_YL _ c) H.cap,fun d e=>?_,fun m V y p=>?_,fun C u=>by rw [H.retract C u,mul_zero]⟩
 · simp_rw [H.credit d e,mul_assoc,integral_const_mul]
 simp_rw [mul_assoc, integral_const_mul]; exact tendsto_const_nhds.mul (H.voyage m V y p)
include f J0 E Z
lemma fiatAtlasYL {I:Type}(s:Finset I)(X:I→ChartOpYL)(H:∀ i: I,AtlasYL R G t U (X i)): AtlasYL R G t U (fun C=> ∑ i∈ s,X i C):=by
 induction s using Finset.induction_on with
 | empty=> simpa using blankAtlasYL R G t U J0 f E Z
 | insert a l h ih=> simp_rw [Finset.sum_insert h]; exact plusAtlasYL R G t U J0 f E Z (H a) ih
omit f J0 E Z
open scoped ComplexConjugate
lemma TattooYL {Q:ChartOpYL}(H:AtlasYL R G t U Q)(v:∀ᵐ x∂P.pillars 3, PureXYL R t x)(u:∀ m (V:Fin m→ΧiMars)(y:Points m),y∈conf m → ∀ᶠ i in atTop,Q (DistantC_YL G m V y i)=0):∀ᵐ χ∂P.pillars 3,Q (fun n F x=> shineYL R t U χ F x)=0:=by
 let M(x:P.Spectrum0 3):= Q (fun n F y=>shineYL R t U x F y); let d:= Star.star ∘ M
 have he(m:ℕ)(V:Fin m→ΧiMars)(y:Points m)(p:y∈conf m):CensusYL R t U d m V y=0:=by
    let T':=TurnupMars timeAxis ∘ V; let p':=MirrorPoseL timeAxis y; have hp:p'∈conf m:=NSF.Points.move_in _ p
    have h : (∫ χ,M χ*shineYL R t U χ T' p'∂P.pillars 3)=0:= tendsto_nhds_unique_of_eventuallyEq (H.voyage m T' p' hp) tendsto_const_nhds (u m T' p' hp)
    have hy: ((fun χ:P.Spectrum0 3=> conj (M χ*shineYL R t U χ T' p')))=ᵐ[P.pillars 3] fun χ=> shineYL R t U χ V y*d χ:=by
       filter_upwards [v] with x u; rw [map_mul,show shineYL R t U x T' p'=Star.star _ from WorldNightL (P.privateH x) R t timeAxis y V U u p]; change _ * Star.star (Star.star _) = _; rw [star_star,mul_comm]; rfl
    unfold CensusYL; rw [←integral_congr_ae hy,integral_conj,h,map_zero]
 exact cash0_YL H.cap ((H.credit d (cashS_YL H.cap)).symm.trans (H.retract _ fun m V _=> he _ _ _))
#print axioms TattooYL
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
