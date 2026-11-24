import GaugeFieldConstruction.CoinEndVU
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
open SignetS Patrons ChSigFe
open YM.GaugeFieldConstruction YM.GaugeFieldConstruction.Ember YM.GaugeFieldConstruction.Ember.Volumetric FirstPackMars Stage Calibration Phys Calibration.Floor
open NSF.Table.Pairing
open YM.Boundary (Test4 Joint)
open MacroGrid
open scoped ContDiff
variable (r s:SampleDose)
variable {n:ℕ}(G:Fin n→SampleDose)
lemma BrandNestVU {T:Points n→ℂ}{U:Set (Points n)}(u:IsOpen U)(h:ContinuousOn T U)(s':tsupport ⇑(ConjoinVU n G)⊆ U): Integrable (fun x=> T x * ConjoinVU n G x):=by
 let L:= (ConjoinVU n G)
 refine Continuous.integrable_of_hasCompactSupport (continuous_iff_continuousAt.mpr (fun i=>?_)) (compactCoinVU _|>.mul_left)
 by_cases v:i∈tsupport ⇑L; · exact (h.continuousAt (u.mem_nhds (s' v))).mul L.continuous.continuousAt
 apply (continuousAt_const (x:=i) (y:=0)).congr; filter_upwards[(isClosed_tsupport ⇑L).isOpen_compl.mem_nhds v] with x k; exact Eq.symm ((congrArg (fun y=> T x*y) (image_eq_zero_of_notMem_tsupport k)).trans (mul_zero _)) -- tune
lemma PureNestVU (H:∀ i,(G i).Normalized): (∫ x:Points n,‖ConjoinVU n G x‖)=1:=by
 have h:= firesVU G H
 have he:∀ i:Points n, (ConjoinVU n G i)= (↑‖ConjoinVU n G i‖:ℂ):=by
    intro i
    have h:=congrFun (funcHeightVU n G).symm i
    rw [h]; change ((∏ j, (G j).val (i j).ofLp:ℝ):ℂ)=↑‖((∏ j, (G j).val (i j).ofLp:ℝ):ℂ)‖; rw[Complex.norm_real,Real.norm_of_nonneg (Finset.prod_nonneg (fun j _=>(H j).1 _))] -- tune
 exact Complex.ofReal_injective (integral_complex_ofReal.symm.trans ((integral_congr_ae (Eventually.of_forall fun i=> (he i).symm)).trans (h.trans Complex.ofReal_one.symm)))
lemma SipsNestVU (H:∀ i,(G i).Normalized){T: Points n→ℂ}(p: Integrable (fun x=> T x*ConjoinVU n G x))(b:ℂ)(ε:ℝ)(t:∀ x∈tsupport ⇑(ConjoinVU n G),‖T x-b‖ ≤ ε) : ‖(∫ x,T x*ConjoinVU n G x)- b‖≤ ε:=by
 let W:= ConjoinVU n G; let S(x):ℂ:= T x*W x; let A(x:Points n):ℂ:=b*W x
 have hp:Integrable (⇑W):= W.continuous.integrable_of_hasCompactSupport (compactCoinVU _)
 have hv:Integrable A:= hp.const_mul _
 have ht:(∫ x,A x)=b:= (integral_const_mul ..).trans (by rw[show (∫ y:Points n,W y)=1 from firesVU G H,mul_one])
 have hz:= p.sub hv -- fine
 change ‖(∫ x,S x)- b‖≤ ε
 have hq:(∫ x:Points n, (S-A) x)=(∫ x,S x)-b:= (integral_sub' (show Integrable S from p) hv).trans (congrArg ((∫ x,S x) - ·) ht); rw [← hq]
 refine ((norm_integral_le_integral_norm ..).trans (integral_mono hz.norm (hp.norm.const_mul ε) ?_)).trans (le_of_eq ((integral_const_mul ..).trans ?_)) -- tune
 · intro i; change ‖T i*W i- b*W i‖≤ ε *‖W i‖; rw [← _root_.sub_mul,norm_mul]; by_cases v:W i=0; · simp[v]
   exact mul_le_mul_of_nonneg_right (t i (subset_closure v)) (norm_nonneg _)
 rw [PureNestVU G H,mul_one] -- unfold W
abbrev courseDoseVU (x:Points n)(i:ℕ)(j:Fin n):= SelectDoseN (x j).ofLp i
noncomputable abbrev foldIntoVU (x:DiagramR (Fin n)):Points n:= (ExpositionVU n).symm (EarthedN x)
lemma NestGatherVU(x:Points n)(U:Set (Points n))(h: U∈ 𝓝 x): ∀ᶠ i in atTop, SponVU n (courseDoseVU x i)⊆ U:=by
 let X:=ΦplanR n x; let K:=foldIntoVU (n:=n)
 have hc:Continuous K:= (ExpositionVU n).symm.continuous.comp (continuous_pi fun x=> by unfold EarthedN; fun_prop)
 have hz(i:Points n):K (ΦplanR n i)= i:= (ExpositionVU n).symm_apply_apply _
 obtain ⟨v,e,g⟩:= Metric.mem_nhds_iff.mp (hc.continuousAt.tendsto (show U∈ 𝓝 (K X) from (hz x).symm ▸ h))
 filter_upwards [eventually_all.mpr fun i:Fin n=> DoseTravel.concentrates (X i) _ (ball_mem_nhds _ e)] with p h y t; rw [← hz y]; apply g; apply (dist_pi_lt_iff e).2; exact fun i=> h i (t i)
lemma nestTunnelVU (x:Points n){A:Points n→ℂ}(U:Set (Points n))(u:IsOpen U)(h:x∈U)(e:ContinuousOn A U): Tendsto (fun i=> ∫ y:Points n, A y*ConjoinVU n (courseDoseVU x i) y) atTop (𝓝 (A (x))):=by
 apply Metric.tendsto_nhds.mpr; intro ε p
 let W:=Metric.ball (A (x)) (ε/2)
 have hV:= e.continuousAt (u.mem_nhds h)
 have hz:A⁻¹' W∈ 𝓝 (x):= hV.tendsto (Metric.ball_mem_nhds _ (half_pos p))
 filter_upwards [NestGatherVU x U (u.mem_nhds h), NestGatherVU x _ hz] with i g v
 rw [dist_eq_norm]; apply lt_of_le_of_lt _ (half_lt_self p); exact SipsNestVU _ (fun _=>DoseTravel.prescribed ..) (BrandNestVU _ u e ((cardCoinVU n _).trans g)) _ _ (fun y t=> (lt_of_eq_of_lt (dist_eq_norm .. |>.symm) (show dist (A y) (A x)<ε/2 from v (cardCoinVU _ _ t))).le)
#print axioms nestTunnelVU
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end

