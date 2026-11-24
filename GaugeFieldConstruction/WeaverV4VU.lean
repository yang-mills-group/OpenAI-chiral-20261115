import GaugeFieldConstruction.VoyMouthVU
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
lemma normalizedPairVU {r s:SampleDose}(p:r.Normalized)(v:s.Normalized):∫ x:Points 2,PairCoinVU r s x=1:= firesVU _ (fun i=>by fin_cases i; exact p; exact v)
lemma shelterPairVU (U:Set (Points 2))(p:∀ x∈tsupport r.val,∀ y∈tsupport s.val,PortsVU x y∈ U): tsupport ⇑(PairCoinVU r s)⊆ U:=fun i h=> heartyVU i ▸ p _ (extentCoinVU _ _ h 0) _ (extentCoinVU _ _ h 1)
lemma shelterΞVU (X Y:Vantage)(U:Set (Points 2))(h:U∈ 𝓝 (PortsVU X Y)) : ∀ᶠ i in atTop, tsupport ⇑(PairCoinVU (SelectDoseN X i) (SelectDoseN Y i))⊆ U:=by
 have H: ContinuousAt (fun p:Vantage×Vantage=> PortsVU p.1 p.2) (X,Y):= PortCΓvU.continuousAt
 have hv: (fun p:Vantage×Vantage=> PortsVU p.1 p.2)⁻¹' U ∈ 𝓝 (X,Y):= H.tendsto h
 filter_upwards [narrowT2N hv] with i k; exact shelterPairVU _ _ U (fun x g y t=>k (show (x,y)∈_ from ⟨g,t⟩)) -- tune
lemma BrandCostVU {T:Points 2→ℂ}{U:Set (Points 2)}(u:IsOpen U)(h:ContinuousOn T U)(s':tsupport ⇑(PairCoinVU r s)⊆ U): Integrable (fun x=> T x * PairCoinVU r s x):=by
 let L:= (PairCoinVU r s)
 refine Continuous.integrable_of_hasCompactSupport (continuous_iff_continuousAt.mpr (fun i=>?_)) (compactCoinVU _|>.mul_left)
 by_cases v:i∈tsupport ⇑L; · exact (h.continuousAt (u.mem_nhds (s' v))).mul L.continuous.continuousAt
 apply (continuousAt_const (x:=i) (y:=0)).congr; filter_upwards[(isClosed_tsupport ⇑L).isOpen_compl.mem_nhds v] with x k; exact Eq.symm ((congrArg (fun y=> T x*y) (image_eq_zero_of_notMem_tsupport k)).trans (mul_zero _)) -- tune
lemma PurePaperVU (u:r.Normalized)(v:s.Normalized): (∫ x:Points 2,‖PairCoinVU r s x‖)=1:=by
 have h:= normalizedPairVU u v
 have he:∀ i:Points 2, (PairCoinVU r s i)= (↑‖PairCoinVU r s i‖:ℂ):=by intro i; rw [moneyPairVU,Complex.norm_real,Real.norm_of_nonneg (mul_nonneg (u.1 _) (v.1 _))] -- tune
 exact Complex.ofReal_injective (integral_complex_ofReal.symm.trans ((integral_congr_ae (Eventually.of_forall fun i=> (he i).symm)).trans (h.trans Complex.ofReal_one.symm)))
lemma SipsVU (u:r.Normalized)(v:s.Normalized){T: Points 2→ℂ}(p: Integrable (fun x=> T x*PairCoinVU r s x))(b:ℂ)(ε:ℝ)(t:∀ x∈tsupport ⇑(PairCoinVU r s),‖T x-b‖ ≤ ε) : ‖(∫ x,T x*PairCoinVU r s x)- b‖≤ ε:=by
 let W:= PairCoinVU r s; let S(x):ℂ:= T x*W x; let A(x:Points 2):ℂ:=b*W x
 have hp:Integrable (⇑W):= W.continuous.integrable_of_hasCompactSupport (compactCoinVU _)
 have hv:Integrable A:= hp.const_mul _
 have ht:(∫ x,A x)=b:= (integral_const_mul ..).trans (by rw[show (∫ y:Points 2,W y)=1 from normalizedPairVU u v,mul_one])
 have hz:= p.sub hv -- fine
 change ‖(∫ x,S x)- b‖≤ ε
 have hq:(∫ x:Points 2, (S-A) x)=(∫ x,S x)-b:= (integral_sub' (show Integrable S from p) hv).trans (congrArg ((∫ x,S x) - ·) ht); rw [← hq]
 refine ((norm_integral_le_integral_norm ..).trans (integral_mono hz.norm (hp.norm.const_mul ε) ?_)).trans (le_of_eq ((integral_const_mul ..).trans ?_)) -- tune
 · intro i; change ‖T i*W i- b*W i‖≤ ε *‖W i‖; rw [← _root_.sub_mul,norm_mul]; by_cases v:W i=0; · simp[v]
   exact mul_le_mul_of_nonneg_right (t i (subset_closure v)) (norm_nonneg _)
 rw [PurePaperVU r s u v,mul_one] -- unfold W
lemma tunnelVUVU (X Y:Vantage){A:Points 2→ℂ}(U:Set (Points 2))(u:IsOpen U)(h:PortsVU X Y∈U)(e:ContinuousOn A U): Tendsto (fun i=> ∫ x:Points 2, A x*PairCoinVU (SelectDoseN X i) (SelectDoseN Y i) x) atTop (𝓝 (A (PortsVU X Y))):=by
 apply Metric.tendsto_nhds.mpr; intro ε p
 let W:=Metric.ball (A (PortsVU X Y)) (ε/2)
 have hV:= e.continuousAt (u.mem_nhds h)
 have hz:A⁻¹' W∈ 𝓝 (PortsVU X Y):= hV.tendsto (Metric.ball_mem_nhds _ (half_pos p))
 filter_upwards [shelterΞVU X Y U (u.mem_nhds h), shelterΞVU X Y _ hz] with i g v
 rw [dist_eq_norm]; apply lt_of_le_of_lt _ (half_lt_self p); exact SipsVU _ _ (DoseTravel.prescribed ..) (DoseTravel.prescribed ..) (BrandCostVU _ _ u e g) _ _ (fun x t=> (lt_of_eq_of_lt (dist_eq_norm .. |>.symm) (show dist (A x) (A (PortsVU X Y))<ε/2 from v t)).le)
#print axioms tunnelVUVU
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
