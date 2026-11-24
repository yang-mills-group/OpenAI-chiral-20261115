import GaugeFieldConstruction.HarvestJointNX
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
-- actual Coalition: one spine/view/archive, one registration, one path, and APPROVED solicitation of orientation frame and dynamics. Predicate open Badge to allow further needs while preserving same purchases.
open RosterJ BoonsθJ SignetS Patrons ChSigFe
open CF.XGarden.MastTin.ArtCart
open SpaΘ
open Fock.Flux
open Papal
open Yoke SelectionAnalysis
open Oath.BellPrice
open GaugeFieldConstruction.Phys
open Fock
open GaugeFieldConstruction
open Fathom Ember
open Calibration.Floor Calibration -- tune

open Ember.Volumetric Ember.Volumetric.FirstPackMars Mavera
open Shower
open Calibration Calibration.Floor
-- main underwriting record.VU. all data generated. abstract REALIZED with a.e qualifications, specifying one spectrum. unproblematic along P path
variable {P:Spine}{R:Signed × Bool}{C:Clip→ℝ}{O:PinRack→Badge}{r:TintDemand}{N:ℕ}
variable {d:YardμN P C O r N}{J:InterR}{α:finsJ}{m:ℕ}(E:ConsoleθN d R α J m)
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
open YM.GaugeFieldConstruction.Wick.Yacht YM.GaugeFieldConstruction.Wick YM.GaugeFieldConstruction.Cauchy
open SelectionAnalysis
open CF.Levier CF.Spire
open Fathom Ember Hulse Points Fathom.Salam Fathom.Palace
-- valuations explicit Universe-safe.
namespace ConsoleθN
variable {X:Axis→GaugeFieldConstruction.Empire.Across}{Y: Sheds E.Crew_N X}{W:Supplies Y}
variable (p: Ticket E.Gamma_N W) (v:P.Spectrum0 3) (q:UpShift_S ≤ m)
-- one educator, constant Cone fields, signature obligations
variable (hp:E.SignVU p v)(qx:E.PathVU p v)
variable {Z:NSF.Boundary.Waves (E.RadianceVU p)}{L:NSF.Boundary.Surface (E.RadianceVU p)}{B:NSF.Boundary.Surface.Aurora L NSF.LD.drapeL}
variable (D:E.GlowVU p v q Z L) (wX:E.HonorsVU p v q Z L B D)
open NSF.Boundary NSF.Work.C20
open Invoice.curvΝ
open YM.Boundary (Test4 Joint)
variable (X G:DegreeViewNX→ΧiMars) -- H.GT
variable (s t:SampleDose)
open Glaze
variable(a:Axis)(ιs:ℕ)
variable (hJ:E.LeaseVU ιs)(T:E.ArtWordNX p v q (L:=L) a ιs)
variable (J₀:P.Ellis 3 v) {I:Type}[Fintype I][DecidableEq I] (K:Set (SpaceN I))(k:IsCompact K)(A:I→P.Apron)(Q:List I)
abbrev CommonWindNX (g:SpaceN I→ℂ)(x:SpaceN I):ℂ:= g x* P.commonWell 3 v A (VantageN x) Q
include k J₀
lemma CommonPriceNX(f:SpaceN I→ℂ)(p:Function.support f ⊆ K)(a:Continuous f)(h: ∀ x∈K,∀ i:Axis,P.Turnstile i A Q (VantageN x)): Tendsto (fun s:ℕ=> P.singleState 3 s v (NativeCostN (fun i=> (A i).full P) Q K k f s)) atTop (𝓝 (∫ x:SpaceN I, CommonWindNX v A Q f x)):=by
   let β:=CommonWindNX v A Q f; have hp: Function.support β⊆K:=Set.Subset.trans (support_mul_subset_left ..) p
   have hz: Continuous β:=by
       apply continuous_iff_continuousAt.mpr; intro x
       by_cases p:x∈K
       · exact a.continuousAt.mul ((P.common_cont 3 v A _ Q J₀ ⟨3,Q,List.Perm.refl _,h x p 3⟩).comp FormalV_N.continuousAt)
       exact (continuousAt_const (x:=x) (y:=(0:ℂ))).congr ((k.isClosed.isOpen_compl.eventually_mem p).mono (fun y v=> Eq.symm (Classical.byContradiction fun (z:β y≠0)=>v (hp z))))
   apply (HarvestᵥN P K k β hz hp).congr'; filter_upwards [eventually_all.mpr fun i=>eventually_ge_atTop (A i).s] with s v'
   unfold NativeCostN; rw [map_sum]; symm; apply sum_congr rfl; intro i z
   let p:= MacroGrid.atTick (P.macroStep s) i; have p':p∈K:=(dustN _ _ _ _ _).1 z
   let y:= TownN i; have hg:P.gridSpot s ∘ y= VantageN p:=TownPoseN ..
   let X:=P.singleState 3 s v
   have hu(j:Axis):P.Turnstile j A Q (P.gridSpot s ∘ y):= hg ▸ h p p' j
   have he:=P.spot_full v A Q y J₀ s (fun i _=>v' i) (hu 3) ⟨fun i=>⟨Q,List.Perm.refl Q,hu i⟩⟩
   rw[hg] at he; rw [map_smul]; change (_:ℂ) • X (P.fullScroll s A y Q)= _; rw [show X _ = P.commonWell 3 v A (VantageN p) Q from he]; unfold CustsN β CommonWindNX; exact smul_mul_assoc _ _ _
omit k
abbrev CommonPose1NX(K:SampleDose)(A:P.Apron):ℂ:= ∫ x: SpaceN (Fin 1), CommonWindNX v (![A]) jNOne (Terra1N K) x
abbrev CommonPose2NX (K L:SampleDose)(A B:P.Apron):ℂ:= ∫ x:SpaceN (Fin 2),CommonWindNX v (![A,B]) jNDuo (Terra2N K L) x
lemma CommonServe1NX(A:P.Apron)(K:SampleDose): Tendsto (fun t=> P.singleState 3 t v (P.prepared t A K)) atTop (𝓝 (CommonPose1NX v K A)):=by
   change Tendsto (fun t=>P.singleState 3 t v (installedN (A.full P) K t)) atTop _; simp_rw [←moneyL1N]; rw [show (![A.full P]: Fin 1→ℕ→P.Test)= fun i=> ((![A]: Fin 1→P.Apron) i).full P from funext fun i=>by fin_cases i; rfl]
   exact CommonPriceNX v J₀ _ _ _ _ _ (levyT1N K) (αKΤ1N K) (fun _ _ _=> List.pairwise_singleton ..)
lemma CommonServe2NX(A B:P.Apron)(K L:SampleDose)(a:ℝ)(hA:∀ i,A.realWidth P i<a)(hB:∀ i,B.realWidth P i<a)(h:BundlesΝ (tsupport K.val) (tsupport L.val) (2*a)) : Tendsto (fun t=> P.singleState 3 t v (P.prepared t A K * P.prepared t B L)) atTop (𝓝 (CommonPose2NX v K L A B)):=by
   change Tendsto (fun t=>P.singleState 3 t v (installedN (A.full P) K t*installedN (B.full P) L t)) atTop _; simp_rw[←moneyL2N]; rw [show (![A.full P,B.full P]:Fin 2→ℕ→P.Test)=fun i=> ((![A,B]: Fin 2→P.Apron) i).full P from funext fun i=>by fin_cases i<;>rfl]
   refine CommonPriceNX v J₀ _ _ _ _ _ (levyT2N K L) (αKΤ2N K L) ?_; intro x p i; let u:= VantageN x 0; let z:=VantageN x 1; change ([0,1]:List (Fin 2)).Pairwise _; simp; change u i+A.realWidth P i < z i-B.realWidth P i; linarith only [hA i,hB i, (h u p.1 z p.2 i)]
#print axioms CommonServe2NX
end ConsoleθN
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
