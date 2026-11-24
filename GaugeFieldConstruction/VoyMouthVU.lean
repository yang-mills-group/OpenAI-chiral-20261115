import GaugeFieldConstruction.CanyonPoseVU
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
-- dose on canonical coordinates on shell, spacetime sets literally same
noncomputable abbrev ΦPaperVU := PiLp.continuousLinearEquiv 2 ℝ (fun _:Axis=>ℝ)
noncomputable def paneLblVU (x:E4):ℂ:=(r.val (ΦPaperVU x):ℂ)
lemma nearMoneyVU:tsupport (paneLblVU r)=(WithLp.ofLp)⁻¹' tsupport r.val:=by
 change tsupport (Complex.ofReal ∘ (r.val ∘ ΦPaperVU.toHomeomorph)) = _
 rw [tsupport_comp_eq (fun {x}=>Complex.ofReal_eq_zero),tsupport_comp_eq_preimage]; rfl
lemma compactLblVU : HasCompactSupport (paneLblVU r):=by
 change IsCompact _; rw [nearMoneyVU]; exact ΦPaperVU.toHomeomorph.isCompact_preimage.mpr r.budget -- tune
lemma paneLblSmVU : ContDiff ℝ ∞ (paneLblVU r):=Complex.ofRealCLM.contDiff.comp (r.smooth.comp ΦPaperVU.contDiff) -- tune
noncomputable abbrev TagVU : Test4:= (compactLblVU r).toSchwartzMap (paneLblSmVU r)
lemma compactTagVU: HasCompactSupport ⇑(TagVU r):= compactLblVU r
@[simp] lemma moneyTagVU (x:E4):TagVU r x= (r.val x.ofLp:ℂ):= rfl
@[simp] lemma moneyExtentVU: tsupport ⇑(TagVU r)=(WithLp.ofLp) ⁻¹' tsupport r.val:= nearMoneyVU r
lemma unitTagVU (p:r.Normalized): (∫ x:E4,TagVU r x)=1:= ((PiLp.volume_preserving_ofLp Axis).integral_comp (ΦPaperVU.toHomeomorph.measurableEmbedding) (fun x=> (r.val x:ℂ))).trans ((integral_complex_ofReal).trans (p.2 ▸ Complex.ofReal_one)) -- tune
noncomputable abbrev ConjoinVU (n:ℕ)(G:Fin n→SampleDose) : Joint n:= YM.Boundary.Joint.materialize n (TagVU ∘ G)
noncomputable abbrev ζfuse (n:ℕ):= YM.Boundary.Joint.breakAt (n:=n)
lemma measureFuseVU(n:ℕ): MeasurePreserving (ζfuse n):= (WithLp.volume_preserving_ofLp _ _).comp (YM.Points.peel (n:=n)).measurePreserving
lemma craddleVU (n:ℕ)(X:Joint (n+1))(Q:Test4)(T: Joint n)(e:∀ i:Points (n+1), X i= Q (i 0) * T (YM.Points.tail i)): (∫ i:Points (n+1),X i)= (∫ i:E4,Q i)* ∫ i: Points n,T i:=by
 let F: E4 × Points n→ℂ:= fun p=> Q p.1 * T p.2
 exact (integral_congr_ae (Eventually.of_forall fun x=> show X x= F (ζfuse n x) from e x)).trans (((measureFuseVU n).integral_comp (ζfuse n).toHomeomorph.measurableEmbedding F).trans (integral_prod_mul _ _))
lemma firesVU {n:ℕ}(G:Fin n→SampleDose)(h:∀ i,(G i).Normalized): (∫ x:Points n,ConjoinVU n G x)=1 :=by
 induction n with
 | zero => rw [YM.Points.volume_nil, integral_dirac]; rfl
 | succ n ih =>
   rw [craddleVU n _ (TagVU (G 0)) (ConjoinVU n (Fin.tail G)) (fun _=>rfl), unitTagVU _ (h 0), ih (Fin.tail G) (fun i=> h i.succ), one_mul]
lemma supportCoinVU{n:ℕ}(G:Fin n→SampleDose)(x:Points n)(v:x∈ Function.support ⇑(ConjoinVU n G))(i:Fin n): (x i).ofLp∈tsupport (G i).val:=by
 apply subset_closure; by_contra f; have h:= mem_support.mp v; simp only [ConjoinVU,YM.Boundary.Joint.material_at] at h; exact h (Finset.prod_eq_zero (Finset.mem_univ i) (show TagVU _ _=0 from (by rw [moneyTagVU,notMem_support.mp f,Complex.ofReal_zero])))
lemma extentCoinVU {n:ℕ}(G:Fin n→SampleDose)(x:Points n)(v:x∈ tsupport ⇑(ConjoinVU n G))(i:Fin n): (x i).ofLp∈tsupport (G i).val:=by
 apply closure_minimal (s:= Function.support ⇑(ConjoinVU n G)) (t:=(fun x: Points n=> (x i).ofLp)⁻¹' tsupport (G i).val) ?_ ((isClosed_tsupport _).preimage ((PiLp.continuous_ofLp 2 _).comp (PiLp.continuous_apply 2 _ _))) v -- tune
 exact fun q h=> supportCoinVU G _ h i
lemma compactCoinVU {n:ℕ}(G: Fin n→SampleDose): HasCompactSupport ⇑(ConjoinVU n G):=by
 let M:Set (Fin n→E4):= Set.univ.pi (fun i=> tsupport ⇑(TagVU (G i)))
 have h:IsCompact M:=isCompact_univ_pi fun i=>compactTagVU _
 have v:= (PiLp.homeomorph 2 (fun _:Fin n=>E4)).isCompact_preimage.mpr h
 exact v.of_isClosed_subset (isClosed_tsupport _) fun x u i _=> by change x i ∈ tsupport ⇑(TagVU (G i)); rw [moneyExtentVU]; exact extentCoinVU G _ u i
noncomputable abbrev PairCoinVU:= ConjoinVU 2 ![r,s]
noncomputable abbrev MonoCoinVU (r:SampleDose):=ConjoinVU 1 ![r]
lemma moneyMonoVU(x:Points 1): MonoCoinVU r x=(r.val (x 0).ofLp:ℂ):=by simp[ConjoinVU,MonoCoinVU]; rfl
lemma moneyPairVU(x:Points 2): PairCoinVU r s x=((r.val (x 0).ofLp * s.val (x 1).ofLp:ℝ):ℂ):=by simp[ConjoinVU,PairCoinVU,Fin.prod_univ_two]; rfl
lemma heartyVU(x:Points 2): PortsVU (x 0).ofLp (x 1).ofLp=x:=by apply PiLp.ext; intro i; fin_cases i<;> rfl
-- Vantage semantics also on n-credit arities.
noncomputable abbrev ExpositionVU(n:ℕ): Points n ≃L[ℝ] SpaceN (Fin n):= (YM.Points.flatten (n:=n)).toContinuousLinearEquiv.trans (PiLp.continuousLinearEquiv 2 ℝ _)
lemma expositionMeasureVU(n:ℕ):MeasurePreserving (ExpositionVU n):= (PiLp.volume_preserving_ofLp _).comp (YM.Points.flatten (n:=n)).measurePreserving
#print axioms nearMoneyVU
#print axioms firesVU
#print axioms compactCoinVU
#print axioms expositionMeasureVU
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
