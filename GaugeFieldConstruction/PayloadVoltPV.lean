import GaugeFieldConstruction.MarginSpeΛ
import GaugeFieldConstruction.TiedVoltPV
import GaugeFieldConstruction.PlenSpeΛ
import GaugeFieldConstruction.CosmosSpeΛ
import GaugeFieldConstruction.OrchardFastYL

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
variable (a:Axis)
open NSF.Table.Pairing
open Set
variable {m:ℕ}(Y:SunlitL Cw R G)(sH:SurfCheckL G)
variable (A:PatMars a n)(B:PatMars a m)(F:Fin n→ΧiMars)(F₁:Fin m→ΧiMars)
abbrev ΦTapePV {n:ℕ}(A:Fin n→ΧiMars)(x:Points n):= G n x A
noncomputable def stitchπPV (x:Points n): (Cw a).DegreeHab:= if z:x∈SimArchMars a n then EmergePeakPV Cw R a F ⟨x,z⟩ else 0
noncomputable def ImposePV (x:Points n): (Cw a).DegreeHab:= (A.test x:ℂ) • stitchπPV Cw R a F x
include Y sH
lemma EraOfPV :ContinuousOn (stitchπPV Cw R a F) (SimArchMars a n):= continuousOn_iff_continuous_restrict.mpr (by
 rw [show (SimArchMars a n).restrict (stitchπPV Cw R a F)= EmergePeakPV Cw R a F from funext (fun x=> (by change stitchπPV Cw R a F x.val=_; unfold stitchπPV; rw[dif_pos x.property]))]; exact (turnsPeakPV Cw R G a F Y sH).1)
omit Y sH in
lemma FrameOfPV : support (ImposePV Cw R a A F)⊆ tsupport A.test:=by intro x hx; apply subset_closure; intro e; change A.test x=0 at e; exact hx (by unfold ImposePV; rw [e,zero_smul])
lemma StageOfPV : Continuous (ImposePV Cw R a A F):=by
 apply continuous_iff_continuousAt.mpr; intro x; by_cases z:x∈SimArchMars a n
 · exact A.test.continuous.continuousAt.smul ((EraOfPV Cw R G a Y sH F x z).continuousAt ((openArchMars _ _).mem_nhds z))
 have ht:x∉tsupport A.test:= fun i=>z (A.east i); exact continuousAt_const.congr (((isClosed_tsupport _).isOpen_compl.eventually_mem ht).mono fun i p=>  Eq.symm (show ImposePV Cw R a A F i=0 from not_not.mp (fun y=>p (FrameOfPV Cw R a A F y)))) -- maybe orientation
lemma DescentPV: Integrable (ImposePV Cw R a A F) := (StageOfPV Cw R G a Y sH A F).integrable_of_hasCompactSupport (A.test.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _) (closure_minimal (FrameOfPV Cw R a A F) (isClosed_tsupport _))) -- tune
omit Y sH in
noncomputable def PolePulsePV:(Cw a).DegreeHab:= ∫ x,ImposePV Cw R a A F x
lemma PolePropPV (x:Points n)(y:Points m): inner ℂ (ImposePV Cw R a A F x) (ImposePV Cw R a B F₁ y)=(PatentMars A B) (closedUp a x y)*ΦTapePV G (Fin.append (TurnupMars a ∘ F) F₁) (closedUp a x y) :=by
 rw [PatchHMars]; by_cases hx:x∈tsupport A.test; swap
 · rw [show ImposePV Cw R a A F x=0 from notMem_support.mp (fun u=> hx (FrameOfPV Cw R a A F u)), image_eq_zero_of_notMem_tsupport hx]; simp
 by_cases hy:y∈tsupport B.test; swap
 · rw [show ImposePV Cw R a B F₁ y=0 from notMem_support.mp (fun u=> hy (FrameOfPV Cw R a B F₁ u)), image_eq_zero_of_notMem_tsupport hy]; simp
 unfold ImposePV stitchπPV; rw [dif_pos (A.east hx),dif_pos (B.east hy), inner_smul_left,inner_smul_right, CurrencyPairPV Cw R G a Y sH, mul_assoc]; rfl
lemma PulsePropPV : inner ℂ (PolePulsePV Cw R a A F) (PolePulsePV Cw R a B F₁)=(PatentMars A B).applyTo (ΦTapePV G (Fin.append (TurnupMars a ∘ F) F₁)):=by
 let f:= ImposePV Cw R a A F; let g:= ImposePV Cw R a B F₁; let y:=PolePulsePV Cw R a B F₁; let Q:=PatentMars A B; let S:=ΦTapePV G (Fin.append (TurnupMars a ∘ F) F₁); let pIso:=pairIso (n:=n) (m:=m) a
 let V(q:Points n× Points m):= inner ℂ (f q.1) (g q.2)
 have he(x:Points (n+m)): V (pIso x)=Q x*S x:=by have h:= PolePropPV Cw R G a Y sH A B F F₁ (pIso x).1 (pIso x).2; exact show _ from (by rwa [show closedUp a (pIso x).1 (pIso x).2=x from pIso.symm_apply_apply x] at h)
 have hv:Integrable V:= ((volume_split (n:=n) (m:=m) a).integrable_comp_emb pIso.toHomeomorph.measurableEmbedding).mp ((Q.smearing (sH.sm _).continuousOn).congr (Eventually.of_forall fun i=> (he i).symm))
 change inner ℂ (∫ x,f x) y= Q.applyTo S
 rw [show Q.applyTo S=∫ x,V x from ?_, MeasureTheory.Measure.volume_eq_prod, integral_prod V hv]; swap
 · rw [←MeasurePreserving.integral_comp (volume_split _ (n:=n) (m:=m)) pIso.toHomeomorph.measurableEmbedding V]; exact integral_congr_ae (Eventually.of_forall fun i=> (he i).symm)
 have ht(x:Points n):(∫ w:Points m,V (x,w))=inner ℂ (f x) y:= integral_inner (DescentPV Cw R G a Y sH B F₁) (f x)
 simp_rw [ht]; rw [← inner_conj_symm _ y,← integral_inner (DescentPV Cw R G a Y sH A F),← integral_conj]; apply integral_congr_ae; exact Eventually.of_forall fun i=> inner_conj_symm .. -- tune y/f
#print axioms PulsePropPV
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
