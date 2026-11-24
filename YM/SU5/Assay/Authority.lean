import SatinFixedContrastNovember4
import YM.SU5.Assay.Gridded
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set
variable (P:Spine)(j i l:Axis)(x:P.Spectrum0 j)
/-! Use *the same vote*, whether or not the bills call `advocate`. No equivalence here
  of the time-dynamic Hilbert spaces across axes. The probes entering authority
  include ANY molds with the earlier Satin normalization, also at the old fixed
  widths; any refinements use precisely those pose and wall currencies. -/
private lemma plane_triangle (v:P.vacuum j): P.planeChoice i l (P.planeChoice j i v)=P.planeChoice j l v:=by
 let g(j k):P.vacuum j→L[ℂ]P.vacuum k:=(P.planeChoice j k).toLinearIsometry.toContinuousLinearMap
 have e:(g i l).comp (g j i)=g j l:=P.extGroundOperator j _ _ fun t=> by
   change P.planeChoice i l (P.planeChoice j i _)=P.planeChoice j l _
   rw [flips_spaces,flips_spaces,flips_spaces]
 exact DFunLike.congr_fun e v
lemma migrate_triangle (z:P.Ensemble j): P.migrateHom i l (P.migrateHom j i z)=P.migrateHom j l z:=by
 apply Subtype.ext
 rw [migrant,migrant,migrant];ext1 v
 rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
   LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
 rw [plane_triangle,planeChoice_back,planeChoice_back,planeChoice_back,plane_triangle]
lemma advocate_triangle :P.advocate i (P.advocate j x i) l=P.advocate j x l:=by
 ext b
 change P.chi l (P.otherSpectrum i l (P.otherSpectrum j i x)) b=P.chi l (P.otherSpectrum j l x) b
 rw [P.translates,P.translates,P.translates,P.migrate_triangle]
lemma advocate_noop:P.advocate j x j=x:= (P.advocate_triangle j j j x).symm.trans (P.advocate_roundtrip j x j)

abbrev spiritOne (P:Spine)(r:P.Register)(x:P.Spectrum0 3)(t:ℕ)(A:P.Apron)(F:SampleDose):=
 P.spirits r 3 x (P.paintPoly A t F.val)
abbrev spiritBoth (P:Spine)(r:P.Register)(x:P.Spectrum0 3)(t:ℕ)(A:P.Apron)(F:SampleDose)(D:P.Apron)(G:SampleDose):=
 P.spirits r 3 x (P.paintPair A D t F.val G.val)
section
variable (r:P.Register)(x₃:P.Spectrum0 3)(t:ℕ)(A D:P.Apron)(F G:SampleDose)
local notation "μ"=>P.singleState 3 t x₃
local notation "a"=>P.prepared t A F
local notation "b"=>P.prepared t D G
lemma spirit_single : P.spiritOne r x₃ t A F=μ a:=by
 rw [reviewWardPaint]; exact P.oneCup ..
lemma spirit_both_mark: P.markPair A D t F.val G.val=a*b:=by
 rw [reviewWardPaint,reviewWardPaint]; rfl
lemma spirit_pair: P.spiritBoth r x₃ t A F D G=μ (a*b):=by
 unfold spiritBoth; rw [paintPair_here,P.spirit_both_mark]
lemma spirit_single_normalization (h:A.s≤t):
 P.spiritOne r x₃ t A F= ((P.macroStep t)^4*(∑ᶠ q:Cover,F.val (P.meshPose t q)):ℝ) • P.singleState 3 A.s x₃ A.F:=
 P.paint_set r A t F.val x₃ F.budget h
end
-- Mean computation, regulator formula in Elected. A further selection
-- is needed before paying these spirit readings, not buying them just by
-- taking cutoff limits on each stencil alone.
lemma reading_mean (s:ℕ)(f:P.Test):
 (∫ z, P.singleState 3 s z f ∂P.pillars 3)=P.E s f.val:= (P.recovery 3 (P.reading 3 s f)).trans (P.occupied ..)
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
