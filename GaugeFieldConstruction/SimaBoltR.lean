import GaugeFieldConstruction.PonzoR
import Mathlib.Analysis.Complex.Liouville
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
open OS.Semigroup
lemma RaateR (H:Hilbert)(j:Axis)(S:OS.Semigroup H j)(c d:ℝ≥0)(r:ℝ)(p:0<r)(h:2*r≤(c:ℝ))(s:2*r≤(d:ℝ)) : ‖S.E c - S.E d‖ ≤ r⁻¹* |(c:ℝ)-(d:ℝ)|:=by
 let K: Set ℂ:={x|2*r ≤ x.re}; let F:=S.F
 have κ:Convex ℝ K:= convex_halfSpace_ge Complex.reCLM.toLinearMap.isLinear _
 have v:2*r>0:=mul_pos (by norm_num) p
 have hz:duration c∈K:= h; have hy:duration d∈K:= s
 have e:S.F (duration c)=S.E c:=S.roots_heat (show 0<c from (v.trans_le h))
 have e': S.F (duration d)=S.E d:=S.roots_heat (show 0<d from (v.trans_le s))
 have hp: K ⊆ inside:=fun i q=> v.trans_le q
 have hc:= S.localHeat
 have h₀(x:ℂ)(a:x∈K): closedBall x r⊆ inside:=by
    intro i ie; have h': dist x i ≤ r:= (dist_comm _ _).le.trans ie; rw[dist_eq_norm] at h'; have hv:= (Complex.re_le_norm (x-i)).trans h'; rw[Complex.sub_re] at hv; change 2*r≤x.re at a; change 0 < i.re; linarith
 have hf(x:ℂ)(a:x∈ K): ‖deriv S.F x‖ ≤ r⁻¹:=by
    rw [←one_div]; exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le p ⟨fun i u=> ((hc i (h₀ x a (Metric.ball_subset_closedBall u))).differentiableAt).differentiableWithinAt, hc.continuousOn.mono ((closure_ball_subset_closedBall).trans (h₀ x a))⟩ (fun i q=> S.norm_row (h₀ x a (sphere_subset_closedBall q))) -- tune
 have hx:=κ.norm_image_sub_le_of_norm_deriv_le (fun i q=> (hc i (hp q)).differentiableAt) hf hy hz
 rw [e,e'] at hx
 rw [show ‖duration c-duration d‖=|(c:ℝ)-(d:ℝ)| from (by unfold duration; rw [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs])] at hx; exact hx
variable {I:Type}[Fintype I][DecidableEq I]{cost:ℕ→P.Test→ℂ} {j:Axis}(C:Porch P cost j)
local notation "ζ"=> C.BrightHab
local notation "Η" => C.DegreeHab
local notation "Ξ"=> C.ρ
local notation "η"=> C.groundHab
local notation "U" x:max=> (ζ).U x
local notation "Z" t:max=> (ζ).E t
lemma SpateT_R (x:Axis→ℝ) : ‖C.BrightHab.U (diameter x)‖ ≤ 1:=ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun i:Η=>by rw[(ζ).unitary,one_mul])
variable (σ:I→PermWallJ P)(A:I→P.Slabs j)
local notation "X"=> StageR σ C A
abbrev Strut_R (i:I)(x:Axis→ℝ) : C.DegreeHab.Op:=(C.BrightHab.U (diameter x))* (show C.DegreeHab.Op from rack (StageR σ C A) i)* C.BrightHab.U (diameter (-x))
lemma rackF_r (i:I) : ‖rack (StageR σ C A) i‖ ≤ ‖A i‖:=by
 refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun v:Η=> ?_)
 let Z':=(X).sky.track.aviator (X).sky.list; change ‖Z'.orthogonalProjectionOnto (C.ρ (A i) (v.val))‖ ≤ _
 exact (Submodule.norm_orthogonalProjectionOnto_apply_le _ _).trans (((Ξ (A i)).le_opNorm _).trans (mul_le_mul_of_nonneg_right (C.watch_le (A i)) (norm_nonneg _)))
lemma StrutF_R (i:I)(x:Axis→ℝ): ‖Strut_R C σ A i x‖≤ ‖A i‖:= (norm_pads_mul _ _ _ (SpateT_R C x) (SpateT_R C (-x))).trans (rackF_r C σ A i)
variable (x:I→Axis→ℝ) (i:I)(b:Option ℝ)(L:List I)
lemma gaitR : (show C.DegreeHab.Op from (X).gliding b i (x i))= (Z ((X).sep b i (x i)))*(Strut_R C σ A i (x i)) :=by unfold Repertoire.gliding Strut_R; simp only [mul_assoc]; rfl
lemma GlideAmtR(B:ℝ)(h:∀ i,‖A i‖≤ B)(w:C.DegreeHab): ‖(X).gliding b i (x i) w‖≤ B*‖w‖:=by
 change ‖(show C.DegreeHab.Op from (X).gliding b i (x i)) w‖≤ _; rw[gaitR C σ A x i b]; let Z':= (X).rack i; refine (ContinuousLinearMap.le_opNorm ..).trans ?_; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
 exact (norm_mul_le ..).trans ((mul_le_mul ((ζ).shrinks _) ((StrutF_R C σ A i (x i)).trans (h i)) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
lemma FleetAmtR (B:ℝ)(q:0≤B)(h:∀ i,‖A i‖≤ B): ‖(X).roadList L x b‖ ≤ B^L.length:=by
 induction L generalizing b with
 | nil=> change ‖η‖ ≤ B^0; rw [pow_zero]; exact C.normΩ.le
 | cons i w ih=>
    rw [List.length_cons,pow_succ,mul_comm,roadList]; apply (GlideAmtR C σ A x i b B h _).trans (mul_le_mul_of_nonneg_left (ih _) q)
lemma CensusAmtR (B:ℝ)(q:0≤B)(h:∀ i,‖A i‖≤ B) : ‖Repertoire.reading (StageR σ C A) L x‖ ≤ B^L.length:=by
 unfold Repertoire.reading; refine (norm_inner_le_norm ..).trans ?_; rw[show ‖(X).origin‖= 1 from C.normΩ,one_mul]; exact FleetAmtR C σ A x none L B q h
#print axioms CensusAmtR
#print axioms RaateR
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
