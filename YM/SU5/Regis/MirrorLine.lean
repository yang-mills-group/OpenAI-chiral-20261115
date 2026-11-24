import YM.SU5.Regis.Voyance
import YM.SU5.Celeste.Custodian

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition
variable (P:Spine)(R : P.Register)(j:Axis)
local notation "Ω"=>P.Hil j
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "W"=> P.calibration
local notation "Q"=> P.par.block
local notation "ℓ"=> P.calibration.ℓ
local notation "Ξ"=> household W
open Papal Regis.Head Gleam
variable {I J:Type*}[Fintype I][Fintype J] (A:Etch SU.group I)(Z:Etch SU.group J) (ρ:ℝ)
/-- intrinsic pose test -/
def view (s:ℕ): P.Test:= P.art (household P.calibration (panelet A (museumV (P:=P.par) s))) (Tower.aux_test ((designed_test ..).widen))
def rollPose (s:Signed)(x:Cover)(N:Side) := paletteU A ρ s (wrap (More N) x)
lemma lit_lane(s:Signed)(x:Cover) : panelet (A.pose s x) ρ=rollPose A ρ s x:=by funext N z; unfold rollPose panelet paletteU Clock.Hookah.chalkOp; dsimp only; rw [show (A.pose s x).palette ρ 1 0 _=_ from A.posed_p ..] -- ns
lemma home_s : rollPose A ρ 1 0 = panelet A ρ:=by funext N; unfold rollPose panelet; rw [map_zero]
private def returning (j:Axis)(z:ℤ): Cover:= 2 • (z • step j)
lemma linear_lull(s:Signed)(x:Cover)(z:ℤ): fluent j z (rollPose A ρ s x)=rollPose A ρ (Signed.mirror j*s) (affine (Signed.mirror j) (returning j z) x):=by
 funext N t; unfold fluent rollPose reflMark reflFields paletteU Clock.Hookah.chalkOp; dsimp only [Prod.map]; rw [theta_smul,theta_one,fling_eq,A.panel_pull, Complex.star_def, Complex.conj_ofReal]; congr 4; simp only [returning,affine, map_add, wrap_signed]; try rfl -- congr
lemma port_forward (z:ℤ): traction j z (panelet A ρ)= rollPose A ρ 1 (returning j z):=by
 unfold traction; rw [← home_s A ρ,linear_lull,linear_lull]; simp only [affine,returning,Signed.act_zero, zero_smul,smul_zero,zero_add, mul_one]; rw [show Signed.mirror j* Signed.mirror j=1 from (by nth_rw 2 [← Signed.mirror_inv j]; rw [mul_inv_cancel])]
lemma passenger (s:ℕ)(q:ℕ) : P.halfShift j q (P.view A s) = P.view (A.pose 1 (returning j (gaugeShift (Q) (q:ℤ)))) s:=by
 apply Subtype.ext; let G:=Heat.gaugeShift (Q) (q:ℤ); change household P.calibration (traction j G (panelet A _))=household P.calibration (panelet _ _); rw [lit_lane,port_forward] -- unify placeholders
lemma paint_mul (s:ℕ): P.view A s*P.view Z s=P.view (A.radial Z) s:= by
 apply Subtype.ext; funext n x; change ((A.here _ x.1:ℂ) • _)*((Z.here _ x.1:ℂ) • (1:FC (Single (P.calibration.c n))))=((A.radial Z).here _ x.1:ℂ) • _; rw [Etch.radial_h]; push_cast; rw [Matrix.smul_mul,one_mul,smul_smul]
lemma paint_theta(s:ℕ)(b:Signed)(x:Cover): P.reflectTest j (P.view (A.pose b x) s)= P.view (A.pose (Signed.mirror j * b) ((Signed.mirror j).act x)) s:=by
 apply Subtype.ext; let t:= museumV (P:=P.par) s; change household P.calibration (fluent j 0 (panelet _ _))= household P.calibration (panelet _ _); rw [lit_lane,lit_lane,linear_lull]; simp only [affine,returning,zero_smul,smul_zero,add_zero]
private def domeErase(P:Spine): P.Test→ₗ[ℂ] Buffered.Family P.calibration:=⟨⟨fun i=>i.val,fun i j=>rfl⟩,fun c f=>rfl⟩ -- Families ring has module, universes
lemma ensemble_book (o:J→ Cover)(t:J→ Signed)(s:ℕ) : P.view (A.ensemble t o) s= ∑ i:J,P.view (A.pose (t i) (o i)) s:=by
 apply Subtype.ext; let K:= (∑ i:J,(P.view (A.pose (t i) (o i)) s)); have h:K.val=∑ i:J,(P.view (A.pose (t i) (o i)) s).val:= by have e(z:P.Test):domeErase P z=z.val:=rfl; simp_rw [←e]; exact map_sum (domeErase P) (fun i=> P.view (A.pose (t i) (o i)) s) univ; -- find function erasure
 rw [h]; funext n x; simp only [Finset.sum_apply]; let N:=P.calibration.c n; let g:Seat N:=0; change ((A.ensemble t o).here _ x.1:ℂ) • _ = ∑ i:J, ((A.pose (t i) _).here _ x.1:ℂ) • _; rw [Etch.ensemble_h,Etch.gallery,Complex.ofReal_sum,sum_smul]; simp_rw [A.posed_p]; rfl
lemma mirror_view(s:ℕ)(x:J→ Cover)(t:J→Signed) :
   P.reflectTest j (P.view (A.ensemble t x) s)= P.view (A.ensemble (fun i=>Signed.mirror j*t i) (fun i=> (Signed.mirror j).act (x i))) s:=by
 rw [ensemble_book P _ x,ensemble_book]; rw [map_sum]; apply Finset.sum_congr rfl; intro i _; rw [P.paint_theta]
def nexus (t:Etch SU.group I)(o:J→ Cover): Etch SU.group ((J×I) ⊕ (J×I)):= (t.ensemble (fun _=>Signed.mirror j) (fun i=>(Signed.mirror j).act (o i))).radial (t.ensemble (fun _=>1) o)
lemma nexus_sum (x:J→ Cover)(s:ℕ): P.view (nexus j A x) s=P.reflectTest j (P.view (A.ensemble (fun _=>1) x) s)*P.view (A.ensemble (fun _=>1) x) s :=by
 rw [P.mirror_view,P.paint_mul]; simp [nexus]
abbrev stretchO (b:ℕ):= returning j (gaugeShift P.par.block (b:ℤ))
def lineup (b:J→ℕ):= P.stretchO j ∘ b
lemma stretchO_inj : Injective (P.stretchO j):=by
 intro s t p; let B:ℝ:= P.par.block.val; let x:ℤ:=↑P.par.block.val; have ht:0<x:=by unfold x; positivity
 have he:= congrFun p j; unfold stretchO returning gaugeShift at he; simp at he; omega -- need mult
variable (b:J→ℕ)
lemma view_wing(s:ℕ): P.view (A.ensemble (fun _=>1) (P.lineup j b)) s= ∑ i, P.halfShift j (b i) (P.view A s):=by rw [ensemble_book]; simp_rw [passenger]; rfl
lemma located(s:ℕ)(U:∀ i,Tower.region j 0 (P.calibration.ℓ) (onFlight P.par.block (spanOf A) j (b i))) : ∃ v:P.Vox j s, P.voxTest j s v=P.view (A.ensemble (fun _=>1) (P.lineup j b)) s:=by
 let f:=P.view A s; let S(i:J):=onFlight P.par.block (spanOf A) j (b i); let T:= univ.biUnion S; let A':=∑ i,P.halfShift j (b i) f
 -- choose T union finite. even/narrow.
 have he(i:J): P.halfShift j (b i) f ∈bay P.calibration T true:=by rw [Tapestry.locates,P.halfShift_val]; exact (Tower.flow_port _ _ _ ((designed_test A P.calibration (museumV (P:=P.par) s)).widen)).mono (subset_biUnion_of_mem S (mem_univ i))
 refine ⟨P.positiveVox j s T A' ((bay P.calibration T true).sum_mem fun i _=>he i) ?_,?_⟩; · intro x q; obtain ⟨i,_,t⟩:= mem_biUnion.mp q; exact U i x t
 rw [P.view_wing]; rfl
lemma keepAll : ∃ b:J→ℕ, Injective b ∧ ∀ i,Tower.region j 0 (P.calibration.ℓ) (onFlight P.par.block (spanOf A) j (b i)):=by
 obtain ⟨k,h⟩:= Filter.eventually_atTop.1 (prepareLaunch P.par.block (spanOf A) j (ℓ)); let f:= Fintype.equivFin J; exact ⟨fun i=>k+↑(f i),fun i t g=>f.injective (Fin.val_injective (Nat.add_left_cancel g)),fun i=>h _ (Nat.le_add_right ..)⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.located
