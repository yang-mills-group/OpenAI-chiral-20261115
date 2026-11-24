import Velour.Crepe.Aperture

/-! # Ironing aprons with a total physical time budget. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 800000
set_option quotPrecheck false
noncomputable section
namespace YM.OS.Semigroup
open scoped NNReal
variable {Z:Hilbert}{j:Axis} (S:Semigroup Z j)
def pad (a b:ℝ) : Z.Op →ₗ[ℂ] Z.Op where
 toFun T:= S.E a.toNNReal * T * S.E b.toNNReal
 map_add' T U:=by rw [mul_add, add_mul]
 map_smul' c T:=by rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc]; rfl
lemma pad_le(a b:ℝ)(T:Z.Op): ‖S.pad a b T‖ ≤ ‖T‖:=by
 refine (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) (S.shrinks _)).trans ?_)
 exact (norm_mul_le ..).trans (mul_le_of_le_one_left (norm_nonneg _) (S.shrinks _))


lemma pad_val(a b:ℝ)(T:Z.Op): S.pad a b T = S.E a.toNNReal * T * S.E b.toNNReal:=rfl
lemma E_mul(a b:ℝ≥0): S.E a * S.E b = S.E (a+b):= (S.time a b).symm
lemma star_pad(a b:ℝ)(T:Z.Op): star (S.pad a b T)= S.pad b a (star T):=by
 have h(t:ℝ≥0):star (S.E t) = S.E t:= S.sym t
 rw [pad_val,pad_val, star_mul, star_mul, h,h,mul_assoc]
lemma pad_twice {a b c d:ℝ}(e:0≤a)(f:0≤b)(g:a≤c)(h:b≤d)(T:Z.Op):
   S.pad (c-a) (d-b) (S.pad a b T) = S.pad c d T:=by
 rw [pad_val,pad_val,pad_val,
      ←mul_assoc (S.E (c-a).toNNReal),←mul_assoc (S.E (c-a).toNNReal),mul_assoc (_*_ *T),E_mul,E_mul,
      ←Real.toNNReal_add (sub_nonneg.mpr g) e,←Real.toNNReal_add f (sub_nonneg.mpr h),sub_add_cancel,add_sub_cancel]
end YM.OS.Semigroup

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
variable (P: Spine) (j:Axis) (x:P.Spectrum0 j)
open Aria Set TopologicalSpace Metric
local notation "Λ"=> P.par
local notation "K"=> P.calibration
local notation "H"=> P.large
local notation "Y₀"=> P.run
local notation "Φ" => P.colorSpace j x
local notation "ω"=>P.colorZero j x
local notation "u"=> enclave P.calibration
local notation "X"=> P.ColorHil j x

local notation "E"=> (P.physicalEnergy j x).E
local notation "m"=> timeMesh P.par
local notation "Q" => P.shifts j
local notation "L"=> P.par.R.L.val
variable {s t v w:ℕ}
local notation "σ"=> P.physicalEnergy j x
namespace Apron
variable (D:P.Apron)
local notation "W"=> D.realWidth P j
/-- On ColorHil, at the original grid center (no spatial slide),
using total left/right physical time budgets (includes the slab itself).
Use only when W ≤ a,b; as with beamRaw, smaller budgets do not inverse-heat.
-/
noncomputable def dye (a b:ℝ): (P.ColorHil j x).Op:=
 (σ).pad (a-W) (b-W) (D.engine P j x)
/-- Symmetric time budget. -/
noncomputable def velour (a:ℝ):= D.dye P j x a a
lemma dye_twice {a b c d:ℝ}(e:W ≤ a)(f:W ≤ b)(g:a≤c)(h:b≤d):
   (σ).pad (c-a) (d-b) (D.dye P j x a b) = D.dye P j x c d:=by
 unfold dye
 refine Eq.trans ?_ ((σ).pad_twice (sub_nonneg.mpr e) (sub_nonneg.mpr f)
     (sub_le_sub_right g _) (sub_le_sub_right h _) (D.engine P j x))
 rw [sub_sub_sub_cancel_right, sub_sub_sub_cancel_right]


lemma dye_le {a b c d:ℝ}(e:W≤a)(f:W≤b)(g:a≤c)(h:b≤d):
   ‖D.dye P j x c d‖≤‖D.dye P j x a b‖:=by
 rw [←D.dye_twice P j x e f g h]
 exact (σ).pad_le _ _ _ 
lemma velour_twice {a c:ℝ}(e:W ≤ a)(g:a≤c):
   D.velour P j x c=(σ).pad (c-a) (c-a) (D.velour P j x a):=(D.dye_twice P j x e e g g).symm
lemma velour_le {a c:ℝ}(e:W≤a)(g:a≤c): ‖D.velour P j x c‖ ≤ ‖D.velour P j x a‖:=D.dye_le P j x e e g g
end Apron


lemma commence_velour (f:P.Test): P.chartAll 0 f=f:=by
 unfold chartAll
 generalize Vacancy.ordinate=l
 induction l with
 | nil=>rfl
 | cons i l t=> rw [P.cruise_step,AlgHom.comp_apply,Pi.zero_apply,t, P.shifts_zero]
lemma ThreadOp.unshiftCap {P:Spine}{j:Axis}{x:P.Spectrum0 j}{p:Cover}{f:P.Test}
    {T:(P.ColorHil j x).Op}(q:P.ThreadOp j x s w (P.chartAll p f) T):
    P.ThreadOp j x s w (P.shifts j (p j) f) (P.charter j x (P.vtile s (-p)) T):=by
    exact (q.shiftCap (-p)).mono rfl (by rw [Pi.neg_apply,neg_neg,P.chart_ids,neg_add_cancel,P.commence_velour])

-- generic. q at center budget U ticks (total u+u). extend to shift θ:ℤ and width W
local notation "ψ"=>P.physicalEnergy j x
local notation "ρ"=>bell (timeMesh P.par)
variable {P j x}

lemma ThreadOp.extendCenter {n:ℕ}{f:P.Test}
    {T:(P.ColorHil j x).Op} (q:P.ThreadOp j x s (n+n) (Q n f) T)
    (W:ℕ)(θ:ℤ)(A B:ℝ)
    (a:ρ s θ=A)(b:ρ s W-A=B)(e:ρ s n ≤ A)(g:ρ s n ≤ B):
    P.ThreadOp j x s W (Q θ f) ((ψ).pad (A-ρ s n) (B-ρ s n) T):=by
   have h₁:(n:ℤ)≤θ:= (bell_le m s _ _).mp (e.trans_eq a.symm)
   have h₂:(n:ℤ)≤(W:ℤ)-θ:= (bell_le m s _ _).mp (g.trans_eq ((P.bell_sub s W θ).trans (by rw [a,b])).symm)
   let i:= (θ-n).toNat; let k:=((W:ℤ)-θ-n).toNat
   have x₁:(i:ℤ)=θ-n:= Int.toNat_of_nonneg (sub_nonneg.mpr h₁)
   have x₂:(k:ℤ)=W-θ-n:= Int.toNat_of_nonneg (sub_nonneg.mpr h₂)
   have y₁:(A-ρ s n).toNNReal=whenly m s i:=by
       rw [←a,←P.bell_sub,←x₁,natural_time]; exact Real.toNNReal_coe
   have y₂:(B-ρ s n).toNNReal=whenly m s k:=by
       rw [←b,←a,←P.bell_sub,←P.bell_sub,←x₂,natural_time]; exact Real.toNNReal_coe
   rw [OS.Semigroup.pad_val,y₁,y₂]


   exact (q.pad i k).mono (by omega) (by rw [P.shifts_sum,x₁,sub_add_cancel])
variable (P j x)
namespace Apron
variable (D:P.Apron)
local notation "W"=> D.realWidth P j
lemma dyedHere (θ:ℤ)(A B:ℝ)
    (a:ρ D.s θ=A)(b:ρ D.s w-A=B)(e:W ≤ A)(g:W ≤ B):
    P.ThreadOp j x D.s w (Q θ D.F) (D.dye P j x A B):= D.sewn.extendCenter w θ A B a b e g
lemma dyedAbove (h:D.s ≤ s)(θ:ℤ)(A B:ℝ)
    (a:ρ s θ=A)(b:ρ s w-A=B)(e:W ≤ A)(g:W ≤ B):
    P.ThreadOp j x s w (Q θ (D.full P s)) (D.dye P j x A B):=by
 have p:= D.zoom_bell P j s h
 unfold dye
 rw [←p]
 exact (D.promoted h).extendCenter w θ A B a b (p.le.trans e) (p.le.trans g)


lemma buyDye {s w:ℕ}(p:Cover){T:(P.ColorHil j x).Op}
     (g:P.ThreadOp j x s w (P.chartAll p D.F) T)
     (h:D.s = s)
     (a:W ≤ ρ s (p j)) (b:W ≤ ρ s w - ρ s (p j))
     (d:ℝ)(e:ρ s w≤d):
     W ≤ d ∧ ‖D.velour P j x d‖ ≤ ‖T‖:=by
 subst s
 have t:0<W:=D.real_width_pos P j
 have p0:ρ D.s (p j)≤d:= by linarith
 have p1:ρ D.s w - ρ D.s (p j)≤d:=by linarith
 refine ⟨a.trans p0,(D.dye_le P j x a b p0 p1).trans ?_⟩
 rw [(D.dyedHere P j x (w:=w) (p j) _ _ rfl rfl a b).unique g.unshiftCap]
 exact P.charter_pay ..
end Apron
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

