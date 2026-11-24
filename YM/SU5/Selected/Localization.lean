import YM.SU5.Selected.PlantLeft

/-! # Abstract helper for building the physical phase (not itself the phase application)

Use χ on a Gram given by operator legs $P$ out of space X. It yields an OS-space
implementing every transformation of the target Hilbert Y whose left action and adjoint
preserve the allowed Leg, as bounded operators. This style of choosing a phase then
using its character is motivated by the reconstruction framework in `YM/Phase` etc,
but also doesn't rely on an abstract choice of time stationary vectors being joint ground.
Carries linearity, *-structure. In particular this is not choosing a character to evaluate
operators that didn't lie in the ground algebra. P will be very concretely the actual `prepare`
ranges in the application, so these theorems apply to the very same **signed** measures only
with that proof!
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 230000
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.Selection.Localization
open Function Filter Set Analysis
open scoped Matrix MatrixOrder Topology InnerProductSpace ComplexOrder Classical

variable (X Y : Hilbert) (P : Submodule ℂ (X →L[ℂ] Y)) (B : StarSubalgebra ℂ X.Op)
structure Blueprint (f : B →ₗ[ℂ] ℂ) : Prop where
  owns (x y : ↑P) : x.val.adjoint.comp y.val ∈ B
  positive (x : ↑B) (p : 0 ≤ x.val) : 0 ≤ f x
namespace Blueprint
variable {B} {f : B →ₗ[ℂ] ℂ} {X Y P} -- dependent order tune!
-- crowd
variable (V : Blueprint X Y P B f)

def bond (x y : P) : B := ⟨x.val.adjoint.comp y.val,V.owns x y⟩
lemma bond_add_r (x y z : P) : V.bond x (y+z)=V.bond x y+V.bond x z:=
  Subtype.ext (ContinuousLinearMap.comp_add ..)
lemma bond_add_l (x y z : P) : V.bond (x+y) z=V.bond x z+V.bond y z:=Subtype.ext (by
  change (x.val+y.val).adjoint.comp z.val=_; rw [map_add]; exact ContinuousLinearMap.add_comp ..)
lemma bond_scale_r (x y : P) (b : ℂ) : V.bond x (b • y)=b • V.bond x y:= by
  apply Subtype.ext; apply ContinuousLinearMap.ext; intro i; exact map_smul x.val.adjoint _ _
lemma bond_scale_l (x y : P) (b : ℂ) : V.bond (b • x) y=star b • V.bond x y:=Subtype.ext (by
  change (b • x.val).adjoint.comp y.val=_; rw [map_smulₛₗ]; rfl)

def pair : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ where
  toFun x := {
    toFun y := f (V.bond x y)
    map_add' u v := by rw [V.bond_add_r,map_add]
    map_smul' u v := by rw [V.bond_scale_r,map_smul]; rfl }
  map_add' x y := LinearMap.ext (fun s => by
    change f (V.bond (x+y) s)=_
    rw [V.bond_add_l,map_add]; rfl)
  map_smul' z x := LinearMap.ext (fun s => by
    change f (V.bond (z • x) s)=_
    rw [V.bond_scale_l,map_smul]; rfl)
lemma pair_nonneg (x : P) : 0 ≤ V.pair x x := V.positive _ ((ContinuousLinearMap.nonneg_iff_isPositive (x.val.adjoint.comp x.val)).2 (ContinuousLinearMap.isPositive_adjoint_comp_self x.val))

abbrev Room := _root_.YM.Kernel.Gram (fun (x y : P) => V.pair x y)
lemma can_room : Nonempty (V.Room) := _root_.YM.Kernel.host (fun _ f => Tower.halfSpaceKernel V.pair (fun x => V.pair_nonneg x) f)

variable (H : V.Room)
def bloom : P →ₗ[ℂ] H.H where
  toFun := H.plant
  map_add' x y := by
    apply H.whole.eq_of_inner_right ℂ; intro i
    induction i using Finsupp.induction_linear with
    | zero => simp
    | add a b p q => simp only [map_add,inner_add_left,p,q]
    | single i v => rw [inner_add_right]; simp [H.measure,YM.Kernel.Gram.stems]; ring
  map_smul' z x := by
    apply H.whole.eq_of_inner_right ℂ; intro i
    induction i using Finsupp.induction_linear with
    | zero => simp
    | add a b p q => simp only [map_add,inner_add_left,p,q]
    | single i v => simp [H.measure,YM.Kernel.Gram.stems]; ring

lemma bloom_dense : DenseRange (V.bloom H) := by
  change Dense (↑(LinearMap.range (V.bloom H)) : Set H.H)
  refine H.dense.mono (Submodule.span_le.mpr ?_)
  rintro a ⟨x,rfl⟩; exact ⟨x,rfl⟩
lemma seeded (x y : P) : inner ℂ (V.bloom H x) (V.bloom H y)= f (V.bond x y) := H.measure _ _
lemma petals (x y : P) : inner ℂ (V.bloom H x) (V.bloom H y)= V.pair x y := H.measure _ _
lemma norm_bloom_sq (x : P) : ‖V.bloom H x‖ ^ 2 = (f (V.bond x x)).re := by
  rw [←seeded (H:=H),← inner_self_eq_norm_sq (𝕜:=ℂ)]; rfl -- maybe direction
end Blueprint
-- stabilizer
namespace Pruner
variable {X Y}

def Left (T : Y.Op) : Prop := ∀ x : P, T.comp x.val ∈ P
namespace Left
variable {P} {T U : Y.Op}
lemma product (h : Left P T) (t : Left P U) : Left P (T*U) := fun x => h ⟨U.comp x.val,t _⟩
lemma sum (h : Left P T) (t : Left P U) : Left P (T+U) := fun x => by rw [ContinuousLinearMap.add_comp]; exact P.add_mem (h x) (t x)
lemma scale (h : Left P T) (c : ℂ) : Left P (c • T) := fun x => by rw [ContinuousLinearMap.smul_comp]; exact P.smul_mem c (h x)
lemma source : Left P 1 := fun x => x.property
lemma none : Left P 0 := fun x => P.zero_mem
end Left

def preserves : StarSubalgebra ℂ Y.Op where
  carrier := {T | Left P T ∧ Left P (star T)}
  zero_mem' := ⟨Left.none, by rw [star_zero]; exact Left.none⟩
  one_mem' := ⟨Left.source, by rw [star_one]; exact Left.source⟩
  add_mem' p q := ⟨Left.sum p.1 q.1, by rw [star_add]; exact Left.sum p.2 q.2⟩ -- type indentation? implicit x
  mul_mem' p q := ⟨Left.product p.1 q.1, by rw [star_mul]; exact Left.product q.2 p.2⟩
  algebraMap_mem' c := by
    change Left P _ ∧ Left P _; rw [Algebra.algebraMap_eq_smul_one,star_smul,star_one]
    exact ⟨Left.source.scale c,Left.source.scale _⟩
  star_mem' h := ⟨h.2, by rw [star_star]; exact h.1⟩
-- something with `star_mem'` binder tune
lemma stay (T : preserves P) : Left P T.val := T.property.1

def applyM (T : preserves P) : P →ₗ[ℂ] P where
  toFun x := ⟨T.val.comp x.val,stay P T x⟩
  map_add' _ _ := Subtype.ext (ContinuousLinearMap.comp_add ..)
  map_smul' _ _ := by apply Subtype.ext; apply ContinuousLinearMap.ext; intro i; exact map_smul T.val _ _
lemma starTurn {B : StarSubalgebra ℂ X.Op} {f : B →ₗ[ℂ] ℂ} (V : Blueprint X Y P B f)
    (T : preserves P) (x y : P) : V.bond (applyM P (star T) x) y = V.bond x (applyM P T y) := by
  apply Subtype.ext; change (T.val.adjoint.comp x.val).adjoint.comp _ = x.val.adjoint.comp (T.val.comp y.val)
  rw [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint]; rfl
end Pruner
namespace Blueprint
open Pruner
variable {X Y P B} {f : B →ₗ[ℂ] ℂ} (V : Blueprint X Y P B f) (H : V.Room)
local notation "F" => V.bloom H
local notation "S" => preserves P
local notation "O" => applyM P

lemma pruner_bound (T : S) (x : P) : ‖(F) ((O) T x)‖ ≤ ‖(T.val : Y.Op)‖ * ‖(F) x‖ := by
  set p := (O) T x
  let c := ‖(T.val : Y.Op)‖; let a := V.bond x x; let b := V.bond p p
  -- as operator c² bound between positive caps
  have he : 0 ≤ (((c^2:ℝ):ℂ) • a-b).val := by
    let Q := (((c^2:ℝ):ℂ) • a-b)
    apply (ContinuousLinearMap.nonneg_iff_isPositive _).2
    apply (ContinuousLinearMap.isPositive_iff_complex _).2; intro y
    have ih(z : P): inner ℂ ((V.bond z z).val y) y = ↑(‖z.val y‖^2:ℝ) := by
      change inner ℂ (z.val.adjoint (z.val y)) y = _
      rw [ContinuousLinearMap.adjoint_inner_left, inner_self_eq_norm_sq_to_K]; norm_cast
    change (↑(RCLike.re (inner ℂ (Q.val y) y)):ℂ) = inner ℂ (Q.val y) y ∧ 0 ≤ (inner ℂ (Q.val y) y).re
    have hh : inner ℂ (Q.val y) y = ↑(c^2 * ‖x.val y‖^2 - ‖p.val y‖^2 : ℝ) := by
      change inner ℂ (((c^2:ℝ):ℂ) • a.val y - b.val y) y = _
      rw [inner_sub_left,inner_smul_left,show inner ℂ _ y= _ from ih x, show inner ℂ _ y= _ from ih p]; simp
    rw [hh]; let u := ((T.val : Y.Op).le_opNorm (x.val y))
    exact ⟨rfl, sub_nonneg.mpr ((pow_le_pow_left₀ (norm_nonneg _) (show ‖p.val y‖≤ c*‖x.val y‖ from (T.val : Y.Op).le_opNorm _) 2).trans_eq (mul_pow ..))⟩
  have hm := (Complex.le_def.mp (V.positive _ he)).1
  rw [map_sub,map_smul,Complex.sub_re] at hm
  change 0 ≤ _ - _ at hm
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow,V.norm_bloom_sq,V.norm_bloom_sq]
  refine sub_nonneg.mp ?_
  simpa only [smul_eq_mul,Complex.zero_re,Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,sub_zero] using hm

def implement (T : S) : H.H.Op := ((F).comp (applyM P T)).extendOfNorm (F)
lemma implement_size (T : S) : ‖V.implement H T‖ ≤ ‖(T.val : Y.Op)‖ := LinearMap.opNorm_extendOfNorm_le (V.bloom_dense H) (norm_nonneg _) (V.pruner_bound H T)
lemma implement_law (T : S) (x : P) : V.implement H T ((F) x) = (F) ((O) T x) := LinearMap.extendOfNorm_eq (V.bloom_dense H) ⟨_, V.pruner_bound H T⟩ x
lemma knows {x y : H.H.Op} (p : ∀ i, x ((F) i) = y ((F) i)) : x=y:= DFunLike.coe_injective ((V.bloom_dense H).equalizer x.continuous y.continuous (funext p))
local notation "V₀" => V.implement H

lemma pledge : (V₀) 1 = 1:= V.knows H (fun i => V.implement_law H _ _)
lemma again (T U : S) : (V₀) (T*U) = (V₀) T * (V₀) U := by
  refine V.knows H (fun i => ?_); change _ = (V₀) T ((V₀) U _); simp only [V.implement_law H]; rfl
lemma totals (T U : S) : (V₀) (T+U) = (V₀) T + (V₀) U := by
  refine V.knows H (fun i => ?_); rw [ContinuousLinearMap.add_apply]; simp only [V.implement_law H]; rw [show O (T+U) i = O T i + O U i from Subtype.ext (ContinuousLinearMap.add_comp ..),map_add]
lemma weights (T : S) (c : ℂ) : (V₀) (c • T) = c • (V₀) T := by
  refine V.knows H (fun i => ?_); rw [ContinuousLinearMap.smul_apply]; simp only [V.implement_law H]; rw [show O (c • T) i = c • O T i from Subtype.ext (ContinuousLinearMap.smul_comp ..),map_smul]
lemma adjoints (T : S) : (V₀) (star T)=star ((V₀) T) := by
  refine V.knows H (fun i => (V.bloom_dense H).eq_of_inner_right ℂ fun j => ?_)
  change _= inner ℂ ((F) j) ((V.implement H T).adjoint ((F) i))
  have he := starTurn P V (star T) j i
  rw [star_star] at he
  rw [ContinuousLinearMap.adjoint_inner_right, V.implement_law, V.implement_law, V.seeded,V.seeded,he]

set_option maxHeartbeats 600000 in
def plays : (S) →⋆ₐ[ℂ] H.H.Op where
  toFun := V₀
  map_mul' := V.again H
  map_add' := V.totals H
  map_one' := V.pledge H
  map_zero' := by simpa only [zero_smul] using (V.weights H 1 0)
  commutes' c := by rw [Algebra.algebraMap_eq_smul_one,V.weights,V.pledge,Algebra.algebraMap_eq_smul_one]
  map_star' := V.adjoints H
lemma remains_pos (T : S) (p : 0 ≤ (T.val:Y.Op)) : 0 ≤ V.plays H T := by
  have hp : (T.val:Y.Op).IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive _).1 p
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).2; apply ContinuousLinearMap.isPositive_def'.mpr
  refine ⟨ (show IsSelfAdjoint T from Subtype.ext hp.isSelfAdjoint).map _ ,?_⟩; intro x
  let q : Set H.H := { x | 0 ≤ (inner ℂ (V.plays H T x) x).re }
  apply closure_minimal (t:=q) _ (isClosed_le continuous_const (by fun_prop)) (V.bloom_dense H x)
  rintro x ⟨a,rfl⟩
  have hv : inner ℂ (V.plays H T ((F) a)) ((F) a) = f (V.bond a ((O) T a)) := by
    rw [← V.seeded H]; nth_rw 1 [← show ((V.plays H T):H.H.Op).adjoint=_ from (show IsSelfAdjoint T from Subtype.ext hp.isSelfAdjoint).map (V.plays H)] -- tune
    rw [ContinuousLinearMap.adjoint_inner_left]; exact congrArg _ (V.implement_law H T a)
  have hs := (Complex.le_def.mp (V.positive (V.bond a ((O) T a)) ((ContinuousLinearMap.nonneg_iff_isPositive _).2 (hp.adjoint_conj a.val)))).1
  change 0≤(inner ℂ _ _).re; rwa [hv]
end Blueprint
end YM.CF.Buffered.Afterglow.Tower.Selection.Localization
