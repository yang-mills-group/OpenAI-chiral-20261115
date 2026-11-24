import GaugeFieldConstruction.Wish
import Mathlib.Analysis.ODE.ExistUnique

/-!
# Finite-dimensional flows. For now algebraic spaces `H` with the topology
 implemented in their coordinates. Don't import this structure as an instance onto the
 Finsupp shell of **all** jets.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Stage
open Cauchy Row Phys Calibration RawBank Function Set Filter
open scoped Matrix Matrix.Norms.Frobenius BigOperators Topology ContDiff
variable {α β η : Type*}
abbrev SO := ↥orbit

section
variable {H V R : Type*} [AddCommGroup H] [Module ℂ H] [AddCommGroup V] [Module ℂ V]
def Sends (f : ℝ → H) (t : ℝ) (U : H) := ∀ x : H →ₗ[ℂ] ℂ, HasDerivAt (x ∘ f) (x U) t
lemma posts {f : ℝ → H} {t} {U : H} (h : Sends f t U) (A : H →ₗ[ℂ] V) : Sends (A ∘ f) t (A U):= fun Q=>h (Q ∘ₗ A)
lemma captain [Module.Finite ℂ H] (A : Module.End ℂ H) (p q : ℝ→H) (h : ∀ t,Sends p t (A (p t)))
    (g : ∀ t,Sends q t (A (q t))) (e : p 0=q 0) : p=q := by
  let L:= (Module.finBasis ℂ H).equivFun
  let K : (Fin (Module.finrank ℂ H)→ℂ)→L[ℂ] (Fin (Module.finrank ℂ H)→ℂ):= LinearMap.toContinuousLinearMap (L.toLinearMap ∘ₗ A ∘ₗ L.symm.toLinearMap)
  have he (p : ℝ → H) t (h : Sends p t (A (p t))): HasDerivAt (fun t=>L (p t)) (K (L (p t))) t := by
    rw [hasDerivAt_pi]; intro i
    rw [show K (L (p t))= L (A (p t)) from congr_arg L (congr_arg A (L.symm_apply_apply (p t)))]
    exact h (LinearMap.proj i ∘ₗ L.toLinearMap)
  have H : (L ∘ p)=(L ∘ q):= ODE_solution_unique_univ (s:=fun _=> Set.univ) (v:=fun _ : ℝ=> (K : _→_)) (fun t=>K.lipschitz.lipschitzOnWith) (fun t=>⟨he p t (h t),trivial⟩) (fun t=>⟨he q t (g t),trivial⟩) (show (L ∘ p) 0=(L ∘ q) 0 from congr_arg L e)
  exact funext fun t=> L.injective (congr_fun H t)
lemma confined [Module.Finite ℂ H] {A : Module.End ℂ H} (p : ℝ→H) (h : ∀ t,Sends p t (A (p t))) (e:p 0=0): p=0 := by
  apply captain A p 0 h ?_ e
  intro t L; change HasDerivAt (fun _=> L 0) (L (A 0)) t; rw [map_zero,map_zero]; simp; exact hasDerivAt_const _ _ -- tweak
end
namespace Cell
variable [Fintype α] [DecidableEq α] (P : Cell α)

def rotate : Ortho→* Module.End ℂ (J α) where
  toFun u:= bill (P.active u)
  map_one':= LinearMap.ext fun i=>by rw [map_one,bills1]; rfl
  map_mul' x y:= by rw [map_mul]; exact (success ..).symm
lemma north (u : Rotors) (x) : Sends (fun t=> P.rotate (Ortho.oneParameter u t) x) 0 (P.beta u x) := by
  intro L
  have he i : HasDerivAt (fun t=> L (P.rotate (Ortho.oneParameter u t) (ket i))) (L (P.beta u (ket i))) (0:ℝ):= by
    unfold rotate; simp only [MonoidHom.coe_mk, OneHom.coe_mk,bill,on_ket,Cell.beta,map_sum,map_smul]
    exact HasDerivAt.fun_sum fun j _=> ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 (P.live u j i)).mul_const _)
  induction x using Finsupp.induction_linear with
  | zero => simp only [Function.comp_def,map_zero]; exact hasDerivAt_const _ _
  | add x y h k =>simp only [Function.comp_def,map_add]; exact h.add k
  | single i t=>
    rw [show Finsupp.single i t=t • ket i from by simp [ket]]
    simp only [Function.comp_def,map_smul]; exact (he i).const_smul t
lemma globe (u : Rotors) (x) (t): Sends (fun t=>P.rotate (Ortho.oneParameter u t) x) t (P.beta u (P.rotate (Ortho.oneParameter u t) x)) := by
  intro L; let R r:=P.rotate (Ortho.oneParameter u r); let y:= R t x
  let G := fun r=> L (R r y)
  have he s : G (s-t)=L (R s x) := by
    unfold G y R
    rw [← Module.End.mul_apply, ← map_mul,← parameter_add,sub_add_cancel]
  suffices T: HasDerivAt (fun s:ℝ=>G (s-t)) (L (P.beta u y)) t by simp_rw [he] at T; exact T
  have H : HasDerivAt G (L (P.beta u y)) (t-t):= by rw [sub_self]; exact north P u y L
  have he:= H.scomp t (h:=fun z : ℝ=> z-t) ((hasDerivAt_id' t).sub_const t); exact he.congr_deriv (by simp)
lemma realZ (x : Ortho) (v) : Conj.tr α (P.rotate x v)=P.rotate x (Conj.tr α v):= by
  change Conj.tr _ (bill _ _) = bill _ _
  have he : Conj.tr α ∘ₛₗ bill (P.active x)= bill (P.active x) ∘ₛₗ Conj.tr α := Conj.ksets (fun i=>by rw [LinearMap.comp_apply,LinearMap.comp_apply,Conj.tr_ket,bill,on_ket]; simp only [map_sum,LinearMap.map_smulₛₗ,Conj.tr_ket]; simp [Conj.bar])
  exact LinearMap.congr_fun he v

/-- Read transported pin prices. -/
lemma breeze (x) (L : J α →ₗ[ℂ] ℂ) : Continuous (fun u:Ortho=>L (P.rotate u x)) := by
  have h i : Continuous (fun u:Ortho=>L (P.rotate u (ket i))) := by
    simp only [rotate,MonoidHom.coe_mk,OneHom.coe_mk,bill,on_ket,map_sum,map_smul,smul_eq_mul]
    exact continuous_finsetSum _ fun j _=> ((Complex.ofRealCLM.continuous.comp (P.cont j i)).mul continuous_const)
  induction x using Finsupp.induction_linear with
  | zero=> simp only [map_zero]; exact continuous_const
  | add x y a b=>simp only [map_add]; exact a.add b
  | single i t=> rw [show Finsupp.single i t=t • ket i from by simp [ket]]; simp only [map_smul,smul_eq_mul]; exact continuous_const.mul (h i)
end Cell

namespace Angles
open Cell
variable [Fintype α] [DecidableEq α] {R : Record β η} {F : Conj.Flip β} {H : Submodule ℂ (J β)} (B : Mint R H F α)
    (P : Cell α) (p : ∀ x : J α,B.issue x=0 → ∀ Ω,B.issue (P.beta Ω x)=0)
local instance iG : AddCommGroup ↥H:= @Submodule.addCommGroup ℂ (J β) _ _ _ _ -- caution syntactic instance

include p
variable (f : Module.Finite ℂ H)
include f
lemma grace (s : Ortho) (v : s∈orbit) (i) (h:B.issue i=0): B.issue (P.rotate s i)=0 := by
  have he Ω t j (g : B.issue j=0): B.issue (P.rotate (Ortho.oneParameter Ω t) j)=0 := by
    let u (t : ℝ):= B.issue (P.rotate (Ortho.oneParameter Ω t) j)
    have h' (t : ℝ) : Sends u t (Mint.spin B P Ω (u t)) := by unfold u; rw [Mint.click B P p]; exact posts (P.globe Ω j t) B.issue
    have ht : u 0=0:=by unfold u; rw [YM.Work.A13.oneParameter_zero,map_one,Module.End.one_apply,g]
    exact congr_fun (confined u h' ht) t
  -- inversion step use also inv membership
  suffices T: ∀ x∈orbit,(∀ j,B.issue j=0→B.issue (P.rotate x j)=0)∧ (∀ j,B.issue j=0→B.issue (P.rotate x⁻¹ j)=0) from (T s v).1 _ h
  intro x hx; apply Subgroup.closure_induction (p:=fun x _=>_) _ _ _ _ hx
  · rintro x ⟨Ω,t,e⟩; subst x; rw [param_inv]; exact ⟨he Ω t, he Ω (-t)⟩
  · constructor <;> intro i h <;> simpa
  · intro x y _ _ p q; constructor
    · intro i z; rw [map_mul,Module.End.mul_apply]; exact p.1 _ (q.1 _ z)
    intro i z; rw [_root_.mul_inv_rev,map_mul,Module.End.mul_apply]; exact q.2 _ (p.2 _ z)
  intro x a h; rw [inv_inv]; exact ⟨h.2,h.1⟩

omit f p in
def takeup (s : SO): Module.End ℂ H:= B.issue ∘ₗ P.rotate s.val ∘ₗ B.protrude
lemma returns (s : SO) (z): takeup B P s (B.issue z)=B.issue (P.rotate s.val z) := by
  let c := B.protrude (B.issue z)
  have hc:B.issue (c-z)=0 := by rw [map_sub]; rw [show B.issue c=B.issue z from LinearMap.congr_fun (show B.issue ∘ₗ B.protrude=LinearMap.id from Classical.choose_spec (Mint.bend B)) _,sub_self]
  have H:= grace B P p f s.val s.property _ hc; rw [map_sub,map_sub,sub_eq_zero] at H; exact H

def repr (p : ∀ x : J α,B.issue x=0→∀ Ω,B.issue (P.beta Ω x)=0) (f : Module.Finite ℂ H) : SO →* Module.End ℂ H where
  toFun:= takeup B P
  map_one':= by
    apply LinearMap.ext; intro x; obtain ⟨z,rfl⟩:=B.supply x
    rw [returns B P p f]; change _=B.issue z; congr; rw [show ((1:SO).val)=1 from rfl,map_one]; rfl
  map_mul' x y:= LinearMap.ext fun u=>by obtain ⟨z,rfl⟩:=B.supply u; rw [Module.End.mul_apply]; simp_rw [returns B P p f,Subgroup.coe_mul,map_mul]; rfl

def rise (u : Rotors) (t : ℝ): SO:=⟨_,paid u t⟩
lemma bOut (x s): repr B P p f s (B.issue x)= B.issue (P.rotate s.val x) := returns B P p f s x
lemma pressure (u : Rotors) (x : H) t : Sends (fun t=> repr B P p f (rise u t) x) t (B.spin P u (repr B P p f (rise u t) x)) := by
  obtain ⟨s,rfl⟩:=B.supply x; simp_rw [bOut]; rw [Mint.click B P p]; exact posts (P.globe u s t) B.issue
lemma cont (x : H) (L:H→ₗ[ℂ]ℂ):Continuous (fun s :SO=> L (repr B P p f s x)) := by
  obtain ⟨v,rfl⟩:=B.supply x; simp_rw [bOut]; exact (Cell.breeze P v (L ∘ₗ B.issue)).comp continuous_subtype_val
lemma hero (v w : H) (x : SO) (h:w.val=F v.val): (repr B P p f x w).val=F (repr B P p f x v).val := by
  obtain ⟨k,rfl⟩:=B.supply v; rw [show w=B.issue (Conj.tr α k) from Subtype.ext (h.trans (B.real k)), bOut,bOut]; rw [← Cell.realZ]; exact Eq.symm (B.real _)
lemma charges (G : LabelAction.Carries R H) (q : Cell.Match B.label P) (s : Signed) (x : H) (u : signBit s=false) : G.moves s x= repr B P p f ⟨s.ortho,(covers_all _).mpr (by rw [parity,u]; rfl)⟩ x := by
  obtain ⟨z,rfl⟩:=B.supply x; rw [bOut,← B.respect]; change _ = B.issue (bill (P.active s.ortho) z); rw [q s u]
end Angles
end YM.GaugeFieldConstruction.Stage
