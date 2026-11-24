import YM.SU5.Reconstruction.AnglePath.Budget
/-!
# Phase budgets passed via Friedrichs comparison (the second Clasp). Generic.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CrossedFrame.Cardio
open Function Set Filter MeasureTheory Spectral Analysis Metric
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace
variable {K J H D:Hilbert} {X:Type}
open Clasp

namespace Organ
variable [AddCommGroup X][Module ℂ X](A:Organ X H D)(G:Clasp K H H)(p:A.Pre G)(C:Clasp J H D)(q:A.Core C)
open MeasureTheory Multiplier Clasp Complex
variable (u:ℝ)(e:u∈Icc (0:ℝ) (1/2))
noncomputable def vellum(u z:ℝ):ℂ:= Real.exp ((1/2-u)*Real.log z + u * Real.log (1-z))
noncomputable def valons(u:ℝ) : J.Op:= order C.motion (vellum u ∘ C.realF)
local notation "Y"=> valons C
local notation "Π"=> C.motion
include e
private lemma zone_turn (x:ℝ)(v:x∈Icc (0:ℝ) 1): ‖vellum u x‖≤1:=by
 unfold vellum; rw [Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]; exact Real.exp_le_one_iff.mpr (add_nonpos (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr e.2) (Real.log_nonpos v.1 v.2)) (mul_nonpos_of_nonneg_of_nonpos e.1 (Real.log_nonpos (sub_nonneg.mpr v.2) (sub_le_self _ v.1))))
private lemma affords : Registers C.motion (vellum u ∘ C.realF) (Y u):=order_reads C.motion ⟨by unfold vellum; fun_prop,1,zero_le_one,fun x=> zone_turn u e (C.realF x) (C.price x)⟩
private lemma announceP : 0 ≤ Y u :=by
 let W:=Y u; apply (ContinuousLinearMap.nonneg_iff_isPositive W).2; apply (ContinuousLinearMap.isPositive_toLinearMap_iff _).mp; apply (LinearMap.isPositive_iff_complex _).2; intro x
 have hv: 0≤ inner ℂ x (W x):=by
    unfold W; rw [(affords C u e).awakes]; apply integral_nonneg; intro x; change 0 ≤ vellum u _; unfold vellum; positivity
 have he:0 ≤ inner ℂ (W x) x:=by rw [←inner_conj_symm]; simpa only [←Complex.star_def,star_nonneg_iff] using hv
 exact ⟨Complex.ext rfl he.2,he.1⟩
omit e
private lemma spirit(t:ℝ)(u:ℝ):vellum u t*vellum 0 t=oracle (u:ℂ) t:=by unfold vellum oracle; push_cast; rw [←Complex.exp_add]; ring_nf
local notation "R" => peel C.l
private lemma cost_pr:valons C 0=peel C.l:=by
 have t:=affords C 0 (by norm_num); have he:Y 0 *Y 0= spool C 0:=by
    apply (t.times t).single; rw [show (vellum 0 ∘ C.realF)*(vellum 0 ∘ C.realF)= _ from funext fun x=> show (vellum 0 ∘ C.realF) x*(vellum 0 ∘ C.realF) x=(oracle 0 ∘ C.realF) x from (by simpa using spirit (C.realF x) 0)]; exact book C 0 (by simp [scroll])
 rw [spool_first] at he; exact (CFC.sqrt_unique he (announceP C 0 (by norm_num))).symm
include e
private lemma annuity : valons C u * R= spool C u:= by
 rw [←cost_pr]; apply ((affords C u e).times (affords C 0 (by norm_num))).single
 rw [show (vellum u ∘ C.realF)*(vellum 0 ∘ C.realF)= _ from funext fun x=> show (vellum u ∘ C.realF) x*(vellum 0 ∘ C.realF) x=(oracle (u:ℂ) ∘ C.realF) x from spirit (C.realF x) u]; exact book C _ (show u∈Icc (0:ℝ) 1 from ⟨e.1,e.2.trans (by norm_num)⟩)
private lemma reachV : Injective (valons C u) := by
 let X:= (spectrum ℂ C.angle); apply (injective_iff_map_eq_zero (valons C u)).2 -- guess
 intro y hy; have hp:= (affords C u e).squareCost y; let f:= vellum u ∘ C.realF; rw [hy,norm_zero] at hp; let g(x:X):= ‖f x‖^2
 have he:∀ᵐ x∂ (Π).diagonal y,g x=0:=(integral_eq_zero_iff_of_nonneg (f:=g) (fun x=>sq_nonneg _) ?_).mp (by simpa [g,f] using hp.symm)
 swap
 · apply Tag.rent Π _ y; refine ⟨by unfold g f; unfold vellum; fun_prop,1,zero_le_one,fun x=>?_⟩; unfold g; rw [Real.norm_of_nonneg (sq_nonneg _)]; exact pow_le_one₀ (norm_nonneg _) (zone_turn u e _ (C.price x))
 have ga(x:X):0<g x:= pow_pos (norm_pos_iff.mpr (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')) _ -- local name shadow
 have v: (Π).diagonal y univ=0:=by
    exact measure_mono_null (fun x _=> (ga x).ne') (ae_iff.mp he)
 have h':= Registers.size Π y
 rw [Measure.real,v] at h'; simpa using h'.symm
include q
/-- Full angular participation also for each **whole sweep from a to Tilt**, REAL Eu analytic interpolation. No hypothesis of given dense interpolated field smears. Right beyond 1/2 only claiming continuous procurement using L-path and at real END/other axis of course its density. -/
lemma rises: DenseRange (A.bond C (u:ℂ)):= by
 have hu:=polar_dense (IsSelfAdjoint.of_nonneg (announceP C u e)) (reachV C u e)
 have he(x:X):peel C.l (A.bill C x)=budget A C x:= peel_inj C.l C.j (by rw [show R (R (A.bill C x))=C.angle (A.bill C x) from DFunLike.congr_fun (peel_sq C.l) (A.bill C x)]; exact (A.workout C q x).1.trans (A.prepayments C q x).1)
 have hd:DenseRange (C.Left ∘ (Y u) ∘ (budget A C)):= C.Left.surjective.denseRange.comp (hu.comp (grow _ _ C q).1 (Y u).continuous) C.Left.continuous
 apply hd.mono; rintro _ ⟨x,rfl⟩; refine ⟨x,?_⟩
 unfold bond; rw [←annuity C u e]; simp only [Function.comp_apply]; change C.Left (Y u (R (A.bill C x)))=_; rw[he]
end Organ
end YM.CrossedFrame.Cardio
