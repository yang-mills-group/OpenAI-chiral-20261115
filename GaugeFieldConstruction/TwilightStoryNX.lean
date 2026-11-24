import GaugeFieldConstruction.AsterVolumeNX
import GaugeFieldConstruction.Tropic
import GaugeFieldConstruction.Pliant
import GaugeFieldConstruction.Ethos
set_option autoImplicit false
set_option maxHeartbeats 220000
set_option maxRecDepth 5700
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
set_option linter.style.longLine false
open Function Filter Set MeasureTheory
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
namespace Spine
open Fock Analysis SlabMark MeshClock Vacancy Tapestry Etch
open Germ Alliance Lattice Py.Rate Py.Rate.LocalLimit Preparation Journey Satin Heat
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
noncomputable section
open Fock
variable (P:Spine)
open MeasureTheory
open Afterglow -- tune
local notation "Ω"=>P.floorVec
-- Alternative Porch gives linear itself for all tests fit BEntry.B.Q. Thus prove for any p.H3 and shift stamp.
variable {P}
open Papal Papal.FrameP
open CF.XGarden CF.XGarden.MastTin ArtCart
open RG Fock CF.Rush Vale Branch Fock.Flux Tapestry
open YM.Gleam BProof.PricePort Gleam.Guide Gleam.clocks
variable (P)
-- Receipt at a leaf: still uses exactly pair's heights and centers.
def ReaderVolumeNX (N:ℕ)(d:ℕ)(s m:ℕ)(S:Finset Cover)(F:Buffered.Family P.calibration)(u:ℂ):Prop:=
 let i:=P.gatePeriod m; let k:=P.gateCut m; let Y:= P.run
 ∃ (ℓ:s≤Y.uv k)(A: List (BeaconNX N)),
    A.length≤d ∧ (∀ i∈A,i.1.patio ⊆ S) ∧ filed Y P.large s i F= (fun x=> rayFNX _ A x.1) ∧ u=allotΩ Y s i k (rayVNX _ A) ℓ
lemma stringVolNX {N:ℕ}(d:ℕ)(Q: Py.Rate.LocalLimit.Badge)(t:ℕ)(u: TintDemand)(H: LicensedHeight (tagged_B Q) t u P.par)(C:ℝ→ℝ){f:ℝ}(j: RunRate 0 f C) : ∀ᶠ s in atTop,let x:= P.urnMark s
 ∀ (K: Finset Cover)(w:ℕ)(σ:Cover)(b:Axis)(i:ℤ), House P.calibration w σ 0 (plow P.calibration b i K) →σ b=0 → 0<w → (SlabMark.Etch.ratio P.calibration.B w:ℝ)≤ C x →
 ∀ (M:P.Test)(F:ℕ→Buffered.Family P.calibration), P.LongQueue K F M → ∀ (a:ℕ→ℕ), StrictMono a → ∀ (V:ℕ → ℂ)(B:ℂ), Tendsto V atTop (𝓝 B) →
 (∀ᶠ k:ℕ in atTop, P.ReaderVolumeNX N d s (a k) K (F k) (V k)) →
 ∀ z:ℂ, ‖z‖≤ KeyTurn x → ‖P.meanBox b s w (P.shifts b i (P.moneyF z B M))‖ ≤ Real.exp (KeyTurn x*ClockTurn x):=by
 filter_upwards [NovelVolumeNX P.run P.large N d Q t u H C j] with s h
 intro x S w σ b i p P₁ u W K F B a v z V ht hL d' t
 apply P.deckProof (a:=a) P₁ (B.books d' ht) u (Real.exp_pos _).le p v
 let φ:= P.Coheresγ a v
 filter_upwards [hL, φ.finance s, proscenium_at P.run P.large P.law s φ u] with n he y m
 obtain ⟨k,A,l,v₁,rA,gH⟩:=he
 let F₀:=F n; let t₁:= P.gatePeriod (a n); let t₂:=P.gateCut (a n)
 apply h t₁ t₂ k y.depth _ _ _ m W A S d' l v₁ t b i p
 rw [fileAnd,fileW,fileSub,fileW,fileOne,rA,gH]; rfl
#print axioms stringVolNX
section
variable {P}{j:Axis}{cost:ℕ→P.Test→ℂ}(R:Porch P cost j)
private lemma expSKNX (x:ℝ)(p:0≤x)(q:x≤1):Real.exp x≤ 1+2*x:=by
 have hx:‖(↑x:ℂ)‖=x:=by simp [Real.norm_of_nonneg p]
 have h:=Complex.exp_bound_sq 0 (↑x) (hx.le.trans q)
 simp only [zero_add,Complex.exp_zero,hx,norm_one,one_mul,smul_eq_mul,mul_one] at h
 rw[←Complex.ofReal_exp,←Complex.ofReal_one,←Complex.ofReal_sub, ←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at h
 have e:=(le_abs_self _).trans h
 nlinarith only [mul_nonneg (show 0≤1-x from sub_nonneg.mpr q) p,e]
private lemma dinChx (z:ℂ) (x e:ℝ)(t:0<x)(p:0<e)(q:x*e≤1) (h:∀ w:ℂ, ‖w‖≤x→‖1+w*z‖≤Real.exp (x*e)): ‖z‖≤ 2*e:=by
 by_cases u:z=0; · rw[u,norm_zero]; positivity
 let w:ℂ:=(↑(x*‖z‖))/z
 have he:w*z= (x*‖z‖:ℝ):= div_mul_cancel₀ _ u
 have ht:0< x*‖z‖:=mul_pos t (norm_pos_iff.mpr u)
 have hw:‖w‖=x:= by apply mul_right_cancel₀ (norm_pos_iff.mpr u).ne'; rw [← norm_mul,he,Complex.norm_real,Real.norm_of_nonneg ht.le]
 have h':= (h w hw.le).trans (expSKNX _ (mul_pos t p).le q)
 rw [he,←Complex.ofReal_one, ←Complex.ofReal_add, Complex.norm_real, Real.norm_of_nonneg (by positivity)] at h'
 apply le_of_mul_le_mul_left _ t; linarith only [h']

lemma TwilightStoryNX {N:ℕ}(d:ℕ)(Q: Py.Rate.LocalLimit.Badge)(t:ℕ)(u: TintDemand)(H: LicensedHeight (tagged_B Q) t u P.par)(C:ℝ→ℝ){f:ℝ}(q: RunRate 0 f C) : ∀ᶠ s in atTop,let x:= P.urnMark s
 ∀ (K: Finset Cover)(w:ℕ)(σ:Cover)(j:Axis)(i:ℤ), House P.calibration w σ 0 (plow P.calibration j i K) →σ j=0 → 0<w → (SlabMark.Etch.ratio P.calibration.B w:ℝ)≤ C x →
 ∀ (M:P.Test)(F:ℕ→Buffered.Family P.calibration), P.LongQueue K F M → ∀ (a:ℕ→ℕ), StrictMono a → ∀ (V:ℕ → ℂ)(B:ℂ), Tendsto V atTop (𝓝 B) →
 (∀ᶠ k:ℕ in atTop, P.ReaderVolumeNX N d s (a k) K (F k) (V k)) →
 ∀ cost:ℕ→P.Test→ℂ, Porch P cost j → ‖cost s M-B‖ ≤2*ClockTurn x :=by
 have hz: RunRate (-callE/2+-callE/16) 0 (fun x=> KeyTurn x*ClockTurn x):= by rw[← add_zero (0:ℝ)]; exact (show RunRate (-callE/2) 0 KeyTurn from RunRate.coins ..).mul (show RunRate (-callE/16) 0 ClockTurn from RunRate.coins ..)
 have he:∀ᶠ s:ℕ in atTop, KeyTurn (P.urnMark s)*ClockTurn (P.urnMark s)≤1:= (Py.Rate.LocalLimit.turnover P.par).eventually ((hz.tends (Or.inl (by norm_num [callE,gratuity]))).eventually (ge_mem_nhds zero_lt_one))
 filter_upwards [P.stringVolNX d Q t u H C q, he] with s h he
 intro x K w σ j i y ℓ t a M F r m v f B H T' C P'
 have H':=P.PositionedPrice ℓ y r.bayΛ t
 exact dinChx _ _ _ (BProof.coin_pos ..) (BProof.coin_pos ..) he (fun z p=> (cashle P' H' z B).trans (h K w σ j i y ℓ t a M F r m v f B H T' z p))
end
#print axioms TwilightStoryNX
end
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
