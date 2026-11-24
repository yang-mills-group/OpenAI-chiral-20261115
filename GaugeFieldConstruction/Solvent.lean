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
abbrev urnMark (P:Spine)(s:ℕ):= hat P.par.R.L P.par.x s
abbrev gatePeriod (P:Spine)(u:ℕ):=P.period (P.projection.rows u)
abbrev gateCut (P:Spine)(u:ℕ):=P.cutoff (P.projection.columns u)
variable (P)
-- Receipt at a leaf: still uses exactly pair's heights and centers.
def ReaderProof (N:Side)(d:ℕ)(r:ℝ)(s m:ℕ)(S:Finset Cover)(F:Buffered.Family P.calibration)(u:ℂ):Prop:=
 let i:=P.gatePeriod m; let k:=P.gateCut m; let Y:= P.run
 ∃ (ℓ:s≤Y.uv k)(A: List AdmitA)(p:BudgetPoint)(M₁:Tulip.Male),
    p.order≤6∧ p.power≤3 ∧ p.threshold=(Papal.gram Y s i k).p.threshold ∧
    ReaderShip _ A d r (Satin.region S (Papal.count Y s i)) ∧ filed Y P.large s i F= (fun x=> Uranus Y s i k N A p M₁ x.1) ∧ u=allotΩ Y s i k (headPlus Y s i N A p M₁) ℓ
lemma PositionedPrice {w:ℕ}{F:P.Test}{x:ℤ}{j:Axis}{σ:Cover}{S: Finset Cover}(v:σ j=0)(h:House P.calibration w σ 0 (plow P.calibration j x S))(u:F∈bay P.calibration S true)(p:0<w): P.BEntry j w (P.shifts j x F):= by
 refine ⟨p,_,P.shifts_support j x _ u,?_⟩
 have ht:=h j; unfold runnel at ht; rw [v] at ht; simp at ht; exact ht
lemma deckProof {N:ℕ}{c:ℝ}{f:P.Test}{s:ℕ}{x:ℤ}{j:Axis}{σ:Cover}{S:Finset Cover}{F:ℕ→Buffered.Family P.calibration}{a:ℕ→ℕ} (w:σ j=0)(h:P.LongQueue S F f)(u:0<N)(m:0≤c)(g:House P.calibration (N:ℤ) σ 0 (plow P.calibration j x S))(v: StrictMono a)
    (p:∀ᶠ n:ℕ in atTop, Mosaic (N:ℤ) σ (slideN P.run s N (P.gatePeriod (a n))) (relocate P.calibration j x (F n)) c (Journey.sharp P.run P.large s (P.gatePeriod (a n)) (P.gateCut (a n)))):
    ‖P.meanBox j s N (P.shifts j x f)‖≤ c:=by
 let t:=P.PositionedPrice w g h.bayΛ u; rw[meanBox_eq s t]
 let π:=P.Coheresγ a v
 have hp:=BQueue.station j x h
 refine premiereBox P.run P.large P.law s π j N σ u w _ g P.history P.projection.clipped false (P.room j) (t.card s) hp c m (fun q h=>?_)
 apply p.mono; intro n hv X A B q' r F G; apply (hv X A B q' r F G).trans; exact pow_le_pow_left₀ m h.le _
-- `χ` aperture
abbrev moneyF (z u:ℂ)(F:P.Test):= 1+ z •(F-u •1)
lemma stringCosts {N:Side}(nw:300<N.val)(d:ℕ)(r:ℝ)(g:0≤r)(Q: Py.Rate.LocalLimit.Badge)(t:ℕ)(u: TintDemand)(H: LicensedHeight (tagged_B Q) t u P.par)(C:ℝ→ℝ){f:ℝ}(j: RunRate 0 f C) : ∀ᶠ s in atTop,let x:= P.urnMark s
 ∀ (K: Finset Cover)(w:ℕ)(σ:Cover)(b:Axis)(i:ℤ), House P.calibration w σ 0 (plow P.calibration b i K) →σ b=0 → 0<w → (SlabMark.Etch.ratio P.calibration.B w:ℝ)≤ C x →
 ∀ (M:P.Test)(F:ℕ→Buffered.Family P.calibration), P.LongQueue K F M → ∀ (a:ℕ→ℕ), StrictMono a → ∀ (V:ℕ → ℂ)(B:ℂ), Tendsto V atTop (𝓝 B) →
 (∀ᶠ k:ℕ in atTop, P.ReaderProof N d r s (a k) K (F k) (V k)) →
 ∀ z:ℂ, ‖z‖≤ KeyTurn x → ‖P.meanBox b s w (P.shifts b i (P.moneyF z B M))‖ ≤ Real.exp (KeyTurn x*ClockTurn x):=by
 filter_upwards [NovelGreen P.run P.large N nw d r g Q t u H C j] with s h
 intro x S w σ b i p P₁ u W K F B a v z V ht hL d' t
 apply P.deckProof (a:=a) P₁ (B.books d' ht) u (Real.exp_pos _).le p v
 let φ:= P.Coheresγ a v
 filter_upwards [hL, φ.finance s, proscenium_at P.run P.large P.law s φ u] with n he y m
 obtain ⟨k,A,Z,M₁,l,p₀,q',v₁,rA,gH⟩:=he
 let F₀:=F n; let t₁:= P.gatePeriod (a n); let t₂:=P.gateCut (a n)
 apply h t₁ t₂ k y.depth _ _ _ m W M₁ Z l p₀ q' A S d' v₁ t b i p
 rw [fileAnd,fileW,fileSub,fileW,fileOne,rA,gH]; rfl
#print axioms stringCosts
section
variable {P}{j:Axis}{cost:ℕ→P.Test→ℂ}(R:Porch P cost j)
include R in
lemma cashle {w:ℕ}{s:ℕ}{x:ℤ}{F:P.Test} (p:P.BEntry j w (P.shifts j x F)) (z u:ℂ):
   ‖1+z*(cost s F-u)‖≤‖P.meanBox j s w (P.shifts j x (P.moneyF z u F))‖:=by
 let G:=P.shifts j x F
 have h:P.shifts j x (P.moneyF z u F)=P.moneyF z u G:=by unfold moneyF G; simp
 have hp:=BEntry.one P j p.pos; have hx:P.BEntry j w (P.moneyF z u G):=hp.add ((p.sub (hp.smul u)).smul z)
 have he: inner ℂ R.Ω (R.ρ (P.HabBox j s w 1) R.Ω)=1:=by
    rw[HabBox_one s P j p.pos,R.still, inner_self_eq_norm_sq_to_K,R.normΩ]; simp
 rw [h, ← R.axSym s x F,←R.expense p, show 1+z*( _-u) = cost s (P.moneyF z u G) from ?_]
 · exact Porch.plot_le R hx
 rw [←R.expense hx]; unfold moneyF
 rw[HabBox_add s hp ((p.sub (hp.smul u)).smul z),HabBox_smul s (p.sub (hp.smul u)) z, HabBox_sub s p (hp.smul u),HabBox_smul s hp u,map_add,map_smul,map_sub,map_smul]
 simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.sub_apply,inner_add_right,inner_sub_right,inner_smul_right,he, smul_eq_mul,mul_one]

private lemma expS (x:ℝ)(p:0≤x)(q:x≤1):Real.exp x≤ 1+2*x:=by
 have hx:‖(↑x:ℂ)‖=x:=by simp [Real.norm_of_nonneg p]
 have h:=Complex.exp_bound_sq 0 (↑x) (hx.le.trans q)
 simp only [zero_add,Complex.exp_zero,hx,norm_one,one_mul,smul_eq_mul,mul_one] at h
 rw[←Complex.ofReal_exp,←Complex.ofReal_one,←Complex.ofReal_sub, ←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at h
 have e:=(le_abs_self _).trans h
 nlinarith only [mul_nonneg (show 0≤1-x from sub_nonneg.mpr q) p,e]
private lemma din (z:ℂ) (x e:ℝ)(t:0<x)(p:0<e)(q:x*e≤1) (h:∀ w:ℂ, ‖w‖≤x→‖1+w*z‖≤Real.exp (x*e)): ‖z‖≤ 2*e:=by
 by_cases u:z=0; · rw[u,norm_zero]; positivity
 let w:ℂ:=(↑(x*‖z‖))/z
 have he:w*z= (x*‖z‖:ℝ):= div_mul_cancel₀ _ u
 have ht:0< x*‖z‖:=mul_pos t (norm_pos_iff.mpr u)
 have hw:‖w‖=x:= by apply mul_right_cancel₀ (norm_pos_iff.mpr u).ne'; rw [← norm_mul,he,Complex.norm_real,Real.norm_of_nonneg ht.le]
 have h':= (h w hw.le).trans (expS _ (mul_pos t p).le q)
 rw [he,←Complex.ofReal_one, ←Complex.ofReal_add, Complex.norm_real, Real.norm_of_nonneg (by positivity)] at h'
 apply le_of_mul_le_mul_left _ t; linarith only [h']

lemma Storytold {N:Side}(nw:300<N.val)(d:ℕ)(r:ℝ)(g:0≤r)(Q: Py.Rate.LocalLimit.Badge)(t:ℕ)(u: TintDemand)(H: LicensedHeight (tagged_B Q) t u P.par)(C:ℝ→ℝ){f:ℝ}(q: RunRate 0 f C) : ∀ᶠ s in atTop,let x:= P.urnMark s
 ∀ (K: Finset Cover)(w:ℕ)(σ:Cover)(j:Axis)(i:ℤ), House P.calibration w σ 0 (plow P.calibration j i K) →σ j=0 → 0<w → (SlabMark.Etch.ratio P.calibration.B w:ℝ)≤ C x →
 ∀ (M:P.Test)(F:ℕ→Buffered.Family P.calibration), P.LongQueue K F M → ∀ (a:ℕ→ℕ), StrictMono a → ∀ (V:ℕ → ℂ)(B:ℂ), Tendsto V atTop (𝓝 B) →
 (∀ᶠ k:ℕ in atTop, P.ReaderProof N d r s (a k) K (F k) (V k)) →
 ∀ cost:ℕ→P.Test→ℂ, Porch P cost j → ‖cost s M-B‖ ≤2*ClockTurn x :=by
 have hz: RunRate (-callE/2+-callE/16) 0 (fun x=> KeyTurn x*ClockTurn x):= by rw[← add_zero (0:ℝ)]; exact (show RunRate (-callE/2) 0 KeyTurn from RunRate.coins ..).mul (show RunRate (-callE/16) 0 ClockTurn from RunRate.coins ..)
 have he:∀ᶠ s:ℕ in atTop, KeyTurn (P.urnMark s)*ClockTurn (P.urnMark s)≤1:= (Py.Rate.LocalLimit.turnover P.par).eventually ((hz.tends (Or.inl (by norm_num [callE,gratuity]))).eventually (ge_mem_nhds zero_lt_one))
 filter_upwards [P.stringCosts nw d r g Q t u H C q, he] with s h he
 intro x K w σ j i y ℓ t a M F r m v f B H T' C P'
 have H':=P.PositionedPrice ℓ y r.bayΛ t
 exact din _ _ _ (BProof.coin_pos ..) (BProof.coin_pos ..) he (fun z p=> (cashle P' H' z B).trans (h K w σ j i y ℓ t a M F r m v f B H T' z p))
end
#print axioms Storytold
end
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
