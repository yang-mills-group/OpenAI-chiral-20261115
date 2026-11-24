import YM.CF.Vow.Jig
import YM.CF.DPress.Fees.Note
import YM.CF.Vow.Goal
import YM.CF.Mew.Pot
/-! Clock stencils and JetDu.§D. `Groom` away from support indicates direct/general. -/
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.DPress.Fees
open Function Lattice MeasureTheory Filter Metric Analytic Finset
open Lat Cube RG Fock Pastry Skye Scree Vow Mew Jet Hake
open scoped Topology Classical BigOperators ContDiff Matrix Matrix.Norms.L2Operator YM.CF.Mew
attribute [local instance] opCStarAlgebra
variable {I:Type*}{n:Side}{P:BudgetPoint} {N p:ℕ}{a L:ℝ}{e:Seat n}{S t:Support (More n)}
variable {A:Type}[NormedAddCommGroup A][NormedSpace ℝ A][FiniteDimensional ℝ A]
namespace JetRead
abbrev FT(j:ℕ)(x:A→ℂ) := iteratedFDeriv ℝ j x 0 -- Root
abbrev lookP(j:ℕ)(k:Fin j→A)(x:A→ℂ):ℂ:= FT j x k / (↑(∏ i, ‖k i‖):ℂ)
private lemma ζFT(j:ℕ)(k:Fin j→ A)(x:A→ℂ): ‖lookP j k x‖*(∏ i,‖k i‖)= ‖FT j x k‖:=by
 unfold lookP; rw [norm_div, Complex.norm_real,Real.norm_of_nonneg (prod_nonneg (fun _ _=>norm_nonneg _))]; by_cases h:(∏ i,‖k i‖)=0; rw [h,mul_zero]; have hp:= (FT j x).le_opNorm k; rw [h,mul_zero] at hp; exact le_antisymm (norm_nonneg _) hp
 field_simp
abbrev launch(j:ℕ): Dial (A→ℂ):= Set.range (fun k=>lookP (A:=A) j k) -- maybe unused placeholder? ensure
lemma launchQ (f:A→ℂ)(j:ℕ): Budget (launch j) f a↔ 0≤a ∧ ‖FT j f‖≤ a:=by
 constructor; intro p; refine ⟨p.p, ContinuousMultilinearMap.opNorm_le_bound p.p (fun i=>?_)⟩; rw [← ζFT]; exact mul_le_mul_of_nonneg_right (p.t (lookP j i) ⟨i,rfl⟩) (Finset.prod_nonneg fun _ _=> norm_nonneg _) -- tune CLM args
 rintro ⟨k,z⟩; refine ⟨k,?_⟩; rintro i ⟨i,rfl⟩; have hp:= prod_nonneg (s:=univ) (fun j _=>norm_nonneg (i j)); rcases hp.eq_or_lt with h|h; simp_rw [lookP,← h,Complex.ofReal_zero,div_zero,norm_zero]; exact k
 exact le_of_mul_le_mul_right ((ζFT ..).le.trans (ContinuousMultilinearMap.le_of_opNorm_le z i)) h
abbrev Launch(p:ℕ): Dial (A→ℂ):= staff launch (fun j=>(1:ℝ)^j/(j.factorial:ℝ)) (range (p+1))
lemma LaunchQ(p:ℕ)(x:A→ℂ): Budget (Launch p) x a↔ potash 1 p x 0≤a:=by
 have ht (j:ℕ): Budget (launch j) x ‖FT j x‖:= (launchQ x j).2 ⟨norm_nonneg _,le_rfl⟩
 let G(j:ℕ):=(1:ℝ)^j/(j.factorial:ℝ)
 let T:= range (p+1)
 have hp(j:ℕ)(_ : j ∈ T):0≤ G j:=by unfold G; positivity
 let V(j:ℕ):=launch (A:=A) j
 let C (j:ℕ) := ‖FT j x‖
 let Z (j:ℕ) := meter (V j) x
 have h (j:ℕ): Live (V j) x:=⟨C j,ht j⟩
 have hc(j:ℕ): C j ≤ Z j:= (launchQ x j|>.1 (Live.pays (h j))).2
 constructor; intro f; refine le_trans (b:=∑ i∈T,G i* Z i) ?_ (staff_due V G hp f (fun i _=> h i)); change (∑ i∈ T,G i*C i)≤_; gcongr
 next=> exact hc _
 intro f; exact (staff_up V G hp C (fun i _=>ht i)).up f
abbrev loft (P:BudgetPoint)(e:Seat n): Dial (tangD n → ℂ):= {h|∃ (p:ℕ),p≤P.order ∧ ∃ (k:Fin p→tangD n),(∀ i,P.dirBound e (k i))∧ h=fun x=>iteratedFDeriv ℝ p x 0 k}
lemma loftQ(f:tangD n→ℂ)(h:ContDiffAt ℝ (↑P.order:WithTop ℕ∞) f 0): Signs P e f a↔ Budget (loft P e) f a:=by
 constructor; intro v; exact ⟨v.grade,fun i ⟨p,w,k,u,t⟩=> t.symm ▸ v.token _ w _ u⟩; intro v; exact ⟨v.p,h,fun i g k u=> v.t (fun f=>iteratedFDeriv ℝ i f 0 k) ⟨i,g,k,u,rfl⟩⟩
-- brings.S vector via pricing functions at arbitrary Qual.
lemma humble (L:ℝ) (p:ℕ) (x:ℂ→A→ℂ)(e:1<L)(g:tend L x p)(t:∀ᶠ i in 𝓝 (0:A),DifferentiableOn ℂ (fun z=>x z i) (ank L)): Brings L x (x 1-x 0) (Launch p):=by
 apply Brings.stage; intro i a; rintro _ ⟨k,rfl⟩; let c:= (↑(∏ i, ‖k i‖):ℂ)⁻¹; let Z:= Analytic.diffClock p L x g t i (Nat.le_of_lt_succ (mem_range.mp a)) k e; unfold Function.comp; simp_rw [lookP,div_eq_mul_inv,mul_comm (FT _ _ k)]; exact Disc.scale c Z -- tune simp composition at z
lemma humL (L:ℝ) (x:ℂ→tangD n→ℂ)(e0:1<L)(g:tend L x P.order)(t:∀ᶠ i in 𝓝 (0:tangD n),DifferentiableOn ℂ (fun z=>x z i) (ank L)): Brings L x (x 1-x 0) (loft P e) :=by rintro u ⟨j,p,k,g',rfl⟩; exact Analytic.diffClock _ _ _ g t j p k e0
section orbit
-- recenter projected or scaled.P coordinates. uniform qualitative threshold.C.F.
abbrev sting(P:BudgetPoint)(t:Support (More n))(U: Pane n)(i:tangD n):= increment U (openG P t i)
lemma stingQ(P:BudgetPoint)(t:Support (More n))(U:Pane n)(i:tangD n): sting P t U i= pressQ P t U (P.threshold⁻¹ • i):=by unfold sting pressQ; rw [smul_inv_smul₀ P.threshold_pos.ne', Rill.padP]; rfl
lemma interest' (U:Pane n)(v:tangD n): sting P ∅ U v=increment U v:= by unfold sting; rw [show openG P ∅ v= v from funext fun i=> by simp [openG,Lattice.halo]]
variable {U:Pane n}{x:ℂ→Pane n→ℂ}
variable (f: pingS P.threshold S U)(g:∀ i:Pane n,pingS P.threshold S i → DifferentiableOn ℂ (fun z=> x z i) (ank L))
lemma coast(v:tangD n): pressQ P t U v= sting P t U (P.threshold • v):=by rw [stingQ,inv_smul_smul₀ P.threshold_pos.ne']
include f g
lemma merit (c:∀ z∈ank L,∀ i:Pane n,pingS P.threshold S i→ Pence P.order (x z ∘ pressQ P t i) 0 a)(v:1<L): Brings L (fun z=> x z ∘ pressQ P t U) (x 1∘ pressQ P t U - x 0 ∘ pressQ P t U) (Launch P.order):=by
 obtain ⟨C,k,h⟩:= reach_p (Y:=t) (X:=S) (D:=∅) (P:=P) (U:=U) (by rwa [sdiff_empty]); apply humble _ _ _ v ⟨C*a,h.mono fun i p z w=> p (x z) a (fun i t=>c z w i (by rwa [sdiff_empty] at t))⟩; filter_upwards [Vow.tick (X:=S) (D:=∅) (Y:=t) (P:=P) (U:=U) (by rwa [sdiff_empty])] with i p; rw [sdiff_empty] at p; exact g _ p -- tune syntax star comp
lemma coal (c:∀ z∈ank L,∀ i:Pane n,pingS P.threshold S i→ Signs P e (x z ∘ sting P t i) a)(v:1<L): Brings L (fun z=> x z ∘ sting P t U) (x 1∘ sting P t U - x 0 ∘ sting P t U) (loft P e):=by -- want commerce via results; signs from scaled transform for recentered uniform around 0 using yacht proof variant or algebra transport via norm map derivative $Consent.H_x.At zero`; represent jets exactly via derivative scalar factor from alternative charts. Use Disc.sub mapRes.K.
 let θ:=P.threshold; have pθ:0<θ:= P.threshold_pos; let U₀:=tangD n; let T:=ContinuousLinearMap.id ℝ U₀; let Z':=θ⁻¹ • T; let A(z:ℂ):=x z ∘ pressQ P t U; let B(z:ℂ):=x z ∘ sting P t U; have cb(z:ℂ):B z=A z∘Z':=funext fun i=> congrArg (x z) (stingQ _ _ _ _)
 let m:= P.order; let d(z:ℂ)(p:z∈ank L)(i)(w:pingS P.threshold S i) := (pins (le_refl t) (c z p i w)); obtain ⟨C,k,h⟩:= reach_p (Y:=t) (X:=S) (D:=∅) (P:=P) (U:=U) (by rwa [sdiff_empty]); have c' : tend L A m:=by
    let r:ℝ:= (m+1:ℝ)*composeCost m a 1; refine ⟨C*r, h.mono fun i tp z p=>?_⟩; refine tp _ _ ?_; intro W c; rw [sdiff_empty] at c; exact Rue.bare_p _ _ (d z p W c) -- tune `pins` application
 have ht:∀ᶠ i in 𝓝 (0:U₀),DifferentiableOn ℂ (fun z=>A z i) (ank L):=(Vow.tick (X:=S) (D:=∅) (Y:=t) (P:=P) (U:=U) (by rwa [sdiff_empty])).mono (fun i c=> g _ (by rwa [sdiff_empty] at c)); apply humL _ _ v _ _; ·
    obtain ⟨C,h⟩:=c'; let D:= ‖Z'‖+1; have hv: Tendsto Z' (𝓝 0) (𝓝 0):= by simpa only [map_zero] using Z'.continuous.tendsto 0
    refine ⟨composeCost m C D,?_⟩; filter_upwards [hv.eventually h, hv.eventually (Metric.ball_mem_nhds (0:U₀) (by norm_num : (0:ℝ)<1))] with i p q -- tune gt
    intro z l; change Allows m (B z) _ _; rw [cb z]; exact (p z l).comp (allows_linear (by unfold D; linarith) ((mem_ball_zero_iff.mp q).le.trans (le_add_of_nonneg_left (norm_nonneg _))))
 have hv:Tendsto Z' (𝓝 0) (𝓝 0):= by simpa only [map_zero] using Z'.continuous.tendsto 0
 filter_upwards [hv.eventually ht] with i p; change DifferentiableOn ℂ (fun z=>B z i) _; simp_rw [cb]; exact p
end orbit
end JetRead
end YM.CF.DPress.Fees
