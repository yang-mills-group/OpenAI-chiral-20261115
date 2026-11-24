import YM.SU5.FiniteGaugeData.Poin.Paste
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
open Filter Function Set OS OS.Semigroup Mink Mink.General Mink.Lorentz Complex Flute MeasureTheory Boundary Probe
open scoped Topology ContDiff NNReal InnerProductSpace
local notation "tt"=>timeAxis
variable {H:Hilbert}{α:Type}(M':Canopy H α)(S: OS.Semigroup H timeAxis)(Ω:Bench S)(hΩ:∀ z:E4,M S z Ω.val=Ω.val)
variable {n:ℕ} (p q:Mink.Poincare)
namespace Canopy
variable (t u:M'.Token)(chip:M'.Chip)(g:Test4)(w:List M'.Token)
local notation "D"=>Bench S
open Submodule
local notation "L"=> M'.Climb S Ω
local notation "H₀"=> Hatch M' S Ω
local notation "R"=> saucer S
variable (n:ℕ)(y x:Bench S)
-- local duplicate `zProj`? previous local instance imported def but not active. new.
local instance : CompleteSpace (M'.Climb S Ω):= isClosed_closure.completeSpace_coe
lemma Rp_alt(i:H): (1-H₀ :H.Op) i ∈ Lᗮ:= sub_starProjection_mem_orthogonal i
lemma hatch_adj : IsSelfAdjoint (Hatch M' S Ω):= isSelfAdjoint_starProjection _
-- Cash.W.k. Comm preserve.Bench.
omit hΩ in
lemma oracle (f:E4→ ℂ)(p:Continuous f)(h:∀ g:Test4,(∫ x,g x *f x)=0): f=(fun _=>0):=by
 apply Measure.eq_of_ae_eq (μ:=volume) _ p continuous_const; apply ae_eq_zero_of_integral_contDiff_smul_eq_zero p.locallyIntegrable; intro g hg hex; let G:= Complex.ofRealCLM; have e:ContDiff ℝ ∞ (G ∘ g):= G.contDiff.comp hg; let F:Test4:= (hex.comp_left (show G 0=0 from G.map_zero)).toSchwartzMap e
 apply Eq.trans ?_ (h F); refine integral_congr_ae (Eventually.of_forall fun x=>?_); exact Complex.real_smul
include hΩ
local notation "J"=> H₀
local notation "P"=> M'.dep chip
local notation "ν"=>M'.grade chip
local notation "K"=>Cache S
lemma dark : Commute R (1-(M'.Hatch S Ω)):= (Commute.one_right _).sub_right (r_cap M' S Ω hΩ)
lemma fade : (Hatch M' S Ω)*(M'.dep chip)*(1-Hatch M' S Ω)=0:=by
 let T:H.Op:= J*P*(1-J); let Y:=(1-J :H.Op); let V:Bench S→H:= Subtype.val; have hv:DenseRange V:= by unfold DenseRange V; rw [Subtype.range_val]; exact bench_warm S
 apply DFunLike.coe_injective; apply hv.equalizer T.continuous (ContinuousLinearMap.continuous _); funext y; apply hv.eq_of_inner_right ℂ; intro x; let x':= park S J (autumn S _ (r_cap M' S Ω hΩ).symm) x; let y':= park S Y (autumn S _ (dark M' S Ω hΩ).symm) y; -- defeq. t:t placeholder.not expected.
 let A:=park S (K ν) (autumn S _ ((Commute.refl R).pow_left _)); have hh: (A x').val∈ L:= by rw [show (A x').val= J (K ν x.val) from DFunLike.congr_fun ((r_cap M' S Ω hΩ).pow_left ν).eq x.val]; apply starProjection_apply_mem
 have ht: (A y').val ∈ Lᗮ:=by rw [show (A y').val= Y (K ν y.val) from DFunLike.congr_fun ((dark M' S Ω hΩ).pow_left ν).eq y.val]; exact Rp_alt M' S Ω (K ν y.val)
 have he(f:Test4): (∫ i,f i * lucent S x'.val y'.val P i)=0:=by
    let w:= (chip,f); have e':= inner_right_of_mem_orthogonal hh (respects M' S Ω w (A y') ht); rw [horizon, assizes] at e'; exact (Subtype.ext_iff.mp (cache_park S x' ν)) ▸ (Subtype.ext_iff.mp (cache_park S y' ν)) ▸ e'
 have hp:inner ℂ x'.val (P y'.val)=0:=by
    rw [← show optx S P (0:E4)= P from vroot ..]; exact congrFun (oracle _ (show Continuous (lucent S x'.val y'.val P) from continuous_const.inner (village ..)) he) 0
 change inner ℂ _ (J _)= inner ℂ _ ((0:H.Op) _); rw [← ContinuousLinearMap.adjoint_inner_left J,show (J).adjoint=J from hatch_adj ..]; exact Eq.trans hp (by simp)
#print axioms oracle
lemma symphonyP (chip:M'.Chip): Commute (M'.dep chip) (Hatch M' S Ω):=by
 -- fix shadow P notation: expand or remove
 let A':=M'.dep chip; let X:=M'.Hatch S Ω; let Y:H.Op:=1-X; have hv: X*A'*Y=0:=fade M' S Ω hΩ chip; have h:= congrArg star (fade M' S Ω hΩ (M'.mirrorK chip)); change star (X*M'.dep (M'.mirrorK chip)*Y) = star (0:H.Op) at h -- errone at h need at h
 rw [star_mul,star_mul,spar,star_star,show star X=X from hatch_adj ..,show star Y=Y from (show IsSelfAdjoint Y from (show IsSelfAdjoint (1:H.Op) from star_one _).sub (hatch_adj ..)), star_zero,←mul_assoc] at h; unfold Y at h hv; rw [sub_mul,one_mul, sub_mul, mul_assoc X A' X] at h; rw [mul_sub,mul_one,mul_assoc X A' X] at hv; exact (sub_eq_zero.mp h).trans (sub_eq_zero.mp hv).symm
#print axioms fade
-- Kernel flashlight reducing Eu criterion.TO falsify via approximate moments.S.Static. Use ONLY as intermediate! needs actual invoice
structure Pierces :Prop where
 aims (Q:H.Op) (_:IsIdempotentElem Q) (_: IsSelfAdjoint Q)
      (p:Commute (saucer S) Q) (z:∀ t,Commute (S.E t) Q)
      (e: ∀ t,Commute (S.U t) Q) (h: Q Ω.val=Ω.val) (_:∀ chip,Commute (M'.dep chip) Q): Q=1
theorem fullCanopy (p:M'.Pierces S Ω): Climb M' S Ω=⊤:=by
 apply eq_top_iff.mpr; intro x _; apply starProjection_eq_self_iff.mp; change J x=x; rw [p.aims (Hatch M' S Ω) (isIdempotentElem_starProjection _) (hatch_adj M' S Ω) (r_cap M' S Ω hΩ) (heat_P M' S Ω hΩ) (fun t=>by rw [← laneslot]; exact stock M' S Ω hΩ t.val) (carp M' S Ω) (symphonyP M' S Ω hΩ)]; rfl
#print axioms fullCanopy
end Canopy
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
