/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import GaugeFieldConstruction.Pryor
import YM.CF.Prism.Homic
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.PMOM
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 75000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open FlightFlux Fluxim
open Labels Source Source.Drops Analysis MultiNext.SignedSource Mom Pattern
open Cube
namespace Axon
local notation "GS"=> SU.group
open AnalyticBridge VerifiedReset Next.Foundations Taxi Lenten Flot
variable {n:Side} {P: BudgetPoint}{X:Scree.Hub n}{Q:InkD n}{T:tangD n}{a c:ℝ}{w m:ℕ}
open PhysicalNext.JointLoad Heir Lyre Banjo Analysis Siete
variable {b s r:ℝ}{k l:ℕ}
section
variable {F:Pane n → ℂ} (U:tangD n) {X:Hub n}(h:Chamber X P U)(V:Fin m → tangD n)(t:Fin m→ℝ)(p: m < 6)(u:∀ i:ℝ,∀ q:i∈Set.Icc (0:ℝ) 1,Signs P X.val.1 (F∘increment (increment 1 (i • U))) c)(hx:∀ x y,Agrees X.val.2 x y→ F x=F y)(hv:‖U‖ ≤ r * P.threshold)(v:∀ i,Sized (t i) (V i) P X.val.1)
-- for GE PH white. pays exact output S1.Wind.
lemma sized_short (p:‖U‖ ≤ r * P.threshold)(o:Skye.Seat n): Sized r U P o:=by
 have ht:0 ≤ r:=nonneg_of_mul_nonneg_left ((norm_nonneg _).trans p) P.threshold_pos
 refine ⟨ht,fun i=> (norm_le_pi_norm ..).trans (p.trans (mul_le_mul_of_nonneg_left ?_ ht))⟩
 unfold Lyre.width; apply le_mul_of_one_le_right P.threshold_pos.le; exact one_le_pow₀ (by simp)
include h v u hx hv p
lemma chamber_B : ‖iteratedFDeriv ℝ m (F ∘ increment 1) U V-iteratedFDeriv ℝ m (F∘ increment 1) 0 V‖ ≤ xHoch 6 * (r*∏ i,t i)*c:=by
 let T:=F∘ increment 1
 have hxU(i:ℝ)(p':i ∈Set.Icc (0:ℝ) 1):= u i p'
 have he (i) (e:i ∈ Set.Icc (0:ℝ) 1):ContDiffAt ℝ ((m+1:ℕ):ℕ∞ω) T (i • U):= (stirring 1 _ hx _ (u i e)).of_le (Nat.cast_le.mpr (le_trans p P.order_ge))
 let H:Fin (m+1)→tangD n:=Fin.cons U V; let K:=xHoch 6 *(r*∏ i,t i)*c
 have hf(i)(e:i∈Set.Icc (0:ℝ) 1):‖iteratedFDeriv ℝ (m+1) T (i • U) H‖ ≤ K:=by
    have hb(j:Fin (m+1)): Sized ((Fin.cons r t:Fin _→ℝ) j) (H j) P X.val.1:=by refine Fin.cases ?_ (fun k=> ?_) j; simpa only [H,Fin.cons_zero] using sized_short U hv _; simpa only [H, Fin.cons_succ] using v k
    have ht:= (multip 6).choose_spec.2 n X.val.2 1 P X.val.1 (i • U) F hx _ (hxU i e) (tile_c h i e) (m+1) p (le_trans p P.order_ge) H (Fin.cons r t) hb; rw [Fin.prod_univ_succ] at ht; exact ht -- tune
 let h₀ := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f:=fun t:ℝ=> iteratedFDeriv ℝ m T (t • U) V) (fun i p=> (Heir.along_deriv U V i (he _ p)).hasDerivWithinAt) (fun i e=>hf i e) (convex_Icc ..) (show (0:ℝ)∈Set.Icc (0:ℝ) 1 by simp) (show (1:ℝ)∈Set.Icc (0:ℝ) 1 by simp); simpa only [one_smul,zero_smul,sub_zero,norm_one,mul_one] using h₀
end
open Boom
section
variable {γ:E4} {l n:Side} {F:tangD n → ℂ}
variable {p:BudgetPoint} {V:tangD n} {X:Scree.Hub n}
-- prefer fixed Color hessian.GENERIC
end
section
variable {E F H:Type} [NormedAddCommGroup E][NormedSpace ℝ E] [NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup H][NormedSpace ℝ H]
-- Push.Loops.second_chain with second-regular. 
lemma second_m {f : E → F} {g : F → H} {x} (hg : ContDiffAt ℝ 2 g (f x))
    (hf : ContDiffAt ℝ 2 f x) (v w : E) :
    iteratedFDeriv ℝ 2 (g ∘ f) x ![v,w] =
      iteratedFDeriv ℝ 2 g (f x) ![fderiv ℝ f x v, fderiv ℝ f x w] +
      fderiv ℝ g (f x) (iteratedFDeriv ℝ 2 f x ![v,w]) := by
  have he : fderiv ℝ (g ∘ f) =ᶠ[𝓝 x] fun z => (fderiv ℝ g (f z)).comp (fderiv ℝ f z) := by
    filter_upwards [hf.eventually (by simp),hf.continuousAt.eventually (hg.eventually (by simp))] with z hf hg
    exact fderiv_comp z (hg.differentiableAt (by simp)) (hf.differentiableAt (by simp))
  have hf' := hf.differentiableAt (by simp)
  have hd := (hf.fderiv_right (m:=1) (by decide)).differentiableAt (by simp)
  have hg' := (hg.fderiv_right (m:=1) (by decide)).differentiableAt (by simp)
  rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply, iteratedFDeriv_two_apply, he.fderiv_eq,
    fderiv_clm_comp (show DifferentiableAt ℝ (fun z => fderiv ℝ g (f z)) x from hg'.comp x hf') hd,
    show fderiv ℝ (fun z => fderiv ℝ g (f z)) x = _ from fderiv_comp x hg' hf']
  simp [add_comm]

variable {F:tangD n} {W: E→ tangD n}
end
-- localization at flat. x any bounded period. costs with origin.Face.
variable {c₀ c₁ c₂:ℝ}{V W Z Y:tangD n} (U:PressB P X Q a c) (z:0 ≤a)
lemma local_veil {o:Skye.Seat n}(X:Finset (Skye.Seat n))(p:0 ≤ c₀)(i:tangD n)(h:∀ j,Mom.needed X j → ‖i j‖ ≤ c₀*P.threshold): Sized c₀ (Mom.screen X i) P o:=by
 refine ⟨p,fun j=>?_⟩; rw [Mom.screen_at]; split; rename_i g; · refine (h j g).trans (mul_le_mul_of_nonneg_left ?_ p); unfold Lyre.width; apply le_mul_of_one_le_right P.threshold_pos.le; exact one_le_pow₀ (by simp)
 rw [norm_zero]; exact mul_nonneg p (Lyre.width_pos ..).le
include U z
lemma censored : fderiv ℝ (term Q) 0=0:=by
 apply ContinuousLinearMap.ext; intro i; have hx(L:ℂ→L[ℝ]ℝ): L (fderiv ℝ (term Q) 0 i)=L (0:ℂ):=by
    have hd: DifferentiableAt ℝ (term Q) 0:=(eraF Q X U z 1 (ping_f P _)).paid.differentiableAt (by have hg:=P.order_ge; exact_mod_cast (by omega:¬P.order=0)) -- tune condition ne
    have he: fderiv ℝ (L ∘ term Q) 0=0:= flat_critical Thera.yet_one (cashR Q X U z L _ le_rfl).regular
    rw [fderiv_comp 0 L.differentiableAt hd,L.fderiv] at he; exact (DFunLike.congr_fun he i).trans L.map_zero.symm
 exact Complex.ext (hx Complex.reCLM) (hx Complex.imCLM)
private lemma veil2 (hV:Sized b V P X.val.1)(hW:Sized s W P X.val.1): ‖ploy Q V W‖ ≤ b*s*c:= by
 rw [ploy_iter]; let F:Fin 2→tangD n:=![V,W]; let t:Fin 2→ℝ:=![b,s]; have h:= Siete.seals (eraF Q X U z 1 (ping_f P X.val.2)) F t ((by decide:2≤6).trans P.order_ge) (fun i=>by fin_cases i; exact hV; exact hW)
 rw [show b*s=∏ i,t i from (by rw [Fin.prod_univ_two]; rfl)]; exact h
-- perturbation paying r.W through screen. no second lemma W toward F using global.Size.
lemma dark_K (v:Agrees X.val.2 V W):∀ x:tangD n,ploy Q V x= ploy Q W x := by
 intro x; have he:Agrees X.val.2 (V-W) (VerifiedReset.gradient (0:Skye.Seat n→SU.group.Color)):=by intro i p s; rw [Pi.sub_apply, v i p s, sub_self,VerifiedReset.gradient,Pi.zero_apply,Pi.zero_apply,sub_self]
 exact sub_eq_zero.mp (show ploy Q V x-ploy Q W x=0 from (by rw [←_root_.sub_apply,← map_sub]; exact ploy_nil U z _ _ _ he))
abbrev mToll (s δ:ℝ):=δ*s+(s+δ)*δ
lemma refract (hV:Sized b V P X.val.1)(hW:Sized b W P X.val.1)(p:0 ≤ s)(w:∀ j,Mom.needed X.val.2 j→ ‖V j-Z j‖≤ s*P.threshold)(u:∀ j,Mom.needed X.val.2 j→‖W j-Y j‖ ≤ s*P.threshold): ‖ploy Q V W-ploy Q Z Y‖ ≤ mToll b s *c:= by
 let T:=Mom.screen (G:=SU.group) X.val.2; have hh(t):Agrees X.val.2 t (T t):=by intro i p q; exact (show T t i=t i from (by unfold T; rw [Mom.screen_at,if_pos ⟨p,q⟩])).symm
 let F:=ploy Q
 calc
 ‖F V W-F Z Y‖=‖F (V-Z) W+F (W-Y) Z‖:=by congr 1; unfold F; simp_rw [map_sub,_root_.sub_apply]; rw [ploy_herm U z W Z,ploy_herm U z Y Z]; abel
 _≤ s*b*c+s*(b+s)*c:=by
    apply (norm_add_le ..).trans; apply add_le_add
    · unfold F; rw [dark_K U z (hh (V-Z))]; exact veil2 U z (local_veil _ p _ w) hW
    let Y':= V+T (Z-V); have hY: Agrees X.val.2 Z Y':=by
       intro i k l; unfold Y'; rw [Pi.add_apply,← hh (Z-V) i k l,Pi.sub_apply]; abel
    have hy:Sized (b+s) Y' P X.val.1:=sizedι hV (local_veil _ p _ (by intro j v; rw [Pi.sub_apply,norm_sub_rev]; exact w j v)) le_rfl
    unfold F; rw [ploy_herm U z (W-Y) Z,dark_K U z hY,ploy_herm U z Y' (W-Y), dark_K U z (hh (W-Y))]; exact veil2 U z (local_veil _ p _ u) hy
 _= _:=by unfold mToll; ring
end Axon
end YM.CF.TableF
end
