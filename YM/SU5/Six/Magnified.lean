import YM.SU5.Six.Momentum
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import YM.SU5.Six.ChamberCosts
import YM.SU5.Six.ReachDoors
import YM.SU5.Six.Charges
import YM.SU5.Six.Rates
import YM.SU5.Six.Elected
import YM.SU5.Six.MSplit
import YM.SU5.Aria.Grotto
import YM.SU5.Six.KeepCharge
import YM.SU5.Six.MirrorCharge
set_option maxHeartbeats 200000
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Set
open Cheer (Narrow)

/-!
# Spectral response in the six-body mirror measurement

Radian Fourier transform applied only on the priced pose units.
Diagonal V cost on THIS representation and character, all ballots qualify
simultaneously. Matrix statements in usual PSD order and are not uniform in i.
No mass-gap/global forward-cone hypothesis.
-/
open Casting
open Spectral Caino
open Spectral.Orbit.Prairie
open Score
open FrameBound
section abstract
variable (F:SampleDose)(b:ℝ≥0)(X:Hilbert)(S:OS.Semigroup X (3:Axis))
private abbrev pickCost (y:X):X:=∫ p:Vantage,Score.spark X S F.val posse birthClock b y p
local notation "Ψ"=>pickCost F b X S
local notation "μ"=> S.ℚmeasure.diagonal
local notation "Γ"=> S.ℚmeasure.region
private lemma all_bound (y:X): Integrable (Score.spark X S F.val posse birthClock b y):=Score.spark_ready X S F.val F.smooth.continuous F.budget _ posse_cont _ clockFare b _
private lemma pick_plus (y x:X): Ψ (y+x)=Ψ y+Ψ x:=by
 unfold pickCost; rw [←integral_add (all_bound F b X S y) (all_bound F b X S x)] -- ellipsis bad
 apply integral_congr_ae (Eventually.of_forall fun i=>?_); simp only [Score.spark,map_add]; rw [show y+x-(S.E b y+S.E b x) =y-S.E b y+(x-S.E b x) from by abel]; rw [map_add,map_add,smul_add]
private def rolesBeam : X.space→ₗ[ℂ] X.space where
 toFun:= pickCost F b X S
 map_add':=pick_plus F b X S
 map_smul':= by
   intro c x; unfold pickCost; rw [← integral_smul]; refine integral_congr_ae (Eventually.of_forall fun i=>?_)
   unfold Score.spark; dsimp only; rw [map_smul, ← smul_sub,map_smul,map_smul,smul_comm]; rfl -- tune
private lemma voidable (x:X): Γ {p:E4| YM.time p=0} (Ψ x)=0:= by
 let Z:= {p:E4| YM.time p=0}; let Q:= Γ Z; let f:=Score.spark X S F.val posse birthClock b x
 have hz:MeasurableSet Z:= Mink.clock_cont.measurable (measurableSet_singleton _)
 have he(i:Vantage): Q (f i)=0:=by
    unfold f Q Score.spark
    rw [map_smul,inside_lens X S hz,drops_vac,map_zero,map_zero,smul_zero]
 have ht: Γ Z (Ψ x)=∫ p,Q (f p):= ((Q.restrictScalars ℝ).integral_comp_comm (all_bound ..)).symm
 rw [ht]; simp_rw [he]; simp
private lemma wake (W:Set E4)(w:MeasurableSet W)(x:X): Γ W (Ψ x)=Ψ (Γ W x):= consult X S F.val F.smooth.continuous F.budget posse posse_cont birthClock clockFare b x w
private lemma kills (W:Set E4)(w:MeasurableSet W)(x:X)(v: Γ W (Ψ x)=0)
    (h: ∀ᵐ p∂μ (Γ W x), (∫ z:Vantage,Score.gain F.val posse birthClock b z p)≠0) : Γ W x=0:= by
  let y:= Γ W x; let f(p:E4):ℝ:=‖∫ z:Vantage,gain F.val posse birthClock b z p‖^2
  obtain ⟨e,g⟩:= Score.consigned X S F.val F.smooth.continuous F.budget posse posse_cont birthClock clockFare b y
  by_contra t
  have he : (μ y) Set.univ ≠0:=by intro h; exact t (show y=0 from Eq.trans (show y=S.ℚmeasure.region Set.univ y from by rw [S.ℚmeasure.all]; rfl) (((S.ℚmeasure).null_pair MeasurableSet.univ y).1 h))
  haveI : NeZero (μ y):= ⟨fun e=>he (by rw [e]; rfl)⟩
  have hz:(∫ p,f p ∂μ y)=0:=g.symm.trans (by change ‖Ψ y‖^2=0; unfold y; rw [←wake F b X S W w x,v]; simp)
  have m:= (integral_eq_zero_iff_of_nonneg (f:=f) (fun i=> sq_nonneg _) e).1 hz
  obtain ⟨z,u,t⟩:= (m.and h).exists; exact pow_ne_zero 2 ((norm_ne_zero_iff).2 t) u
variable (m:Lead.Clan→X)
private def shooting (W:Set E4) (z: Lead.Clan→X): Lead.Clan→X:= (Γ W) ∘ z
local notation "Θ"=> shooting X S
lemma forcePositive (z:Lead.Clan→ℂ)(h:z≠0) : 0< ∑ i,‖z i‖^2:= by
 obtain ⟨i,p⟩:∃ i,z i≠0:=by by_contra! f; exact h (funext f)
 exact lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr p) 2) (Finset.single_le_sum (f:=fun i=> ‖z i‖^2) (fun i _=>sq_nonneg _) (mem_univ i))
private lemma passesCoercion {b':ℝ}(y:Lead.Clan→X) (W:Set E4)(h:MeasurableSet W)(f:Coercive Lead.Clan X (Θ W y) b'):
   Coercive Lead.Clan X y b':= by
 intro x
 refine le_trans (f x) (Eq.trans_le (a:=‖FrameBound.combination _ _ (Θ W y) x‖^2) ?_ (below X S.ℚmeasure h (FrameBound.combination _ _ y x)))
 apply congrArg (fun p:X=>‖p‖^2); unfold FrameBound.combination; simp only [map_sum,map_smul,shooting,Function.comp_apply]
lemma coercion_li (X:Hilbert)(u:Lead.Clan → X.space) (d:ℝ)(c:0<d)(h:Coercive Lead.Clan X u d): LinearIndependent ℂ u:= by
 rw [Fintype.linearIndependent_iff]
 rintro w y i; by_contra e; have hp:w≠0:= fun g=>e ((congrFun g i))
 have Hv:=mul_pos c (forcePositive w hp)|>.trans_le (h w); unfold FrameBound.combination at Hv; rw [y,norm_zero] at Hv; simp at Hv
lemma spectralGrants (m:Lead.Clan→X)(W:Set E4)(h:MeasurableSet W){p:ℝ}(e:0<p)(u:Coercive Lead.Clan X (Θ W m) p)
    (t:∀ x:X, ∀ᵐ w∂μ (Γ W x),(∫ z:Vantage,Score.gain F.val posse birthClock b z w)≠0):
   ∃ d:ℝ,0<d∧Coercive Lead.Clan X (shooting X S W (Ψ∘ m)) d ∧ Coercive Lead.Clan X (Ψ∘ m) d:= by
  let y:=Ψ ∘ m; let L:=Θ W m; let K:=Θ W y; let Q:= rolesBeam F b X S
  have g{z:Lead.Clan→ℂ}(u:∑ i,z i • K i=0): ∑ i,z i • L i=0:= by
    let Y:=∑ i,z i • m i; have hz:∀ i:Lead.Clan, y i=Q (m i):=fun i=> rfl
    have hp: Γ W (Ψ Y) =0:=by change Γ W (Q (∑ i,z i • m i))=0; simp_rw [map_sum,map_smul,← hz]; exact u
    have H': Γ W Y=0:= kills F b X S W h Y hp (t Y); unfold Y at H'; simp_rw [map_sum,map_smul] at H'; exact H'
  have hz:= FrameBound.eventual Lead.Clan X (v:=fun _=>K) (fun i=>⟨_,Eventually.of_forall fun n=> le_refl _⟩) (fun a ha=>?_)
  · obtain ⟨D,v,p⟩:=hz; obtain ⟨n,p⟩:= p.exists
    exact ⟨D,v,p,passesCoercion X S y W h p⟩
  let t:=FrameBound.combination Lead.Clan X K a; have hb:t ≠0:= fun v=> ha (funext (Fintype.linearIndependent_iff.mp (coercion_li X L p e u) a (g v)))
  have hx:= pow_pos (norm_pos_iff.mpr hb) 2
  exact ⟨_, half_pos hx,Eventually.of_forall fun x=> half_lt_self hx⟩

section order
open Matrix
lemma loewnerCharge (d:ℝ)(x:Lead.Clan→ X.space)(v:Coercive Lead.Clan X x d): ((d:ℂ) • (1:CrossRead)) ≤ Matrix.gram ℂ x:= by
 rw [Matrix.le_iff, posSemidef_iff_dotProduct_mulVec]
 refine ⟨(isHermitian_gram ℂ x).sub (isHermitian_one.smul (show IsSelfAdjoint (d:ℂ) from by unfold IsSelfAdjoint; simp)),fun w=>?_⟩
 rw [sub_mulVec,smul_mulVec,one_mulVec,dotProduct_sub,sub_nonneg,star_dotProduct_gram_mulVec,dotProduct_smul, inner_self_eq_norm_sq_to_K,smul_eq_mul]
 -- compare cast order
 have he : star w ⬝ᵥ w=((∑ i:Lead.Clan,‖w i‖^2:ℝ):ℂ):=by unfold dotProduct; push_cast; refine Finset.sum_congr rfl fun i _=>?_ ; exact Complex.conj_mul' (w i) -- cast order
 rw [he]; change (d:ℂ)*_ ≤ (↑‖FrameBound.combination Lead.Clan X x w‖:ℂ)^2; rw [←Complex.ofReal_pow, ←Complex.ofReal_mul]; exact_mod_cast v w
lemma entryCharge (d:ℝ)(p:0<d)(x:Lead.Clan→ X.space)(v:Coercive Lead.Clan X x d): ReadsSix (gram ℂ x) ∧ (∀ i:Lead.Clan,0< gram ℂ x i i):=
 let H:=posDef_gram_of_linearIndependent (coercion_li X x d p v); ⟨⟨H.det_pos.ne', fun i=> H.diag_pos.ne'⟩,fun i=>H.diag_pos⟩
end order
end abstract

-- Axis 3 purchases
variable (P:Spine)(x:P.Spectrum0 3)(Z:Lead.Clan)(s n:ℕ)(F:SampleDose)
local notation "Η"=> P.ManyF 3 (P.otherSpectrum 3 3 x)
local notation "u"=> P.otherSpectrum 3 3 x
local notation "S"=> P.seasons 3 u
local notation "Γ"=> (S).ℚmeasure.region
local notation "ℓ"=> P.launchCost x s n
local notation "π'"=> P.wealth 3 u
local notation "g"=> P.increment s n
local notation "ν"=> P.birthCloud x Z s n
lemma sharpAim : P.launchCost x s n Z F 0=pickCost F (P.increment s n) Η S ν:= by
 let B:=P.cartage 3 u; let E:=(S).E
 let U:=P.sixWard_macroVector x s n Z -- edit
 unfold launchCost pickCost; refine integral_congr_ae (Eventually.of_forall fun i=> ?_)
 have h:B i=(S).U (posse i):= P.uses_cart 3 u i
 have ht:(i 3-0).toNNReal=birthClock i:=congrArg Real.toNNReal (sub_zero (i 3))
 refine congrArg (fun y:Η=> (F.val i:ℂ) • y) ?_
 exact congrArg₂ (fun (x:(P.ManyF 3 (P.otherSpectrum 3 3 x)).Op)(y:Η)=> x y) h (congrArg₂ (fun (t:ℝ≥0)(y:Η)=> E t y) ht (P.filtered_explicit x s n Z)) -- x shadow dangers notation
lemma strictlyAdvancing : Γ {p:E4|YM.time p=0} (P.launchCost x s n Z F 0)=0:= (congrArg _ (P.sharpAim ..)).trans (voidable ..)
-- zoom of any open (with the transverse octant qualification). Balls as special case.
def WindowCost (A:Set E4)(b:Fin 3→Bool):Prop:= IsOpen A ∧ A.Nonempty∧ A⊆Mink.inside∧ A⊆ terrain tracks3 ⁻¹' (alley b)
-- eventually EVERY i. projection positive already before the inner. wall positivity uses habitat.
variable {P x}
local notation "B"=> P.calibration -- caution
variable {K:P.Register}{c r:ℕ→ℕ}{J:P.Ellis 3 x}(T:P.Experiment K c r x J) (A:Set E4)(b:Fin 3→Bool)(w:WindowCost A b)
include T w
set_option maxHeartbeats 800000 in
lemma lateRoster : ∀ᶠ i:ℕ in atTop, let s:=c i; let n:=r i; let H:= P.ManyF 3 (P.otherSpectrum 3 3 x)
  ∀ (U:Dose AlleySpace)(G:Dose ℝ), U.Normalized → G.Normalized →
   let u₂:=upperTest U G; let v:Lead.Clan→H:=fun Z=>P.launchCost x s n Z u₂ 0
   ∃ d:ℝ,0<d ∧ Coercive Lead.Clan H (fun Z=>((P.seasons 3 (P.otherSpectrum 3 3 x)).ℚmeasure.region (Cheer.press (P.dew s n) A)) (v Z)) d ∧ Coercive Lead.Clan H v d:= by
 have pA : (Mink.inside ∩ A).Nonempty:=by obtain ⟨i,h⟩:= w.2.1; exact ⟨i,w.2.2.1 h,h⟩
 let W:= T.zoommat.2.2 A w.1 pA
 let p:=W.choose; have e:= W.choose_spec.1; have v:= W.choose_spec.2
 filter_upwards [v] with i k; let s':=c i; let n':=r i; let H':=P.ManyF 3 (P.otherSpectrum 3 3 x); let ρ:=(P.dew s' n'); let V:=Cheer.press ρ A
 have hp:0<ρ:= P.dew_pos s' (T.launch.unitSize i)
 have ht:MeasurableSet V:= Cheer.pressured _ w.1.measurableSet
 have he:V⊆Mink.inside:=by change Cheer.zoom ρ ⁻¹' A ⊆ _; simpa [Cheer.zoom_inside hp] using (Set.preimage_mono (f:=Cheer.zoom ρ) w.2.2.1)
 have hz:V ⊆ terrain tracks3 ⁻¹' (alley b):= (Set.preimage_mono w.2.2.2).trans (blaze_keep b _ hp)
 intro s₀ n₀ G' U G m h u' y
 let a:=P.increment s' n'; have hy:0<a:= P.increment_pos s' n' (T.launch.unitSize _)
 let K':=fun Z=>P.birthCloud x Z s' n'; let Q:=pickCost u' a Η S; have H₀:y= Q ∘ K':= funext fun i=>P.sharpAim ..
 exact Eq.mpr (congrArg (fun y:Lead.Clan → H'
       => ∃ d:ℝ, 0<d ∧ Coercive Lead.Clan Η ((Γ V) ∘ y) d ∧ Coercive Lead.Clan Η y d) H₀) (spectralGrants u' a Η S K' V ht e k (fun z=> gain_live U G T.top _ ht he b hz a hy z m h))
omit T w
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
