/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.Next.RANK.Ray
import YM.Work.F03.Transport
/-!
Read a Pane in *unscaled* small log coordinates under the nonwrapping
r-book. Explicit probe for its welded quadratic in linear curls.
Adapts the path proofs Next/Rank/{LoomNative,GlowLine} from project.
No moving-plane limit here.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Next.Rank.Spindle
open Function Set Filter Lattice Wilson RG Source Labels Configuration CellsInt MeasureTheory
open Exterior Precision Push
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
namespace LampP
variable {b : ℕ} {G:Gauge} {n : Side} (o : Site n)
variable (A : fieldDir G n 1)
abbrev column (p:Turn b) := (wrap n p.val.1+o,p.val.2)
def rayFace (o':Site n) (A : fieldDir G n 1) (p:Turn b):= Work.F03.faceCurl (column o' p) A
abbrev runP(t:ℝ): Config G n:= represent (t • A)
local notation "Q" t:max=> runP A t
lemma idleW(i:Turn b): registered b (Q 0) o i=1:=by
 unfold runP; rw [zero_smul,link_one]; unfold registered used central; rw [face_gauge]; rw [show expandAt o (1:Config G n)=1 from rfl,faceValue,Pressure.one]; group
lemma levelFeel : Tendsto (fun t=> runP A t) (𝓝 0) (𝓝 1):=by
 have ht: Continuous (runP A):= continuous_pi fun i=>?_ -- later tune
 rw [show (1:Config G n)=Q 0 from by unfold runP; rw [zero_smul,link_one]]
 exact ht.tendsto 0
 unfold runP represent; simp_rw [increment,Pi.one_apply,mul_one]; apply G.lieExp_cont.comp; simp only [collect]; fun_prop
lemma blinkW (h : 2*(b+1)<n.val)(p:Turn b):
     HasDerivAt (fun t=> G.mat (registered b (Q t) o p)) (G.colorMat (rayFace o A p)) 0:=by
 simp_rw [registering b _ h o p]
 simp only [spine,face_gauge,Gauge.mat_mul,Gauge.mat_inv]
 let k:=column o p; let T:=paths (lift (k.1-o)); let L(t:ℝ):= fingers (Q t) o k.1; let F(t:ℝ):= faceValue (Q t) k
 have he(t:ℝ): L t=travel (Q t) o T:=by unfold L fingers leaves; rw [travel_at,map_zero,zero_add]
 have hA: HasDerivAt (fun t=> G.mat (L t)) (G.colorMat (linkSum (collect G A) o T)) 0:= by simp_rw [he]; exact travell ..
 have ht:L 0=1:=by rw [he]; unfold runP; rw [zero_smul]; exact stroll_zero ..
 have hh:F 0=1:=by unfold F runP; rw [zero_smul]; exact stroll_zero ..
 have hz:HasDerivAt (fun t=> G.mat (F t)) (G.colorMat (rayFace o A p)) 0:=Work.F03.face_deriv ..
 apply ((hA.mul hz).mul hA.star).congr_deriv
 simp [ht,hh,G.colorMat_skew]
lemma actualRay (w:Word b) (h:2*(b+1)<n.val) :
 played (registered b (Q 0) o) w=1 ∧ HasDerivAt (fun t=> G.mat (played (registered b (Q t) o) w)) (G.colorMat (stage w (rayFace o A))) 0:=by
 induction w with
 | nil => simp only [played,stage,List.map_nil,List.prod_nil,List.sum_nil,map_zero]; exact ⟨trivial,hasDerivAt_const _ _⟩
 | cons j w IH=>
    obtain ⟨p,i⟩:=j
    have ht:= blinkW o A h p
    obtain ⟨g,f⟩:= IH
    cases i <;> simp only [played,List.map_cons,List.prod_cons,Bool.false_eq_true,↓reduceIte,Gauge.mat_mul,Gauge.mat_inv,stage,List.sum_cons,map_add,map_neg]
    · refine ⟨?_,(ht.mul f).congr_deriv ?_⟩; rw [idleW,one_mul]; exact g
      rw [g,G.mat_one,mul_one,idleW,G.mat_one,one_mul]; rfl
    · refine ⟨?_, (ht.star.mul f).congr_deriv ?_⟩; rw [idleW, inv_one,one_mul]; exact g
      simp only [g,idleW,Gauge.mat_one,mul_one,one_mul,star_one,Gauge.colorMat_skew]; rfl
private lemma back {f : ℝ → G.El} {a : G.Color} (hp : f 0=1) (h : HasDerivAt (fun t => G.mat (f t)) (G.colorMat a) 0) : HasDerivAt (fun t=> G.plog (G.mat (f t))) a 0 := by
  have he : DifferentiableAt ℝ G.plog 1 := G.plog_diff.differentiableAt (by simp)
  let v := fderiv ℝ G.plog 1
  have ht : HasFDerivAt G.plog v (G.mat (f 0)) := by rw [hp,G.mat_one]; exact he.hasFDerivAt
  refine (ht.comp_hasDerivAt 0 h).congr_deriv ?_
  have H : (v ∘L G.colorMat.toContinuousLinearMap)=ContinuousLinearMap.id ℝ G.Color := by
    apply HasFDerivAt.unique (f:=G.plog ∘ (fun a : G.Color => G.mat (G.lieExp a))) (x:=0)
    · apply HasFDerivAt.comp _ _ G.expDiff_zero; rw [G.mat_lieExp_zero,G.mat_one]; exact he.hasFDerivAt
    exact HasFDerivAt.congr_of_eventuallyEq (hasFDerivAt_id 0) G.plog_left
  exact DFunLike.congr_fun H a
-- extend logs to full Directions by zero elsewhere
abbrev paneExtendLin : Space G o b →L[ℝ] Directions G n:= ContinuousLinearMap.pi (fun i=> if h:i∈ Room o b then ContinuousLinearMap.proj ⟨i,h⟩ else 0)
lemma evaluateE(k: Space G o b)(i: Dim o b): paneExtendLin o k i.val= k i:=by simp only [paneExtendLin, ContinuousLinearMap.pi_apply, dif_pos i.property,ContinuousLinearMap.proj_apply] -- tune
lemma feeE : ‖paneExtendLin o (G:=G) (b:=b)‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v=> by
 rw [one_mul]; refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i=>?_ ; by_cases p:i∈ Room o b
 · exact (congrArg (‖·‖) (evaluateE o v (⟨i,p⟩:Dim o b))).trans_le (norm_le_pi_norm v ⟨i,p⟩) -- equality norm rewrite
 rw [paneExtendLin, ContinuousLinearMap.pi_apply,dif_neg p,ContinuousLinearMap.zero_apply,norm_zero]; exact norm_nonneg _
abbrev rolledZero {b:ℕ} (t:ℝ) : Directions G n:= paneExtendLin o (wired 1 o b (Q t)) -- b binder explicit
lemma spRay (i:Edge (Site n)): ContDiffAt ℝ ω (fun t=> G.mat (spine (Q t) o i)) 0:=by
 have hp : ContDiffAt ℝ ω (fun t:ℝ=> t • A) 0:=by fun_prop
 have hh (x:Site n)(w:Walk): ContDiffAt ℝ ω (fun t=> G.mat (travel (Q t) x w)) 0:=by
    exact (show ContDiffAt ℝ ω (fun i=> G.mat (travel (represent i) x w)) ((0:ℝ)•A) from (zero_smul ℝ A).symm ▸ writes ..).comp (g:=fun i=> G.mat (travel (represent i) x w)) 0 hp
 have hx(i:Site n): ContDiffAt ℝ ω (fun t=> G.mat (fingers (Q t) o i)) 0:=by
    unfold fingers leaves; simp_rw [travel_at,map_zero,zero_add]; exact hh o _
 unfold spine; simp_rw [Lattice.gauge, G.mat_mul,G.mat_inv]; apply ContDiffAt.mul
 · apply (hx i.1).mul; have hv:=hh i.1 [posDir i.2]; simpa [travel,Step.read,Step.used,Step.vec,posDir] using hv
 exact ((starL ℝ).contDiff.contDiffAt.comp _ (hx _))
lemma rollsBill (b:ℕ)(h:2*(b+1)<n.val) :
  let D :=rolledZero (b:=b) o A
  D 0=0 ∧ ContDiffAt ℝ ω D 0 ∧ HasDerivAt D (paneExtendLin o (rows 1 h (rayFace o A))) 0 ∧
   ∀ᶠ t in 𝓝 0, Agrees (patch b o) (increment 1 (D t)) (spine (Q t) o):=by
 let L:=paneExtendLin o (b:=b) (G:=G); let Y(t:ℝ):=wired 1 o b (Q t); let v:Space G o b :=rows 1 h (rayFace o A)
 have he (i:Dim o b): spine (Q 0) o i.val=1:=(spun (Q 0) o h _).trans (actualRay o A (word G h i) h).1
 have hz: Y 0=0:=by funext i; simp [Y,wired,he]
 have ht (i:Dim o b) : HasDerivAt (fun t=>Y t i) (v i) 0:=by
    simp_rw [Y,wired,v,rows,inv_one,one_smul]; apply back (he i); simp_rw [spun _ _ h]; exact (actualRay o A _ h).2
 have hD:= hasDerivAt_pi.mpr ht
 have hd : ContDiffAt ℝ ω Y 0 := by
    apply contDiffAt_pi.mpr; intro i; unfold Y wired; simp only [inv_one,one_smul]
    have hf:=spRay o A i.val; apply ContDiffAt.comp (g:=G.plog) (f:=fun t=>G.mat (spine (Q t) o i.val)) 0 _ hf
    rw [he,G.mat_one]; exact G.plog_diff
 intro D; refine ⟨Eq.trans (congrArg L hz) (map_zero L), L.contDiff.contDiffAt.comp (0:ℝ) hd, L.hasFDerivAt.comp_hasDerivAt _ hD,?_⟩
 have hh (i:Dim o b):∀ᶠ t in 𝓝 0,G.lieExp (Y t i)=spine (Q t) o i.val:=by
    unfold Y wired; simp only [inv_one,one_smul]; apply Tendsto.eventually _ G.plog_right
    rw [show (1:G.El)=_ from (he i).symm]; apply (G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.tendsto_nhds_iff.mpr; exact (spRay o A i.val).continuousAt
 filter_upwards [eventually_all.mpr hh] with t g; intro i hi hj; let e:Dim o b:=⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi,hj⟩⟩; change G.lieExp (paneExtendLin o (Y t) e.val)*1=_; rw [evaluateE,mul_one,g]; -- tune
end LampP
end YM.Next.Rank.Spindle
