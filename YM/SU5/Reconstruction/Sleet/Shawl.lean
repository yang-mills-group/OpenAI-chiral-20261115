import YM.SU5.Reconstruction.Sleet.PressureMeter
import YM.SU5.Reconstruction.Sleet.Frostline
import Mathlib.Analysis.Calculus.Deriv.Star
/-! # Glued scarf. Genuine overlaps required -/
set_option autoImplicit false
noncomputable section
namespace YM.ConePrice.Storm.Snowball
open Function Set Filter Metric MeasureTheory Measure Complex Sail
open scoped Topology NNReal ENNReal Real ComplexOrder InnerProductSpace Classical ComplexConjugate

variable {x:ℝ→ℂ}
structure Affix (C:ℝ)(S:Set ℂ)(x:ℝ→ℂ)(F:ℂ→ℂ) : Prop where
 straight: AnalyticOnNhd ℂ F S
 bulb: ∀ z∈S,‖F z‖≤ C
 values: ∀ v:ℝ, (v:ℂ)∈ S → F v=x v
variable {C C' :ℝ}{A B:Set ℂ} {F G : ℂ→ℂ}
lemma Affix.back (p:Affix C A x F): Affix C ((Neg.neg) ⁻¹' A) (fun y=> x (-y)) (fun y=> F (-y)) := {
 straight z e := (p.straight _ e).comp analyticAt_id.neg
 bulb z e:=p.bulb _ e
 values t v:= by
    have hv:(↑(-t):ℂ)∈ A:= by rw [Complex.ofReal_neg]; exact v
    rw [← ofReal_neg,p.values _ hv] }
lemma Affix.merges [∀ z,Decidable (z∈A)] {Q:ℝ} (h:IsOpen A)(t:IsOpen B)(p:Affix C A x F)(w:Affix C' B x G)(v:C≤Q)(s:C'≤Q)(e:EqOn F G (A∩B)) : Affix Q (A∪B) x (A.piecewise F G):= by
 have ha:EqOn (A.piecewise F G) F A:= by intro y hy; rw [piecewise_eq_of_mem A F G hy] -- name
 have hg:EqOn (A.piecewise F G) G B:= by
   intro y hy; by_cases p:y∈ A
   · exact (ha p).trans (e ⟨p,hy⟩)
   exact Set.piecewise_eq_of_notMem A F G p
 constructor
 · intro y p'; rcases p' with p'|p'
   · refine (p.straight y p').congr (EventuallyEq.symm (ha.eventuallyEq_of_mem (h.mem_nhds p'))) -- tune
   exact (w.straight y p').congr (hg.eventuallyEq_of_mem (t.mem_nhds p') |>.symm)
 · intro z z'; rcases z' with z'|z'; rw [ha z']; exact (p.bulb z z').trans v
   rw [hg z']; exact (w.bulb z z').trans s
 intro u k; rcases k with k|k; exact (ha k).trans (p.values u k)
 exact (hg k).trans (w.values u k)

def rightWork (C:ℝ):= {z:ℂ| C< z.re}
def watch(r:ℝ):Set ℂ:= Metric.ball 0 r

def InPocket (Q b:ℝ)(x:ℝ→ℂ):Prop:=∃ F:ℂ→ℂ, Affix Q (rightWork b) x F
def Weatherproof (Q R:ℝ)(x:ℝ→ℂ):Prop:=∃ F:ℂ→ℂ,Affix Q (watch R) x F
private lemma fit_right {r R:ℝ}(p:0≤r)(v:r<R)(u:Affix C (rightWork r) x F)(t:Affix C' (watch R) x G) : EqOn G F (watch R∩rightWork r):= by
 obtain ⟨z,h,v'⟩:= exists_between v
 have hp(x:ℝ)(q:x∈ Ioo r R): (x:ℂ)∈ watch R∩rightWork r:= by
    refine ⟨Metric.mem_ball.mpr ?_,q.1⟩; rw [dist_zero_right,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (p.trans_lt q.1)]; exact q.2
 refine pioneer (((convex_ball (0:ℂ) R).inter (convex_halfSpace_gt reCLM.toLinearMap.isLinear r)).isPreconnected) (hp z ⟨h,v'⟩) r R ⟨h,v'⟩ (t.straight.mono inter_subset_left) (u.straight.mono inter_subset_right) (fun x h=> (t.values x (hp x h).1).trans (u.values x (hp x h).2).symm)

lemma InPocket.mirror {b:ℝ}(t:InPocket C b x)(p:∀ z:ℝ,x (-z)=conj (x z)): InPocket C b (fun y=>x (-y)):=by
 obtain ⟨F,f⟩:=t
 refine ⟨fun z=>conj (F (conj z)), ?_, ?_,fun t e=>?_⟩
 · apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const continuous_re); intro i h
   exact (differentiableAt_conj_conj_iff.mpr (f.straight _ (by simpa [rightWork] using h)).differentiableAt).differentiableWithinAt -- tune
 · intro z h; exact Eq.trans_le (norm_conj _) (f.bulb _ (by simpa [rightWork] using h))
 rw [p,Complex.conj_ofReal,f.values t e]
lemma Weatherproof.back {R:ℝ}(t:Weatherproof C R x): Weatherproof C R (fun y=>x (-y)):=by
 obtain ⟨F,f⟩:=t; exact ⟨_, Eq.mp (congrArg (fun U=> Affix C U _ _) (show Neg.neg ⁻¹' watch R = watch R from (by ext;simp [watch,Metric.mem_ball]))) (f.back)⟩ -- goal placeholder tune

lemma affords {Q b r d:ℝ}(p:0<b)(h:b<r)(v:0≤d)(w:b^2+d^2<r^2) (t:Weatherproof C r x)(u:InPocket C' b x)(s:InPocket C' b (fun y=>x (-y)))(q:max C C'≤Q):∃ F:ℂ→ℂ,Swale Q d F ∧ ∀ v:ℝ,F v=x v:= by
 obtain ⟨F,f⟩:=t; obtain ⟨X,g⟩:=u; obtain ⟨Y,y⟩:=s
 let A:=watch r; let B:=rightWork b; let S:=Neg.neg ⁻¹' B; have hz(z:ℂ):z∈S ↔ z.re < -b:=by simp [S,B,rightWork,lt_neg]
 have ho:IsOpen A:= Metric.isOpen_ball; have hp:IsOpen B:= isOpen_lt continuous_const continuous_re
 let G':= (A.piecewise F X); have hG: Affix Q (A∪B) x G':= Affix.merges ho hp f g ((le_max_left ..).trans q) ((le_max_right ..).trans q) (fit_right p.le h g f)
 let T:= fun z:ℂ=> Y (-z); have hT:Affix C' S x T:=by have ht:=y.back; simp only [neg_neg] at ht; exact ht
 let M:=(A∪B).piecewise G' T; have hS:IsOpen S:= hp.preimage continuous_neg
 have bm: Affix Q ((A∪ B)∪ S) x M:= by
   refine (show Affix _ _ _ _ from Affix.merges (ho.union hp) hS hG hT le_rfl ((le_max_right ..).trans q) ?_)
   rintro z ⟨H,t⟩; rcases H with H|H; swap; · linarith [show b<z.re from H,(hz z).1 t]
   have hb:= f.back; rw [show Neg.neg ⁻¹' (watch r)= watch r from (by ext; simp [watch,Metric.mem_ball])] at hb
   unfold G' T; rw [piecewise_eq_of_mem A F X H]; simpa only [neg_neg] using (fit_right p.le h y hb (show -z∈watch r∩ rightWork b from ⟨(by simpa [A,watch,Metric.mem_ball] using H),t⟩))
 have hs(z:ℂ)(u:z.im∈ Icc 0 d): z∈ (A ∪B) ∪S:=by
    by_cases hy: z.re < -b; exact Or.inr ((hz z).2 hy)
    apply Or.inl; by_cases hB:b< z.re; exact Or.inr hB
    apply Or.inl; apply mem_ball.mpr
    rw [dist_zero_right]; apply (sq_lt_sq₀ (norm_nonneg _) (p.trans h).le).mp
    have hb: z.re^2≤ b^2:=sq_le_sq.mpr (by rw [abs_of_pos p]; exact abs_le.mpr ⟨le_of_not_gt hy,le_of_not_gt hB⟩)
    rw [←Complex.normSq_eq_norm_sq, Complex.normSq_apply]; nlinarith [u.1,u.2]
 exact ⟨M,⟨v,bm.straight.continuousOn.mono (fun z t=> hs _ t),bm.straight.differentiableOn.mono (fun z t=> hs _ (Ioo_subset_Icc_self t)),fun z t=> bm.bulb _ (hs _ t)⟩,fun i=> bm.values _ (hs _ (by simpa))⟩
end YM.ConePrice.Storm.Snowball
