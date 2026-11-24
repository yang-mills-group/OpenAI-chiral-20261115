import YM.CF.Vol.Shop
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vol
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Char Newt
open Push.SectorMeasure AnalyticBridge.RelativeLogdet.Ink
open Push Push.Uniform Hors Finset Laurent Bloch
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{K:Teller G}{F:Forest S.ratio}{X E B:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup B][NormedSpace ℝ B]{t x s D A C Q V r:ℝ}{i n l:ℕ}
open Tube Next.Fluctuations Work.F03 Nacre
open Next.SectorChange AnalyticBridge.GaussianFieldAlignment Oriented Rows
structure KnotP(f:E→ B)(n:ℕ)(A C ε:ℝ):Prop where
 sails x:‖x‖<ε→ Jet.Allows n f x C
 peak:cFoot 2 f
 cap: ‖iteratedFDeriv ℝ 2 f 0‖ ≤ A
section stone
variable{x:E}{g f:E→B}
lemma KnotP.addV(h:KnotP f n A C t)(u:KnotP g n D Q t)(ht:0<t)(hp:2 ≤ n): KnotP (fun y=>f y+g y) n (A+D) (C+Q) t:=by
 have hv:‖(0:E)‖<t:=by simpa using ht
 have he j (hj:j≤2): iteratedFDeriv ℝ j (fun y=>f y+g y) 0= iteratedFDeriv ℝ j f 0+iteratedFDeriv ℝ j g 0:=iteratedFDeriv_add_apply (((h.sails _ hv).order (hj.trans hp)).smooth) (((u.sails _ hv).order (hj.trans hp)).smooth)
 exact ⟨fun i hi=> (h.sails _ hi).add (u.sails _ hi),fun i hi=> by rw [he i hi.le,h.peak _ hi,u.peak _ hi,zero_add], by rw [he 2 le_rfl]; exact (norm_add_le ..).trans (add_le_add h.cap u.cap)⟩
lemma KnotP.mono(p:KnotP f n A C t)(h:A≤ D)(ht:C≤ Q)(he:r ≤ t): KnotP f n D Q r:= ⟨fun i hp=>(p.sails _ (hp.trans_le he)).mono ht,p.peak,p.cap.trans h⟩
lemma KnotP.scale(h:KnotP f n A C t)(g:ℝ)(ht:0<t)(hp:2 ≤ n): KnotP (fun y=> g • f y) n (|g| * A) (|g| * C) t:=by
 have hv:‖(0:E)‖<t:=by simpa using ht
 have he j(hj:j≤2): iteratedFDeriv ℝ j (fun y=> g • f y) 0=g • iteratedFDeriv ℝ j f 0:=iteratedFDeriv_const_smul_apply ((h.sails _ hv).order (hj.trans hp)|>.smooth)
 exact ⟨fun i hi=>(h.sails _ hi).smul _,fun i hi=> by rw [he i hi.le,h.peak i hi,smul_zero],by rw [he _ le_rfl,norm_smul,Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left h.cap (abs_nonneg _) ⟩
lemma knot3(h:cFoot 3 f)(ht:0≤ A)(hp:∀ x, ‖x‖<t → Jet.Allows n f x C): KnotP f n A C t := ⟨hp,fun i hi => h i (by omega),by rw [h 2 (by omega),norm_zero]; exact ht⟩
variable {f' g':E→ G.Color}
lemma breeze (h:Jet.Allows n f' x C)(p:Jet.Allows n g' x Q): Jet.Allows n (fun u=> inner ℝ (f' u) (g' u)) x (2^n*C*Q):=by
 have hp := h.bilinear (innerSL ℝ) p (show ‖(innerSL ℝ : G.Color →L[ℝ] G.Color →L[ℝ] ℝ)‖ ≤ 1 from ContinuousLinearMap.opNorm_le_bound₂ _ zero_le_one fun i j=> by rw [one_mul]; exact abs_real_inner_le_norm i j); rwa [mul_one] at hp -- maybe re_inner
lemma Yacht(h:∀ x, ‖x‖<r→ Jet.Allows n f' x C)(p:∀ x, ‖x‖<r→ Jet.Allows n g' x Q)(hs:stance f' t)(hg:g' 0=0)(hr:0<r)(hn:2 ≤ n): KnotP (fun y=>inner ℝ (f' y) (g' y)) n (2*t*Q) (2^n*C*Q) r:=by
 let Φ(y):=inner ℝ (f' y) (g' y); let F:=fderiv ℝ f' 0; let U:=fderiv ℝ g' 0
 have hK:‖(0:E)‖<r:=by simpa using hr
 have hh y(hy:‖y‖<r) :=breeze (h y hy) (p y hy)
 let Y(x y:E) := inner ℝ (F x) (U y)+inner ℝ (F y) (U x)
 have hf:DifferentiableAt ℝ f' 0:= ((h _ hK).order hn).smooth.differentiableAt (by norm_cast)
 have he:DifferentiableAt ℝ g' 0:= ((p _ hK).order hn).smooth.differentiableAt (by norm_cast)
 have hq:(∀ x:E,Tendsto (fun t:ℝ=> Φ (t•x)/t^2) (𝓝[≠] 0) (𝓝 (Y x x/2))):=by
    intro x; have ha:= (Push.side f' hf x).tendsto_slope_zero; have ht:= (Push.side g' he x).tendsto_slope_zero; have hh:= ha.inner (𝕜:=ℝ) ht
    simp only [zero_smul,zero_add, hs.origin, hg,sub_zero] at hh
    unfold Φ Y F U; rw [add_self_div_two]; refine hh.congr (fun t=>?_); simp [real_inner_smul_left,real_inner_smul_right]; ring
 obtain ⟨h1,h2,h3⟩ := hessian_of_limit (f:=Φ) (Q:=Y) (((hh _ hK).order hn).smooth) hq (fun i j k=>by unfold Y; rw [map_add,inner_add_left,map_add,inner_add_right]; ring) (fun i j=>add_comm ..) -- tune
 have hu:0≤ t:=(norm_nonneg _).trans hs.rud; have hp:‖U‖ ≤ Q:=drops2 (p _ hK) (by omega); have hQ:0 ≤ Q:=(norm_nonneg _).trans hp
 refine ⟨hh,fun i hi=>?_,Planned.AtomRegular.op_le_of_unit (show 0 ≤ 2*t*Q by positivity) fun x hx=>?_⟩
 · ext1 x; interval_cases i
   · change iteratedFDeriv ℝ 0 Φ 0 x=0; rw [iteratedFDeriv_zero_apply,h1]
   change iteratedFDeriv ℝ 1 Φ 0 x=0; rw [iteratedFDeriv_one_apply,h2]; rfl
 have ht(i j:Fin 2):|inner ℝ (F (x i)) (U (x j))|≤ t*Q:=by
    refine (abs_real_inner_le_norm ..).trans (mul_le_mul ?_ ?_ (norm_nonneg _) hu); exact (F.le_opNorm _).trans ((mul_le_of_le_one_right (norm_nonneg _) (hx i)).trans hs.rud); exact (U.le_opNorm _).trans ((mul_le_of_le_one_right (norm_nonneg _) (hx j)).trans hp)
 rw [show x=![x 0,x 1] from (by ext i; fin_cases i<;>rfl), h3]; exact (abs_add_le ..).trans ((add_le_add (ht 0 1) (ht 1 0)).trans_eq (by ring))
end stone
end YM.CF.Vol
