import YM.CF.BPress.SheetNet
import YM.CF.BPress.Axial
/-! VolumeB-gate eq:B-blend Lie construction with fallback copying at blend endpoints (extends construction off accepted field). Use first-order chord price on all internal small-log templates. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress
open Function MeasureTheory LocalH Lattice SU Mag Cube Grid Filter Branch Sheet Set
open scoped Topology BigOperators Classical Matrix
variable {s : Side} {T : Atlas} {y C C' Lf : ℝ} {B : ℕ} {G : Gauge} (W : Tunnel s)
open Tunnel
namespace chord
variable (V : Chart G)
def blend (u : ℝ) (a b : G.El) : G.El:= if u=0 then a else if u=1 then b else G.lieExp ((1-u) • V.logV a + u • V.logV b)
lemma blend_meas (u:ℝ) : Measurable (fun x:G.El × G.El=>blend V u x.1 x.2):=by
 unfold blend; split; exact measurable_fst; split; exact measurable_snd
 apply Measurable.comp (show Continuous G.lieExp by fun_prop).measurable _; exact ((V.logV_meas.comp measurable_fst).const_smul (1-u)).add ((V.logV_meas.comp measurable_snd).const_smul u) -- tune
lemma blend_eq (u:ℝ) {a b:G.El}(p:G.chord a<V.δ)(h:G.chord b<V.δ): blend V u a b=G.lieExp ((1-u) • snap G a + u • snap G b):=by
 unfold blend; by_cases l:u=0; subst u; simp [V.read _ p.le]; by_cases g:u=1; subst u; simp [V.read _ h.le]; simp [l,g, Chart.logV,p,h]
@[simp] lemma blend_zero (a b:G.El): blend V 0 a b=a:= by simp [blend]
@[simp] lemma blend_one (a b:G.El): blend V 1 a b=b:=by simp [blend]
section taylor
open Gauge
open scoped Matrix.Norms.Frobenius Asymptotics InnerProductSpace ContDiff
attribute [local instance] frobInner
-- interpolation Taylor: provided all data logs in ball of radius r'
private def four (x : Fin 4 → G.Color) := G.lieExp (x 0)*G.lieExp (x 1) * (G.lieExp (x 2))⁻¹ * (G.lieExp (x 3))⁻¹
private lemma four_diff : ContDiff ℝ ω (G.mat ∘ four) := by
 simp_rw [Function.comp_def, four, G.mat_mul, ←exp_neg]; exact (((G.exp_jet.comp (contDiff_apply ..)).mul (G.exp_jet.comp (contDiff_apply ..))).mul (G.exp_jet.comp (contDiff_apply ..).neg)).mul (G.exp_jet.comp (contDiff_apply ..).neg)
private lemma four_bound (u : ℝ) (g : G.Mat) (h : ‖g‖ ≤ u) : ‖g‖ ≤ u:=h
private def mix {X : Type*} [SMul ℝ X] [Add X] (u : ℝ)(a b : X) := (1-u) • a+u • b
private lemma mix_ball {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {x y:X}{u r:ℝ}(p:u∈Icc 0 1)(h:‖x‖ ≤ r)(t:‖y‖ ≤r) : ‖mix u x y‖ ≤ r:=by
 apply (norm_add_le ..).trans; rw [norm_smul,norm_smul, Real.norm_of_nonneg p.1,Real.norm_of_nonneg (sub_nonneg.mpr p.2)]; exact (add_le_add (mul_le_mul_of_nonneg_left h (sub_nonneg.mpr p.2)) (mul_le_mul_of_nonneg_left t p.1)).trans_eq (by ring)
private lemma group1 (g : G.El) : ‖G.mat g-1‖=G.colorScale*G.chord g:= by rw [←G.mat_one,←chord.one,scale_mul]
private lemma four_price (G : Gauge): ∃ C δ : ℝ, 0<C ∧ 0<δ ∧ ∀ (u r m:ℝ)(p:u∈ Set.Icc 0 1) (h:r<δ)(a b:Fin 4→G.Color),
    ‖a‖ ≤ r → ‖b‖ ≤ r → G.chord (four a)≤m → G.chord (four b)≤ m → G.chord (four (mix u a b)) ≤ m+C*r^2:=by
 let f:=G.mat ∘ four; let L:=fderiv ℝ f 0; obtain ⟨δ,C,p,t,Q⟩:= taylor_change _ four_diff.contDiffAt (((four_diff (G:=G)).differentiable (by simp) 0).hasFDerivAt) -- tune
 refine ⟨2*C/G.colorScale,δ,by have h:=G.colorScale_pos; positivity,p,?_⟩; intro u r m k w a b i j h y
 have hr:0≤ r:=(norm_nonneg a).trans i; have hh (i:Fin 4→G.Color) (p:‖i‖ ≤ r) : ‖f i-1-L i‖ ≤ C*r^2:=by
    have he:=Q r w i (Metric.mem_closedBall.mpr (by rwa [dist_zero_right])) 0 (Metric.mem_closedBall_self hr)
    rw [sub_zero] at he; change ‖f i-f 0-L i‖≤_ at he; rw [show f 0=1 by simp [f,four]] at he; refine he.trans ((mul_le_mul_of_nonneg_left p (?_ : 0≤ C*r)).trans_eq ?_); all_goals first| positivity| ring -- tune
 have hx (a:Fin 4→G.Color)(p:‖a‖≤r)(t:G.chord (four a)≤m) : ‖L a‖ ≤ C*r^2+ G.colorScale*m:=by
    have he:= norm_le_norm_sub_add (L a) (f a-1); rw [norm_sub_rev] at he; apply he.trans (add_le_add (hh a p) ?_); rw [show f a=G.mat (four a) from rfl, group1]; exact mul_le_mul_of_nonneg_left t G.colorScale_pos.le
 let v:=mix u a b; have hm: ‖v‖ ≤ r:=mix_ball k i j; have hv : ‖L v‖ ≤ C*r^2+G.colorScale*m:=by unfold v mix; rw [map_add,map_smul,map_smul]; exact mix_ball k (hx a i h) (hx b j y)
 have hg: ‖G.mat (four v)-1‖ ≤ (C*r^2)+(C*r^2+G.colorScale*m):= (norm_le_norm_sub_add (f v-1) (L v)).trans (add_le_add (hh v hm) hv)
 apply le_of_mul_le_mul_left ?_ G.colorScale_pos; change G.colorScale*G.chord (four v) ≤ _; rw [←group1]; refine hg.trans_eq ?_; have ht:=G.colorScale_pos; field_simp; ring
/-- `eq:B-blend` prices. uniform in purchase r (Cframe/R on the use) -/
theorem blend_cost : ∃ δ C : ℝ, 0<δ ∧ 0<C ∧ δ ≤ V.δ ∧ ∀ r<δ, ∀ (a b: G.El), G.chord a ≤ r → G.chord b ≤ r →
    (∀ u∈ Icc 0 1, ∀ v∈ Icc 0 1, chord (blend V u a b) (blend V v a b) ≤ C*|u-v| *r) ∧
    ∀ (u:ℝ)(m:ℝ) (x y : Fin 4→G.El), (∀ i, G.chord (x i) ≤ r ∧ G.chord (y i) ≤ r) → (u∈Icc 0 1) →
     G.chord ((x 0)*(x 1)*(x 2)⁻¹*(x 3)⁻¹) ≤ m → G.chord ((y 0)*(y 1)*(y 2)⁻¹*(y 3)⁻¹) ≤ m →
     let z(i):=blend V u (x i) (y i); G.chord ((z 0)*(z 1)*(z 2)⁻¹*(z 3)⁻¹) ≤ m+C*r^2:=by
 obtain ⟨C,δ,p,t,G'⟩:=four_price G; obtain ⟨K,h⟩:=exp_lip G δ; let k:ℝ:= 2*V.C*K/G.colorScale; have he:=G.colorScale_pos; have hx:=V.span; have hV:0 ≤ k:= by unfold k; positivity
 refine ⟨min (δ/V.C) V.δ,k+C*V.C^2, lt_min (by positivity) V.size,by positivity,min_le_right ..,?_⟩; intro r hp a b v w; have ha: r<V.δ:=hp.trans_le (min_le_right ..); have ht: V.C*r<δ:= by rw [mul_comm]; exact (lt_div_iff₀ hx).mp (hp.trans_le (min_le_left ..))
 have hr:0≤r:=(G.chord_nonneg a).trans v
 have hz (x:G.El)(h:G.chord x≤r): ‖snap G x‖≤V.C*r:=(V.snap_bound x (h.trans ha.le)).trans (mul_le_mul_of_nonneg_left h hx.le)
 constructor; · intro u q d i; let x:= snap G a; let y:=snap G b; let g u:= mix u x y; simp_rw [blend_eq V _ (v.trans_lt ha) (w.trans_lt ha)]; change chord (G.lieExp (g u)) (G.lieExp (g d)) ≤ _
                rw [mat_eq]; have hg(u : ℝ)(p:u∈Icc 0 1): g u∈Metric.closedBall 0 δ:=by rw [Metric.mem_closedBall,dist_zero_right]; exact (mix_ball p (hz a v) (hz b w)).trans ht.le
                apply le_trans _ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (show k ≤ k+C*V.C^2 from le_add_of_nonneg_right (by positivity)) (abs_nonneg _)) hr); have hy:= h.dist_le_mul (g u) (hg u q) (g d) (hg d i); rw [dist_eq_norm,dist_eq_norm] at hy
                refine le_trans (b:=(K:ℝ)*(|u-d| *(2*V.C*r))/G.colorScale) (div_le_div_of_nonneg_right (hy.trans (mul_le_mul_of_nonneg_left ?_ K.property)) he.le) (Eq.le ?_); swap -- set b
                · unfold k; ring
                rw [show g u-g d=(u-d) • (y-x) from (by unfold g mix; module),norm_smul]; have hv: ‖y-x‖ ≤ 2*V.C*r:=(norm_sub_le ..).trans ((add_le_add (hz b w) (hz a v)).trans_eq (by ring)); exact mul_le_mul_of_nonneg_left hv (abs_nonneg _)
 intro u m x y h v a b z; let X(g: Fin 4 → G.El)(i:Fin 4):= snap G (g i); have c(g : Fin 4 → G.El)(q : ∀ i, G.chord (g i)≤r) : (∀ i,G.lieExp (X g i)=g i) ∧ ‖X g‖ ≤ V.C*r:= ⟨fun i=> V.read _ ((q i).trans ha.le), (pi_norm_le_iff_of_nonneg (by positivity : 0≤V.C*r)).mpr fun i=> hz _ (q i)⟩
 obtain ⟨s,xp⟩:= c x (fun i=>(h i).1); obtain ⟨w,yp⟩:= c y (fun i=>(h i).2); let Z:= mix u (X x) (X y); have he(i): z i=G.lieExp (Z i):=blend_eq V u ((h i).1.trans_lt ha) ((h i).2.trans_lt ha)
 simp_rw [he]; refine (G' u (V.C*r) m v ht (X x) (X y) xp yp ?_ ?_).trans ?_; rw [four,s,s,s,s]; exact a; rw [four,w,w,w,w]; exact b; rw [mul_pow,←mul_assoc]; gcongr; exact le_add_of_nonneg_left hV
end taylor
end chord
end YM.CF.BPress
