import YM.CF.Neige.Ton
set_option autoImplicit false
noncomputable section
namespace YM.CF.Neige
open Char Summit
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric Newt Jet
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
 AnalyticBridge.NonflatCovarianceLocality.Matching
open Push.SectorMeasure Next.Fluctuations Next.SectorChange Next.SectorChange.Wisps Next.SectorChange.Schur PhysicalNext.JointLoad PatchReads
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{A A':Stores S}{F F':Forest S.ratio}{k k':S.Choices} {V W:Config G c}{x C:ℝ}{r l:ℕ}
 {Y: LinkArray G (Frozen A x F)}{Y':LinkArray G (Frozen A' x F')}{o:Site c}
variable {α E:Type} [Fintype α][DecidableEq α] [NormedAddCommGroup E][NormedSpace ℝ E] {p:α→Site c}{a:ℕ} {K v d s t:ℝ} {n:ℕ}
open Finset Filter
open AnalyticBridge.RelativeLogdet Ink
section generic
variable {A :E→ Matrix α α ℝ}{P:E→ℝ→Matrix α α ℝ}{x₀:E}{D' U V' z:ℝ}
lemma transX (ha:Protected n A x₀ C): ContDiffAt ℝ n A x₀:= FreeResolvent.TestD.rectangle_smooth fun i j=>by
 let K:=fun _:E=> (0:Matrix α α ℝ); exact ((cost_alt (g:=K) (f:=A) (show Allows n (fun y=>paintO (A y)-paintO (K y)) x₀ C by simp only [K,map_zero,sub_zero]; exact ha) i j).germ (Eventually.of_forall fun y=>sub_zero (A y i j))).smooth
abbrev keystone(A:E→Matrix α α ℝ) (P:E→ℝ→Matrix α α ℝ) (y:E)(s:ℝ):= A y*P y s
structure PriceW (A:E→Matrix α α ℝ)(P:E→ℝ→Matrix α α ℝ)(n:ℕ)(x:E)(K t:ℝ): Prop where
 pre :Arc (uncurry P) n x
 St : Arc (uncurry (keystone A P)) n x
 Tag : Arc (fun z=>tea_r (A z.1) (P z.1) z.2) n x
 heart (w:ℝ)(hw:w∈Isle): IsUnit (edgeM (A x) w).det
 paid (w:ℝ)(hw:w∈Isle): Protected n (fun y=>keystone A P y w) x K ∧ Protected n (fun y=>tea_r (A y) (P y) w) x t
lemma arcW(h:ContDiffAt ℝ n A x₀)(g:Arc (uncurry P) n x₀):Arc (uncurry (keystone A P)) n x₀ ∧Arc (fun z=>tea_r (A z.1) (P z.1) z.2) n x₀:= by
 refine ⟨fun i hi=> (h.comp (f:=Prod.fst) _ contDiffAt_fst).mul (g i hi),fun i hi=>?_⟩
 exact contDiffAt_const.sub ((contDiffAt_const.add (contDiffAt_snd.smul (h.comp (f:=Prod.fst) (x₀,i) contDiffAt_fst))).mul (g i hi))
lemma PriceW.cheaper(h:PriceW A P n x₀ K t)(hx:K ≤  D')(ht:t ≤  z):PriceW A P n x₀ D' z:=⟨h.pre,h.St,h.Tag,h.heart,fun w hw=> ⟨((h.paid w hw).1).mono hx,((h.paid w hw).2).mono ht⟩⟩
def simplest(A:E→Matrix α α ℝ)(x:E)(_t:ℝ):Matrix α α ℝ:=1
lemma up_p (h:Protected n A x₀ t)(hp:t ≤ 1/2): PriceW A (simplest A) n x₀ t t:=by
 let P :=simplest A; have he : Arc (uncurry P) n x₀:=fun t ht=> contDiffAt_const
 obtain ⟨hg,hT⟩:=arcW (transX h) he
 refine ⟨he,hg,hT,fun w hw=> ?_,fun w hw=> ⟨h.germ (Eventually.of_forall fun y=>by simp only [keystone,P,simplest,Matrix.mul_one]),?_⟩⟩
 swap
 · apply ((wrap_r h (-w)).mono (mul_le_of_le_one_left h.nonneg (abs_neg w |>.trans_le ((abs_of_nonneg hw.1).trans_le hw.2)))).germ; filter_upwards with y; unfold tea_r simplest edgeM AnalyticNext.ConnectedActivity.ResolventVolume.graph; simp
 apply (low_invP (edgeM (A x₀) w) _).1; rw [edgeM,AnalyticNext.ConnectedActivity.ResolventVolume.graph,add_sub_cancel_left,map_smul,norm_smul,Real.norm_eq_abs,abs_of_nonneg hw.1]; exact ((mul_le_of_le_one_left (norm_nonneg _) hw.2).trans h.value).trans hp
lemma PriceW.run(h:PriceW A P n x₀ K t)(ht:0  ≤  t)(hp:t<1):HasSum (pulseX (A x₀) (P x₀)) (Real.log (1+A x₀).det):=by
 -- Ink.Arc slice needs finite dim?
 exact hikes _ _ t K h.pre.slice ht hp (fun w hw=> ⟨h.heart w hw, (h.paid w hw).2.value,(h.paid w hw).1.value⟩)
end generic
end YM.CF.Neige
