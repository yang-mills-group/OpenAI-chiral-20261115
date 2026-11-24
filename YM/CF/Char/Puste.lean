import YM.CF.Char.Warp
set_option autoImplicit false
noncomputable section
namespace YM.CF.Char
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric Newt Jet
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
 AnalyticBridge.NonflatCovarianceLocality.Matching
open Push.SectorMeasure Next.Fluctuations Next.SectorChange Next.SectorChange.Wisps Next.SectorChange.Schur PhysicalNext.JointLoad PatchReads
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{A A':Stores S}{F F':Forest S.ratio}{k k':S.Choices} {V W:Config G c}{x C:ℝ}{r l:ℕ}
 {Y: LinkArray G (Frozen A x F)}{Y':LinkArray G (Frozen A' x F')}{o:Site c}
open AnalyticBridge.GaussianFieldAlignment Orthogonal Tensor PhysicalNext.OrderedAffine2B.SymRows Summit AnalyticBridge.RelativeLogdet
variable {X:Box x A A' F F'} {O:ColorOrtho G (Bond f)}{U: ColorOrtho G (Slots S)}{q:Chi}{d σ E Λ:ℝ}
section warp
variable {α β : Type} [Fintype α][Fintype β][DecidableEq α][DecidableEq β] (I:ColorOrtho G α)(Q:α≃β)
local notation "O₁"=> Orthogonal.warp I Q
lemma span_eqX(t:ℝ)(A:Gaussian.Table (β × G.ColorIndex)): Summit.spanX (O₁ A) t = O₁ (Summit.spanX A t):=by
 let e:= Orthogonal.addr Q G.ColorIndex
 have he : O₁ (1:Gaussian.Table (β×G.ColorIndex))=1:=by unfold Orthogonal.warp Orthogonal.dressed; rw [Matrix.submatrix_one_equiv,mul_one]; exact priced_reverse ..
 unfold Summit.spanX; rw [← he]; unfold Orthogonal.warp dressed
 simp only [submatrix_add,submatrix_smul,Pi.add_apply,Pi.smul_apply,Matrix.mul_add, Matrix.add_mul,Matrix.smul_mul,Matrix.mul_smul]
lemma sheetX (A:Gaussian.Table (β × G.ColorIndex)) {w:α→Set α}{W: β × G.ColorIndex→Set (β × G.ColorIndex)}(h:∀ i, addr Q _ ⁻¹' W (addr Q _ i)=together _ w i)(t:ℝ): pie (together G.ColorIndex w) (Summit.spanX (O₁ A) t) 0=O₁ (pie W (Summit.spanX A t) 0):=by rw [pie,pie,span_eqX,zero_smul, add_zero,zero_smul,add_zero]; apply warp_per; exact h
variable {W : β × G.ColorIndex → Set (β × G.ColorIndex)}
omit [Fintype α] [DecidableEq α] in
lemma flow_pie {A : Gaussian.Table (β × G.ColorIndex)} {r:ℝ}(p:FreeResolvent.Gap A r)(hp:0<r)(h:∀ i,i ∈ W i)(i j:β × G.ColorIndex): IntegrableOn (fun t=>pie W (Summit.spanX A t) 0 i j) Summit.Isle:=by
 let H (z:ℝ×ℝ):= Summit.spanX A z.2; have he: Ink.Arc H 0 0:= fun t _=> (((contDiffAt_const.sub (contDiffAt_snd (n:=0))).pow 2).smul (g:=fun _=>A) contDiffAt_const).add (((contDiffAt_snd (n:=0)).pow 2).smul (g:=fun _=>1) contDiffAt_const)
 have hz: Ink.Arc (fun y=>pie W (H y) 0) 0 0:= Summit.pie_s H he h (fun t _=> Summit.span_gap (A:=fun _ : ℝ=>A) (x:=0) p hp.le t) (half_pos (lt_min hp zero_lt_one))
 exact Ink.Arc.int (g:=fun z => pie W (H z) 0 i j) (x:=0) (k:=0) (fun t ht=> typed (hz t ht) i j)
lemma sheetM(A:Gaussian.Table (β×G.ColorIndex)){r:ℝ}(p:FreeResolvent.Gap A r)(hp:0<r){w:α→Set α}(hh:∀ i,i∈W i)(h:∀ i, addr Q _ ⁻¹' W (addr Q _ i)=together _ w i): mild (together G.ColorIndex w) (O₁ A)=O₁ (mild W A):=by
 let Z(t:ℝ):=pie W (spanX A t) 0; have ht(i j):IntegrableOn (fun x=>Z x i j) Isle:=flow_pie p hp hh i j
 unfold mild; simp_rw [sheetX I Q A h]; unfold Orthogonal.warp dressed
 simp only [submatrix_smul,Pi.smul_apply,Matrix.mul_smul, Matrix.smul_mul]; congr 1
 ext ⟨i,u⟩ ⟨j,v⟩
 change (∫ t in Isle, O₁ (Z t) (i,u) (j,v))=dressed (asMatrix I) _ (i,u) (j,v)
 unfold warp; simp_rw [dressed_apply, Matrix.submatrix_apply, Matrix.of_apply]
 let c:=asMatrix I; let e:=addr Q G.ColorIndex; let FF (a b:G.ColorIndex)(t:ℝ):=c i u a* Z t (e (i,a)) (e (j,b))*c j v b; have hi(a b):IntegrableOn (FF a b) Isle:= ((ht _ _).const_mul _).mul_const _
 simp_rw [Finset.sum_mul]; rw [integral_finsetSum _ fun b _=>integrable_finsetSum _ fun a _=>hi a b]; refine Finset.sum_congr rfl fun b _=>?_
 rw [integral_finsetSum _ fun a _=> hi a b]; exact Finset.sum_congr rfl fun a _=> by rw [integral_mul_const,integral_const_mul]
end warp
lemma boxH {r:ℝ}(hp:Flow X O U k k' T V W q d Y Y')(p:FreeResolvent.Gap (Rows.gram T x V k (shots S x) A F) r)(hr:0<r)(h:120 ≤ radiusB x): bark x W T k' A' F'=Orthogonal.warp (onBond O) X.onKey (bark x V T k A F):=by
 unfold bark; rw [hp.test.kernel.same]; apply sheetM _ _ _ p hr (per_self (boards A F G h)) (w:=endLinks A' F' x)
 intro i; ext j; change meeting S x (X.onKey i.1).val.val (X.onKey j.1).val.val ↔ meeting S x i.1.val.val j.1.val.val; rw [X.atK,X.atK]; exact X.pane _ _
end YM.CF.Char
