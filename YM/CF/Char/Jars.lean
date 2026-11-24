import YM.CF.Char.Velvet
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
open Summit
variable {i j:Rows.In x A F (G:=G)}{i' j': Rows.In x A' F' (G:=G)}
local notation "ℋ"=>panels A F (x:=x) (G:=G)
local notation "🅗"=>panels A' F' (x:=x) (G:=G)
private def here_p(h : Scan S x (front A F i) (radiusB x/20) A A' F F' k k' V W Y Y')(hi:PatchReads.lift i=PatchReads.lift i')(j:ℋ i): 🅗 i':=by
 let J:= h.switch j.val.1 (ball_member j.property)
 let t:Rows.In x A' F' (G:=G):=(J.choose,j.val.2)
 have he: PatchReads.lift j.val=PatchReads.lift t:=Prod.ext J.choose_spec rfl
 exact ⟨t,(meetA hi he).mp j.property⟩
private lemma here_h(h : Scan S x (front A F i) (radiusB x/20) A A' F F' k k' V W Y Y')(hi:PatchReads.lift i=PatchReads.lift i')(j:ℋ i): PatchReads.lift j.val=PatchReads.lift (here_p h hi j).val:=Prod.ext (h.switch j.val.1 (ball_member j.property)).choose_spec rfl
private lemma sigl {α β:Type} [Fintype α] [Fintype β][DecidableEq α][DecidableEq β] (T: Gaussian.Table α)(V :Gaussian.Table β)(e:α≃β)(he:T=V.submatrix e e): shard T=(shard V).submatrix e e:=by
 ext i j; unfold shard; simp only [Matrix.submatrix_apply, Matrix.smul_apply]; unfold glassX; simp only [Matrix.of_apply]; congrm _ • ?_; apply setIntegral_congr_fun measurableSet_Icc; intro x hx; dsimp only; rw [show spanX T x=(spanX V x).submatrix e e from ?_, Matrix.inv_submatrix_equiv, Matrix.submatrix_apply]
 unfold spanX; rw [he]; simp only [Matrix.submatrix_add,Matrix.submatrix_smul,Pi.add_apply,Pi.smul_apply,Matrix.submatrix_one_equiv]
private lemma sig_at {α β:Type} [Fintype α][Fintype β][DecidableEq α][DecidableEq β]{w:α→Set α}{W:β→Set β}{i j:α}{i' j' :β}(A:Gaussian.Table α)(B:Gaussian.Table β)(hi:i∈w j)(hj:j∈w j)(hi':i'∈W j')(hj':j'∈W j')(e:w j≃ W j')(he:e ⟨i,hi⟩=⟨i',hi'⟩)(hx:e ⟨j,hj⟩=⟨j',hj'⟩)(hp:principal A (w j)=(principal B (W j')).submatrix e e): mild w A i j=mild W B i' j':=by
 rw [mild_read _ _ _ _ hi hj,mild_read _ _ _ _ hi' hj', sigl _ _ e hp,Matrix.submatrix_apply, he,hx]
lemma bark_read(hr:Ready T x)(h:Scan S x (front A F i) (radiusB x/10) A A' F F' k k' V W Y Y')(hi:PatchReads.lift i=PatchReads.lift i')(hj:PatchReads.lift j=PatchReads.lift j'):
 bark x V T k A F j i=bark x W T k' A' F' j' i':=by
 unfold bark; by_cases he:j∈ℋ i; swap; · rw [mild_zero ℋ _ _ _ he,mild_zero 🅗 _ _ _ (mt ((meetA hi hj).mpr) he)]
 have hx:= per_self (boards A F G hr.length) i
 let L:= h.lower (r':=radiusB x/20) (by omega)
 let e:ℋ i≃ 🅗 i':= { toFun:= here_p L hi, invFun:=here_p ((faces hi) ▸ L.turn) hi.symm, left_inv:=fun i=>Subtype.ext ((lifting_injective ..) ((here_h L hi i).trans (here_h ..)).symm), right_inv:=fun j=> Subtype.ext ((lifting_injective ..) ((here_h _ _ j).trans (here_h ..)).symm)}
 let M:= principal (Rows.gram T x V k (shots S x) A F) (ℋ i)
 let M':= principal (Rows.gram T x W k' (shots S x) A' F') (🅗 i')
 have hh : M=M'.submatrix e e := by
    ext x y; have hp:=ball_member x.property; exact gram_eq hr.rules (h.shrink (by have h:=hr.inputs; omega)) (here_h L hi x) (here_h L hi y)
 have ht (x: ℋ i)(y:🅗 i')(hv:PatchReads.lift x.val=PatchReads.lift y.val): e x=y:=Subtype.ext ((lifting_injective ..) ((here_h L hi x).symm.trans hv))
 exact sig_at _ _ he hx ((meetA hi hj).1 he) ((meetA hi hi).1 hx) e (ht _ _ hj) (ht _ _ hi) hh
end YM.CF.Char
