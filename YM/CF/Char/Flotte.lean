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
open AnalyticBridge.GaussianFieldAlignment Orthogonal Tensor PhysicalNext.OrderedAffine2B.SymRows
variable {L:Box x A A' F F'} {O:ColorOrtho G (Bond f)}{U: ColorOrtho G (Slots S)}{q:Chi}{d σ E Λ:ℝ}
local notation "N"=> Orthogonal.move (onBond O) L.onKey
private lemma reading (i:Active A x F)(a b: Prices G (Active A x F)):
 ∑ j, a (i,j)* pushed T x V k A F b (i,j) = fderiv ℝ (Char.drive T x V k (Rows.fresh x (shots S x) A F (tape b)) i.val.val) 0 (tape a i):=by
 let Y:= fderiv ℝ (Char.drive T x V k (Rows.fresh x (shots S x) A F (tape b)) i.val.val) 0
 let Q:= tape a i; have he: Q=∑ j,a (i,j) • epsI G j:= ((epsI G).sum_repr Q).symm
 change _= Y Q; rw [he,map_sum]; simp_rw [map_smul]; rfl
lemma Flow.gradientP (p:Flow L O U k k' T V W q d Y Y') (a: Prices G (Active A x F)):
 pushed T x W k' A' F' (N a)=N (pushed T x V k A F a):=by
 let Q:= pushed T x W k' A' F' (N a); let P:=pushed T x V k A F a; let D:= L.onKey
 have he(b:Prices G (Active A' x F')): b ⬝ᵥ Q =b ⬝ᵥ(Orthogonal.move (onBond O) L.onKey P):= by
    obtain ⟨b,rfl⟩:=move_surj (onBond O) L.onKey b; rw [move_dot]; unfold dotProduct; rw [Fintype.sum_prod_type,Fintype.sum_prod_type,← D.sum_comp (fun i=> ∑ j, b (i,j)*P (i,j))]; unfold D P Q; refine Finset.sum_congr rfl fun i _=> ?_
    rw [reading,reading,move_tape]
    have hp:=p.drive a i; rw [← hp,(ortho O _).comp_right_fderiv, map_zero]; rfl
 funext i; simpa using he (Pi.single i 1)
section Hess
private lemma qf_build {ι τ:Type} [Fintype ι] [Fintype τ](A: Matrix (ι × τ) (ι × τ) ℝ) (a b: ι × τ → ℝ): a ⬝ᵥ (A *ᵥ b) = ∑ i:ι, ∑ j:ι, ∑ k:τ,a (i,k)* ∑ l:τ,A (i,k) (j,l)*b (j,l):=by
 unfold mulVec; simp_rw [dotProduct,Fintype.sum_prod_type]; simp only [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _=> by rw [Finset.sum_comm (s:= (Finset.univ:Finset τ))]
private lemma builds (g:G.Color × G.Color→ℝ)(a b: G.Color): iteratedFDeriv ℝ 2 g 0 ![(a,0),(0,b)] =∑ i,a i*∑ j, iteratedFDeriv ℝ 2 g 0 ![(epsI G i,0),(0,epsI G j)] * b j:=by
 let H:=fderiv ℝ (fderiv ℝ g) 0
 let L:= ContinuousLinearMap.inl ℝ G.Color G.Color; let R:= ContinuousLinearMap.inr ℝ G.Color G.Color
 have he(x y:G.Color):iteratedFDeriv ℝ 2 g 0 ![(x,0),(0,y)]=H (L x) (R y):=by simp only [iteratedFDeriv_two_apply,Matrix.cons_val_zero, Matrix.cons_val_one]; rfl
 simp_rw [he]; conv_lhs => rw [show a = ∑ j,a j • epsI G j from ((epsI G).sum_repr a).symm, map_sum,map_sum]
 simp_rw [map_smul,ContinuousLinearMap.sum_apply]; simp only [_root_.smul_apply,smul_eq_mul]; apply Finset.sum_congr rfl; intro j _; congrm _ * ?_
 conv_lhs=> rw [show b= ∑ j,b j • epsI G j from ((epsI G).sum_repr b).symm,map_sum,map_sum]
 simp_rw [map_smul]; simp only [smul_eq_mul, mul_comm]
private def panel_dot(i j: Active A x F)(a b z: Prices G (Active A x F))(V:Config G c) (T:Tube G S)(k:S.Choices):ℝ:=∑ l,a (i,l)* ∑ m, headed T x V k A F z (i,l) (j,m) * b (j,m)
private lemma panel_at(i j: Active A x F)(a b z: Prices G (Active A x F))(V:Config G c) (T:Tube G S)(k:S.Choices): panel_dot i j a b z V T k= if meeting S x i.val.val j.val.val then
 iteratedFDeriv ℝ 2 (Char.curveX T x V k (Rows.fresh x (shots S x) A F (tape z)) i.val.val j.val.val) 0 ![(tape a i,0),(0,tape b j)] else 0:=by
 unfold panel_dot headed; have he (a b:G.ColorIndex): (j,b) ∈ panels A F (i,a)↔ meeting S x i.val.val j.val.val:= Iff.rfl
 simp_rw [Matrix.of_apply, he]
 split
 next hv=> exact (builds _ (tape a i) (tape b j)).symm
 next hv=> simp
end Hess
lemma Flow.headT (p: Flow L O U k k' T V W q d Y Y') (a: Prices G (Active A x F)):
 headed T x W k' A' F' (N a)=warp (onBond O) L.onKey (headed T x V k A F a):=by
 apply warp_of; intro b c'
 rw [qf_build,qf_build]; change ∑ i:Active A' x F', (∑ j:Active A' x F',panel_dot i j (N b) (N c') (N a) W T k')=∑ i,∑ j,panel_dot i j b c' a V T k
 rw [← L.onKey.sum_comp (fun i=>∑ j,panel_dot i j b c' a V T k)]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [← L.onKey.sum_comp (fun j=>panel_dot (L.onKey i) j b c' a V T k)]; refine Finset.sum_congr rfl fun j _=>?_
 rw [panel_at,panel_at]
 have he: meeting S x (L.onKey i).val.val (L.onKey j).val.val ↔ meeting S x i.val.val j.val.val:=by rw [L.atK,L.atK]; exact L.pane _ _
 simp_rw [he]; split
 · rw [move_tape,move_tape]; let P:=ortho O i.val.val; let X:=ortho O j.val.val
   rw [show (onBond O i (tape b _) ,(0:G.Color))=P.prodCongr X (tape b _,0) from Prod.ext rfl (map_zero X).symm,show ((0:G.Color),onBond O j (tape c' _))=P.prodCongr X (0,tape c' _) from Prod.ext (map_zero P).symm rfl]; exact derive2P _ _ _ (p.curveX a i j) _ _
 rfl
lemma Flow.orbitM (p:Flow L O U k k' T V W q d Y Y')(h:T.up.Bounds T.high σ E Λ)(hp:S.patch.Branches S.kernel G) (i:ℕ):
 orbitP T x W k' A' F' q d Y' i=N (orbitP T x V k A F q d Y i):=by
 induction i with
 | zero=> exact p.meanP h hp
 | succ i ih=>
    let a:= orbitP T x V k A F q d Y i
    rw [orbitP,orbitP,ih,swingP,swingP,p.gradientP]; unfold columnX; rw [p.test.kernel.ends]; let I:= columnX T x V k A F; let Z:= warp (onBond O) L.onKey
    change _-(Z I).transpose*ᵥ N (pushed T x V k A F a)= _
    have he:(Z I).transpose= Z I.transpose:=by unfold Z warp; rw [transpose_dressed, transpose_submatrix]
    rw [he,warp_mv]; symm; exact Matrix.mulVec_sub ..
end YM.CF.Char
