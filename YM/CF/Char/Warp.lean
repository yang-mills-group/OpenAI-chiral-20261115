/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.CF.Char.Calls
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
private lemma bias_p (a : Prices G (Active A x F)) (Y : LinkArray G (Frozen A x F))(q:Chi)(d:ℝ)
    (h : S.patch.Branches S.kernel G) {σ E Λ : ℝ} (hT : T.up.Bounds T.high σ E Λ) :
    let X := shots S x
    a ⬝ᵥ Offset.b T x k A F q d Y V = Rows.slip * Rows.slip * ∑ i : Slots S, inner ℝ
      (Rows.bump T x V k (Rows.fresh x X A F (tape a)) i)
      ((Offset.fixedBase T x V k+Rows.bump T x V k (Rows.input x A F (autoShell q d V Y))) i) := by
  intro X
  rw [Offset.b,dotProduct_transpose_mulVec,dotProduct_comm, Rows.moved _ _ _ _ _ _ _ hT,Offset.f0]
  have hx (u v : LogArray G (Slots S)) : tape.symm u ⬝ᵥ tape.symm v = ∑ i, inner ℝ (u i) (v i) := by
    simp_rw [dotProduct, Fintype.sum_prod_type,Work.F03.inner_color]; rfl
  rw [hx,Finset.mul_sum]; refine Finset.sum_congr rfl fun ⟨s,i⟩ _ => ?_
  dsimp only [Rows.selected,Rows.restrict]; split
  · rw [real_inner_smul_left,real_inner_smul_right,mul_assoc]
  next hh => rw [skip_bump T x V k A F s i _ h hh]; simp
lemma derive2P {α β:Type} [NormedAddCommGroup α][NormedSpace ℝ α][NormedAddCommGroup β][NormedSpace ℝ β] [CompleteSpace α] [CompleteSpace β] (f:α→ℝ)(g:β→ℝ)(L:β≃L[ℝ] α)(h:f ∘ L=g)(a b:β):
 iteratedFDeriv ℝ 2 f 0 ![L a,L b]=iteratedFDeriv ℝ 2 g 0 ![a,b]:=by
 simp only [iteratedFDeriv_two_apply,Matrix.cons_val_zero,Matrix.cons_val_one]
 let U:= L.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ); let x:= fderiv ℝ f
 have hv:fderiv ℝ g= U ∘ x ∘ L:=by
    funext y; rw [← h,L.comp_right_fderiv]; ext z; change x (L y) (L z)=_; rfl
 have he: fderiv ℝ (fderiv ℝ g) 0 a = U ((fderiv ℝ x 0) (L a)):=by
    rw [hv,U.comp_fderiv,L.comp_right_fderiv,map_zero]; rfl
 rw [he]; rfl
structure Flow (L:Box x A A' F F') (O:ColorOrtho G (Bond f))(C: ColorOrtho G (Slots S))(k k': S.Choices)(T: Tube G S)(V W:Config G c)(q:Chi)(d:ℝ)(Y:LinkArray G (Frozen A x F))(Y':LinkArray G (Frozen A' x F')):Prop where
 test : PhysicalNext.OrderedAffine2B.SymRows.Test L O C V W k k' T q d Y Y'
 heights (a:Directions G f): rack T x W k' (Tensor.lifting O L.edges a)=rack T x V k a
variable {L:Box x A A' F F'} {O:ColorOrtho G (Bond f)}{U: ColorOrtho G (Slots S)}{q:Chi}{d σ E X:ℝ} 
local notation "N"=> Orthogonal.move (onBond O) L.onKey
lemma Flow.bias (p:Flow L O U k k' T V W q d Y Y')(h:T.up.Bounds T.high σ E X)(hp:S.patch.Branches S.kernel G):
 Offset.b T x k' A' F' q d Y' W = N (Offset.b T x k A F q d Y V):=by
 have he(v: Prices G (Active A' x F')): v ⬝ᵥ Offset.b T x k' A' F' q d Y' W = v ⬝ᵥ N (Offset.b T x k A F q d Y V):=by
    obtain ⟨a,rfl⟩:=move_surj (onBond O) L.onKey v
    rw [bias_p _ _ _ _ hp h,move_dot,bias_p (V:=V) _ _ _ _ hp h,funext p.test.y,frozen_move L.edges O _ L.atH,fresh_move L.edges O _ L.atK]
    apply congr_arg; let v:= Rows.bump T x V k (Rows.fresh x (shots S x) A F (tape a)); let u:=Offset.fixedBase T x V k + Rows.bump T x V k (Rows.input x A F (autoShell q d V Y))
    refine Eq.trans ?_ (Equiv.sum_comp L.slots (fun i=>inner ℝ (v i) (u i)))
    unfold v u; refine Finset.sum_congr rfl fun i _=>?_ ; simp_rw [Pi.add_apply,p.test.wave,p.test.frame,← (U i).map_add]; exact (U i).inner_map_map ..
 funext i; simpa using he (Pi.single i 1)
lemma Flow.meanP (p:Flow L O U k k' T V W q d Y Y')(h:T.up.Bounds T.high σ E X)(hp:S.patch.Branches S.kernel G):
 Offset.mean T x k' A' F' q d Y' W = N (Offset.mean T x k A F q d Y V):=by unfold Offset.mean; rw [p.test.kernel.ends,p.bias h hp,negative]
private lemma elev (L:Box x A A' F F')(O:ColorOrtho G (Bond f))(i:Bond f)(v:G.Color): Tensor.lifting O L.edges (Pi.single (L.edges i) v) = Pi.single i (O i v):=by
 ext1 j; rw [lifting_apply]; by_cases h:j=i; · simp [h]
 simp [h] -- tune
lemma solo (i:Active A' x F')(v:G.Color): Pi.single i.val.val (O i.val.val v) = Tensor.lifting O L.edges (Pi.single (L.onKey i).val.val v):= by rw [L.atK,elev]
lemma Flow.drive (p:Flow L O U k k' T V W q d Y Y')(a: Prices G (Active A x F)) (i:Active A' x F'):
 drive T x W k' (Rows.fresh x (shots S x) A' F' (tape (Orthogonal.move (onBond O) L.onKey a))) i.val.val ∘ (ortho O i.val.val)= drive T x V k (Rows.fresh x (shots S x) A F (tape a)) (L.onKey i).val.val:=by
 ext1 v
 rw [fresh_move _ _ _ L.atK]; change Char.drive T x W k' _ i.val.val (O i.val.val v)=_
 unfold Char.drive; rw [solo (L:=L) i v,← map_add,p.heights,p.heights]
lemma Flow.curveX (p:Flow L O U k k' T V W q d Y Y')(a: Prices G (Active A x F)) (i j:Active A' x F'):
 Char.curveX T x W k' (Rows.fresh x (shots S x) A' F' (tape (Orthogonal.move (onBond O) L.onKey a))) i.val.val j.val.val ∘ ((ortho O i.val.val).prodCongr (ortho O j.val.val))= Char.curveX T x V k (Rows.fresh x (shots S x) A F (tape a)) (L.onKey i).val.val (L.onKey j).val.val:=by
 ext1 v; rw [fresh_move L.edges O L.onKey L.atK]; change Char.curveX _ _ _ _ _ _ _ (O i.val.val v.1,O j.val.val v.2)=_
 unfold Char.curveX; rw [solo (L:=L),solo (L:=L),← map_add,← map_add,p.heights,p.heights]
end YM.CF.Char
