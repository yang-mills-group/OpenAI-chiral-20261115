import YM.CF.Neige.Fal
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
variable {q:Chi}{D v' A₀ m:ℝ}{i j: Rows.In x A F (G:=G)}{i' j':Rows.In x A' F' (G:=G)}
variable {a b w:ℕ}
section sheets
variable (k : S.Choices) (V : Config G c)(Y : LinkArray G (Frozen A x F))
def Sample (r:ℕ)(M: Gaussian.Table (Rows.In x A F (G:=G)))(k': S.Choices)(W: Config G c)(Y': LinkArray G (Frozen A' x F'))(N: Gaussian.Table (Rows.In x A' F' (G:=G))):Prop:=∀ i i' j j',Scan S x (front A F i) r A A' F F' k k' V W Y Y'→ PatchReads.lift i=PatchReads.lift i'→PatchReads.lift j=PatchReads.lift j'→ M i j=N i' j'
variable {M R:Gaussian.Table (Rows.In x A F (G:=G))}{N Q:Gaussian.Table (Rows.In x A' F' (G:=G))}{k V Y}
lemma tile_mul(h:Sample k V Y r M k' W Y' N)(hp:Sample k V Y l R k' W Y' Q)(ht:Names M a)(hz:Names N a)(hv:max r (a+l) ≤ b): Sample k V Y b (M*R) k' W Y' (N*Q):=by
 intro i i' j j' hy hi hj; rw [Matrix.mul_apply, Matrix.mul_apply]; have he:=max_le_iff.mp hv
 refine PatchReads.sum_eq (hy.lower (r':=a) (by omega)) (fun j hj=>by rw [ht.rank i j hj,zero_mul]) (fun j hj=>by rw [hz.rank i' j ((faces hi) ▸ hj),zero_mul]) fun p p' hh h₀=> ?_
 rw [h i i' p p' (hy.lower he.1) hi h₀,hp p p' j j' (hy.shrink (by omega)) h₀ hj]
lemma one_eqin (hp: PatchReads.lift i=PatchReads.lift i')(hz:PatchReads.lift j=PatchReads.lift j'):
 (1: Gaussian.Table (Rows.In x A F (G:=G))) i j=(1: Gaussian.Table (Rows.In x A' F' (G:=G))) i' j':=by
 rw [one_apply,one_apply]; by_cases hx:i=j
 · subst j; rw [if_pos rfl,if_pos (lifting_injective A' x F' (hp.symm.trans hz))]
 rw [if_neg hx,if_neg (fun ht=> hx (lifting_injective _ _ _ (hp.trans (ht.symm ▸ hz).symm)))]
lemma tile_pt(h:Sample k V Y r M k' W Y' N)(hp:Names M a)(hz:Names N a)(hv:a+r ≤ b): Sample k V Y b (port M) k' W Y' (port N):=by
 intro i i' j j' hy hi hj; unfold port punt; rw [pow_two, pow_two]; simp only [Matrix.add_apply,Matrix.neg_apply, Matrix.smul_apply]; rw [one_eqin hi hj,h i i' j j' (hy.lower (by omega)) hi hj,tile_mul h h hp hz (by omega) i i' j j' hy hi hj]
end sheets
lemma Sample.more {Z:Gaussian.Table (Rows.In x A F (G:=G))}{Z':Gaussian.Table (Rows.In x A' F' (G:=G))}(h:Sample k V Y r Z k' W Y' Z')(hh:r ≤ l): Sample k V Y l Z k' W Y' Z':=fun i i' j j' h' =>h _ _ _ _ (h'.lower hh)
lemma edgeBill (hr:Ready T x): Sample k V Y (radiusB x) (bark x V T k A F) k' W Y' (bark x W T k' A' F'):=by
 intro i i' j j' h hi hj; have hp := tooth (V:=V) (k:=k) hr A F; have hx := tooth (V:=W) (k:=k') hr A' F'; by_cases he:separation (front A F i) (front A F j)  ≤ radiusB x/20
 · exact bark_read hr (h.shrink (by omega)) hj hi
 rw [hp.rank _ _ (lt_of_not_ge he),hx.rank _ _ (by rw [←faces hi,← faces hj]; omega)]
lemma bankPass(hr:Ready T x)(hp:1000 ≤ radiusB x): Sample k V Y ((l+45)*radiusB x) (bankX T x A F k q D Y l V) k' W Y' (bankX T x A' F' k' q D Y' l W):=by
 let L:=radiusB x; let b:=l*L; let X:=bark x V T k A F; let Z:= bark x W T k' A' F'; let M:=hessN T x V k A F q D Y l; let M':=hessN T x W k' A' F' q D Y' l
 have hh:Sample k V Y L X k' W Y' Z:= edgeBill hr
 have hX: Sample k V Y L X.transpose k' W Y' Z.transpose:=fun i i' j j' h hi hj=>bark_read hr (h.lower (by unfold L; omega)) hi hj
 have ht:Sample k V Y ((l+42)*L) M k' W Y' M':= fun i i' j j' h hi hj=> Char.hessN_read hr h hi hj hp
 have hQ: Names M (L/20):= ⟨fun i j hh=> hessN_off hr (fun he=> hh.not_ge (ball_member he)) hp l⟩; have hP:Names M' (L/20):= ⟨fun i j hh=> hessN_off hr (fun he=> hh.not_ge (ball_member he)) hp l⟩
 have hw:= tooth (V:=V) (k:=k) hr A F; have hw':= tooth (V:=W) (k:=k') hr A' F'; have hf:=tile_mul hX ht hw.turnt hw'.turnt (b:=b+43*L) (by simp_rw [Nat.add_mul]; unfold b L at *; omega)
 have hf':= tile_mul hf hh (hw.turnt.maps hQ) (hw'.turnt.maps hP) (b:=(l+45)*L) (by rw [Nat.add_mul]; unfold b L; omega)
 intro i i' j j' h hi hj; unfold bankX perturb; simp only [Matrix.sub_apply]; rw [one_eqin hi hj]; exact congr_arg (·- (_:Gaussian.Table _ ) i' j') (hf' i i' j j' h hi hj) -- tune
lemma layPt(hr:Ready T x)(hp:1000 ≤ radiusB x): Sample k V Y ((l+48)*radiusB x) (layX T x A F k q D Y l V) k' W Y' (layX T x A' F' k' q D Y' l W):=by
 let L:=radiusB x; have hf := bankPass (k:=k) (V:=V) (Y:=Y) (l:=l) (q:=q) (D:=D) (k':=k') (W:=W) (Y':=Y') hr hp -- tune
 have hh := tile_pt hf (supportV hr hp l) (supportV hr hp l) (b:=(l+46)*L) (by unfold L; simp_rw [Nat.add_mul]; omega)
 exact tile_mul (edgeBill hr) hh (tooth hr _ F) (tooth hr _ F') (by unfold L; simp_rw [Nat.add_mul]; omega)
end YM.CF.Neige
