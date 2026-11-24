import YM.CF.Char.Bois
import YM.CF.Char.Puste
import YM.CF.Char.Flotte
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
open AnalyticBridge.GaussianFieldAlignment Orthogonal Tensor PhysicalNext.OrderedAffine2B.SymRows Locations Summit
-- Newton correction enabled only outside seed guard; no algorithm branches on values here.
def green (x:ℝ)(S:StepData c f)(A:Stores S)(e:Bond f): Prop:=∀ p∈Next.SectorChange.points S e,p∉ A.dome (40*radiusB x)
def liftN(T:Tube G S)(x:ℝ)(V:Config G c)(k:S.Choices)(A:Stores S)(F:Forest S.ratio)(q:Chi)(d:ℝ)(Y:LinkArray G (Frozen A x F))(l:ℕ)(i:Rows.In x A F (G:=G)):ℝ:= if green x S A i.1.val.val then orbitP T x V k A F q d Y l i else Offset.mean T x k A F q d Y V i
def hessN(T:Tube G S)(x:ℝ)(V:Config G c)(k:S.Choices)(A:Stores S)(F:Forest S.ratio)(q:Chi)(d:ℝ)(Y:LinkArray G (Frozen A x F))(l:ℕ):Gaussian.Table (Rows.In x A F (G:=G)):= of fun i j=>if green x S A i.1.val.val ∧ green x S A j.1.val.val then AnalyticBridge.GaussianFieldAlignment.Relative.symPart (headed T x V k A F (orbitP T x V k A F q d Y l)) i j else Rows.gram T x V k (shots S x) A F i j
variable {q:Chi}{d σ E Λ:ℝ}{i j: Rows.In x A F (G:=G)}{i' j':Rows.In x A' F' (G:=G)}
lemma green_pack (h:Scan S x (front A F i) (40*radiusB x+1) A A' F F' k k' V W Y Y')(hi:PatchReads.lift i=PatchReads.lift i'):
 green x S A i.1.val.val ↔ green x S A' i'.1.val.val:=by
 unfold green; rw [← (pairX hi).1]; apply forall_congr'; intro y; apply forall_congr'; intro hy
 have hf:separation (front A F i) y≤1:= meetings _ hy; unfold Stores.dome; simp_rw [halo_spec, not_exists]
 refine forall_congr' fun p=> not_congr (and_congr_left fun hp=> h.marks p ?_); have he:= separation_triangle (front A F i) y p; rw [separation_comm y p] at he; omega
lemma liftN_read (hp:Ready T x)(h:Scan S x (front A F i) ((l+41)*radiusB x) A A' F F' k k' V W Y Y')(hi:PatchReads.lift i=PatchReads.lift i'):
 liftN T x V k A F q d Y l i=liftN T x W k' A' F' q d Y' l i':=by
 have hv:=hp.length; unfold liftN; rw [green_pack (h.lower (by rw [Nat.add_mul]; omega)) hi]; split
 · exact orbitX hp q d _ (h.lower (by simp_rw [Nat.add_mul]; omega)) hi
 exact meetX hp (h.lower (by rw [Nat.add_mul]; omega)) hi _ _
lemma sym_hessN (l:ℕ): (hessN T x V k A F q d Y l).IsSymm:=by
 ext i j; simp_rw [Matrix.transpose_apply,hessN,Matrix.of_apply]; simp only [and_comm]; split
 · simp only [Relative.symPart,Matrix.smul_apply,Matrix.add_apply,Matrix.transpose_apply]; rw [add_comm]
 exact (show Matrix.IsSymm (Rows.gram T x V k (shots S x) A F) by unfold Rows.gram Matrix.IsSymm; simp [Matrix.transpose_mul]).apply i j
lemma gram_off (hr:Ready T x) (he:j∉panels A F i)(hp:1000 ≤ radiusB x): Rows.gram T x V k (shots S x) A F i j=0:=by
 have hy:=not_here hr.inputs hp he -- import!
 unfold Rows.gram; rw [Matrix.mul_apply]; apply Finset.sum_eq_zero; intro b _; rw [Matrix.transpose_apply]; by_cases h:span S.patch x < separation (down S b) (front A F i)
 · rw [move_range hr.rules h,zero_mul]
 rw [move_range hr.rules (i:=b) (j:=j) _,mul_zero]; have ht:= separation_triangle (front A F i) (down S b) (front A F j); rw [separation_comm (front A F i) (down S b)] at ht; omega
lemma hessN_off(hr:Ready T x)(he:j∉panels A F i)(hp:1000 ≤ radiusB x)(l:ℕ): hessN T x V k A F q d Y l i j=0:=by
 have hm : i∉panels A F j:= mt (meeting_comm ..).2 he
 unfold hessN; rw [Matrix.of_apply]; split
 · rw [Relative.symPart,Matrix.smul_apply,Matrix.add_apply,Matrix.transpose_apply,headed,Matrix.of_apply,if_neg he,Matrix.of_apply,if_neg hm,add_zero,smul_zero]
 exact gram_off hr he hp
lemma hessN_read (hp:Ready T x)(h:Scan S x (front A F i) ((l+42)*radiusB x) A A' F F' k k' V W Y Y')(hi:PatchReads.lift i=PatchReads.lift i')(hj:PatchReads.lift j=PatchReads.lift j')(ht:1000 ≤radiusB x):
 hessN T x V k A F q d Y l i j=hessN T x W k' A' F' q d Y' l i' j':=by
 by_cases he:j∈panels A F i; swap
 · rw [hessN_off hp he ht, hessN_off hp (mt ((meetA hi hj).mpr) he) ht]
 have hx:=ball_member he; rw [Nat.add_mul] at h
 unfold hessN; simp only [Matrix.of_apply]; rw [green_pack (h.lower (by omega)) hi,green_pack (i:=j) (h.shrink (by omega)) hj]; split
 · let X:=l*radiusB x
   have hh {p: Rows.In x A F (G:=G)}{p':Rows.In x A' F' (G:=G)}{u:Rows.In x A F (G:=G)}{u':Rows.In x A' F' (G:=G)} (hP:Scan S x (front A F p) (X+41*radiusB x) A A' F F' k k' V W Y Y')(hq:PatchReads.lift p=PatchReads.lift p')(hu:PatchReads.lift u=PatchReads.lift u'): headed T x V k A F (orbitP T x V k A F q d Y l) p u=headed T x W k' A' F' (orbitP T x W k' A' F' q d Y' l) p' u':=by
    apply head_read hp (hP.lower (by omega)) _ hq hu
    intro j j' hj hv; apply orbitX hp _ _ _ (hP.shrink ?_) hv; rw [Nat.add_mul]; unfold X; omega
   unfold Relative.symPart; simp only [Matrix.smul_apply,Matrix.add_apply,Matrix.transpose_apply]; rw [hh (p:=i) (h.lower (by unfold X; omega)) hi hj,hh (p:=j) (h.shrink (by unfold X; omega)) hj hi]
 exact gram_eq hp.rules (h.lower (by have H:=hp.inputs; omega)) hi hj
lemma green_map(s:Signed)(b:Site c)(A: Stores S)(x:ℝ)(e:Bond f): green x S (book s b A) e↔ green x S A (StepData.sendBonds s (S.ratio.embed b) e):=by change _↔green x S A (sendEdge s (S.ratio.embed b) e); unfold green; rw [Tensor.moves_points]; simp only [Set.forall_mem_image,dome_map]
section actors
variable {X:Box x A A' F F'} {O:ColorOrtho G (Bond f)}{U: ColorOrtho G (Slots S)}
def Flows(X:Box x A A' F F'):=∀ i, green x S A' i ↔ green x S A (X.edges i)
lemma boxL (h:Flow X O U k k' T V W q d Y Y')(hx:Flows X)(hr: S.patch.Branches S.kernel G)(hp:T.up.Bounds T.high σ E Λ):
 liftN T x W k' A' F' q d Y' l=Orthogonal.move (onBond O) X.onKey (liftN T x V k A F q d Y l):=by
 apply tape.injective; funext i; rw [move_tape]
 let j:= X.onKey i; have he: green x S A' i.val.val ↔ green x S A j.val.val:=by unfold j; rw [X.atK,hx]
 by_cases hh:green x S A' i.val.val
 · rw [show tape (liftN T x W k' A' F' q d Y' l) i=tape (orbitP T x W k' A' F' q d Y' l) i from ?_,show tape (liftN T x V k A F q d Y l) j=tape (orbitP T x V k A F q d Y l) j from ?_,h.orbitM hp hr,move_tape]
   all_goals ext k; simp only [tape_ap,liftN]; first| exact if_pos hh| exact if_pos (he.mp hh)
 rw [show tape (liftN T x W k' A' F' q d Y' l) i=tape (Offset.mean T x k' A' F' q d Y' W) i from ?_,show tape (liftN T x V k A F q d Y l) (X.onKey i)=tape (Offset.mean T x k A F q d Y V) j from ?_,h.meanP hp hr,move_tape]
 all_goals ext k; simp only [tape_ap,liftN]; first| exact if_neg hh| exact if_neg (mt he.mpr hh)
lemma boxV (h:Flow X O U k k' T V W q d Y Y')(hx:Flows X)(hr:S.patch.Branches S.kernel G)(hp:T.up.Bounds T.high σ E Λ)(l:ℕ):
 hessN T x W k' A' F' q d Y' l= Orthogonal.warp (onBond O) X.onKey (hessN T x V k A F q d Y l):=by
 let R:= onBond (A:=A') (F:=F') (x:=x) O; ext ⟨i,u⟩ ⟨j,v⟩
 rw [warp,dressed_apply,hessN,Matrix.of_apply]
 have he : green x S A (X.onKey i).val.val ∧ green x S A (X.onKey j).val.val ↔ green x S A' i.val.val ∧ green x S A' j.val.val := by rw [X.atK,X.atK,hx,hx]
 split
 next ht=>
    rw [h.orbitM hp hr, h.headT, warp_sym, warp,dressed_apply]; simp only [Matrix.submatrix_apply,Orthogonal.addr,Equiv.prodCongr_apply,Equiv.refl_apply,hessN,Matrix.of_apply,Prod.map_apply, if_pos (he.mpr ht)]
 next ht=>
    rw [h.test.kernel.same,warp,dressed_apply]; simp only [Matrix.submatrix_apply,Orthogonal.addr,Equiv.prodCongr_apply,Equiv.refl_apply,hessN, Matrix.of_apply,Prod.map_apply,if_neg (mt he.mp ht)]
end actors
end YM.CF.Char
