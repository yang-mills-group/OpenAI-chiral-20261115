import YM.CF.Char.Pewter
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
open AnalyticBridge.GaussianFieldAlignment Orthogonal Tensor PhysicalNext.OrderedAffine2B.SymRows Gauges
variable {i j: Rows.In x A F (G:=G)}{s M d v D A₀ E:ℝ}{n:ℕ}{q:Chi}{z:Site c→G.El}{R:Directions G c→ Mast G c}
def graft(T:Tube G S)(x:ℝ)(V:Config G c)(k:S.Choices)(A:Stores S)(F:Forest S.ratio)(q:Chi)(d:ℝ)(Y:LinkArray G (Frozen A x F))(l:ℕ):= Relative.symPart (headed T x V k A F (orbitP T x V k A F q d Y l))-Rows.gram T x V k (shots S x) A F
def driftN(T:Tube G S)(x:ℝ)(V:Config G c)(k:S.Choices)(A:Stores S)(F:Forest S.ratio)(q:Chi)(d:ℝ)(Y:LinkArray G (Frozen A x F))(l:ℕ):=hessN T x V k A F q d Y l-Rows.gram T x V k (shots S x) A F
lemma asMatrix_bound {α:Type} (O: ColorOrtho G α)(i:α)(j k): |asMatrix O i j k|≤1:= by
 rw [asMatrix,Matrix.of_apply,← show ‖O i (EuclideanSpace.basisFun _ ℝ k)‖=1 from by simp]; exact PiLp.norm_apply_le (O i ((EuclideanSpace.basisFun G.ColorIndex ℝ) k)) j -- tune
lemma warp_subX {α β :Type} [Fintype α][Fintype β][DecidableEq α][DecidableEq β](O:ColorOrtho G α)(X:α≃β)(A B:Gaussian.Table (β × G.ColorIndex)): warp O X (A-B)=warp O X A-warp O X B:=by
 unfold warp dressed; rw [Matrix.submatrix_sub]; simp only [Pi.sub_apply,Matrix.mul_sub,Matrix.sub_mul]
lemma graftX(l:ℕ)(h:Flow (PhysicalNext.OrderedAffine2B.SymRows.room x A F) (rotating (constantGauge z⁻¹ S.ratio)) (outRotation z⁻¹) k k T (Lattice.gauge z V) V q d (gaugeY z x A F Y) Y)(hp:S.patch.Branches S.kernel G)(hT:T.up.Bounds T.high v D E) :
 graft T x V k A F q d Y l=Orthogonal.warp (onBond (rotating (constantGauge z⁻¹ S.ratio))) (Equiv.refl _) (graft T x (Lattice.gauge z V) k A F q d (gaugeY z x A F Y) l):=by
 unfold graft; rw [h.orbitM hT hp,h.headT,h.test.kernel.same,warp_subX,warp_sym]; rfl
lemma pricedM {α:Type} [Fintype α][DecidableEq α](O:ColorOrtho G α){f:Directions G c→Gaussian.Table (α × G.ColorIndex)}{i j:α}(h:∀ a b:G.ColorIndex,Allows n (fun y=>f y (i,a) (j,b)) 0 M)(u v:G.ColorIndex): Allows n (fun y=>warp O (Equiv.refl _) (f y) (i,u) (j,v)) 0 (Fintype.card G.ColorIndex*(Fintype.card G.ColorIndex*M)):=by
 have hl(i i' s w: G.ColorIndex):=h i i'; have hm := (h u v).nonneg; let P := asMatrix O; let U:=Fintype.card G.ColorIndex
 let H(a b:G.ColorIndex)(y:Directions G c):=P i u a*f y (i,a) (j,b); have ha(a b):Allows n (H a b) 0 M:= ((h a b).smul _).mono (mul_le_of_le_one_left hm (asMatrix_bound ..))
 have hc(b:G.ColorIndex) :Allows n (fun y=> ∑ a,H a b y) 0 (U*M):=by simpa only [Finset.sum_const, Finset.card_univ,nsmul_eq_mul] using allows_sum (s:=Finset.univ) (f:=fun a=>H a b) (fun i _=>ha i b)
 let G'(b:G.ColorIndex)(y:Directions G c):= P j v b*(∑ a,H a b y); have he(b):Allows n (G' b) 0 (U*M):=((hc b).smul _).mono (mul_le_of_le_one_left (mul_nonneg (Nat.cast_nonneg _) hm) (asMatrix_bound ..))
 have hv := allows_sum (s:=Finset.univ) (f:=G') (fun a _=>he a); simp only [Finset.sum_const, Finset.card_univ,nsmul_eq_mul] at hv
 apply hv.germ; filter_upwards with y; rw [warp,dressed_apply]; exact Finset.sum_congr rfl fun k _=> mul_comm ..
lemma cost_alt {ι α:Type}[Fintype ι][DecidableEq ι][NormedAddCommGroup α][NormedSpace ℝ α]{x:α}{f g:α→Matrix ι ι ℝ}(h:Allows n (fun y=>paintO (f y)-paintO (g y)) x D)(i j:ι): Allows n (fun y=> f y i j-g y i j) x D:=by
 let L:= ContinuousLinearMap.apply ℝ (Fish ι) (Pi.single (M:=fun _ : ι=>ℝ) j 1)
 have he : ‖(Pi.single (M:=fun _ : ι=>ℝ) j 1)‖≤1:=(pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i=>by by_cases h:i=j <;> simp [h]
 have hp : ‖(L:(Fish ι→L[ℝ] Fish ι)→L[ℝ] Fish ι)‖≤1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun i=>by rw [one_mul]; exact (i.le_opNorm _).trans (mul_le_of_le_one_right (norm_nonneg _) he)
 apply (readZ ((h.linear L hp).mono (one_mul D).le) i).germ; filter_upwards with y; unfold L; simp only [ContinuousLinearMap.apply_apply,_root_.sub_apply,Newt.paintO_p,Matrix.mulVec_single_one]; rfl
lemma b_sym{α:Type}[Fintype α](A:Gaussian.Table α)(i j:α): Relative.symPart A i j=(A i j + A j i)/2:=by simp [Relative.symPart]; ring
lemma gramS(h:Tube G S)(F:Forest S.ratio): (Rows.gram h x V k (shots S x) A F).IsSymm:=by unfold Rows.gram Matrix.IsSymm; rw [Matrix.transpose_mul,Matrix.transpose_transpose]
private lemma combo {α:Type} [NormedAddCommGroup α] [NormedSpace ℝ α] {f t:α→ℝ} {x:α} (h:Allows n f x D)(p:Allows n t x D):Allows n (fun x=>(f x+t x)/2) x D:=by
 apply (((h.add p).smul (1/2)).mono (le_of_eq (by rw [abs_of_nonneg (by norm_num)]; ring))).germ; filter_upwards with x; change (1/2:ℝ)*_= _; ring
lemma costPew {i j:Active A x F}(a b: G.ColorIndex)(hr:Ready T x)(ht:T.up.Bounds T.high v D E)(l:ℕ)(hL:l≤18)(hx:Fleet S x V F A Y z k R (S.ratio.parent i.val.val.1) s)(hN:Allows n R 0 (1/2))(hp:meeting S x i.val.val j.val.val)(hi: green x S A i.val.val)(hj:green x S A j.val.val) (hC:
 let H:=bareStores S; let PP:= pageX (G:=G) F x; let P(y:Mast G c):=facadeX G (s•y)
 Allows n (fun y=> paintO ((headed T x (P y) k H F (orbitP T x (P y) k H F q d 1 l)).submatrix PP PP)-gabs T x k F (P y)) (R 0) M):
 Allows n (fun y=> driftN T x (Vmove x V y) k A F q d Y l (i,a) (j,b)) 0 (Fintype.card G.ColorIndex*(Fintype.card G.ColorIndex*Jet.composeCost n M (1/2))):=by
 let H:=bareStores S; let PP:=pageX (G:=G) F x; let P(y:Directions G c):=facadeX G (s•R y); let U(y:Directions G c):=gauge z (Vmove x V y); let Z:= gaugeY z x A F Y
 let i':Active H x F:= ⟨i.val,notChilled S F x _⟩; let j':Active H x F:=⟨j.val,notChilled S F x _⟩
 let X(y:Directions G c):=graft T x (U y) k A F q d Z l
 have hX (y:Directions G c): driftN T x (Vmove x V y) k A F q d Y l (i,a) (j,b)= graft T x (Vmove x V y) k A F q d Y l (i,a) (j,b):=by unfold driftN graft; rw [Matrix.sub_apply,Matrix.sub_apply,hessN,Matrix.of_apply,if_pos ⟨hi,hj⟩]
 suffices hh:∀ u w:G.ColorIndex,Allows n (fun y=>X y (i,u) (j,w)) 0 (Jet.composeCost n M (1/2)) by
    apply (pricedM (onBond (A:=A) (F:=F) (x:=x) (rotating (constantGauge z⁻¹ S.ratio))) hh a b).germ; exact Eventually.of_forall fun y=> ((hX y).trans (congr_fun (congr_fun (graftX (z:=z) l (V:=Vmove x V y) (poursF hr.rules ht) hr.rules ht) _) _)).symm
 intro u w; let r₁:=R (0:Directions G c); dsimp only at hC; have hv:=hC.comp hN; let hf(y):=(orbitP T x (P y) k H F q d 1 l)
 let K:=fun (y:Directions G c)(i j:Rows.In x H F (G:=G)) => headed T x (P y) k H F (hf y) i j-Rows.gram T x (P y) k (shots S x) H F i j
 have hK (i j: Rows.In x H F (G:=G)): Allows n (fun y=>K y i j) 0 (Jet.composeCost n M (1/2)):=by
    obtain ⟨i,rfl⟩:= PP.surjective i; obtain ⟨j,rfl⟩:=PP.surjective j; exact cost_alt (f:=fun y=>(headed T x (P y) k H F (hf y)).submatrix PP PP) hv i j -- tune
 apply (combo (hK (i',u) (j',w)) (hK (j',w) (i',u))).germ; filter_upwards [hx] with y hy
 let I:Rows.In x A F (G:=G):=(i,u); let J:Rows.In x A F (G:=G):=(j,w); have hi:= ball_member (show J∈panels A F I from hp)
 change Scan S x (front A F I) .. at hy
 let L:=radiusB x; let f:=orbitP T x (U y) k A F q d Z l
 have hl:(l+1)*radiusB x≤19*L:= by unfold L; gcongr; omega
 have hh {p q: Rows.In x A F (G:=G)} {p' q':Rows.In x H F (G:=G)} (h: Scan S x (front A F p) (21*L) A H F F k k (U y) (P y) Z 1)(hp:PatchReads.lift p=PatchReads.lift p')(hq:PatchReads.lift q=PatchReads.lift q'): headed T x (U y) k A F f p q=headed T x (P y) k H F (hf y) p' q':=by
    apply head_read hr (h.lower (by unfold L; omega)) _ hp hq; intro i i' hi hv; apply orbitX hr _ _ _ (h.shrink ?_) hv; unfold L at *; omega
 unfold K X graft; rw [Matrix.sub_apply,b_sym, show _=_ from hh (p:=I) (q:=J) (hy.lower (by unfold L; omega)) (p':=(i',u)) (q':=(j',w)) rfl rfl, show _=_ from hh (p:=J) (q:=I) (hy.shrink (by unfold L; omega)) (p':=(j',w)) (q':=(i',u)) rfl rfl]
 rw [gram_eq hr.rules (i:=I) (j:=J) (i':=(i',u)) (j':=(j',w)) (hy.lower (by have H:=hr.inputs; omega)) rfl rfl,(gramS (k:=k) T F).apply]; -- tune ordering
 ring
end YM.CF.Char
