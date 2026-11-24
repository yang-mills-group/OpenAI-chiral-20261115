import YM.CF.Char.Core
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
open Next.SectorChange.Rows
abbrev epsI (G: Gauge):=EuclideanSpace.basisFun G.ColorIndex ℝ
def drive(T:Tube G S)(x:ℝ)(V:Config G c)(k:S.Choices)(a:Directions G f)(i:Bond f) (u:G.Color):ℝ:= rack T x V k (a+Pi.single i u)-rack T x V k a
def pushed(T:Tube G S)(x:ℝ)(V:Config G c)(k:S.Choices)(A:Stores S)(F:Forest S.ratio)(a: Prices G (Active A x F))(i:Rows.In x A F (G:=G)):ℝ:= fderiv ℝ (drive T x V k (Rows.fresh x (shots S x) A F (tape a)) i.1.val.val) 0 (epsI G i.2)
def curveX(T:Tube G S)(x:ℝ)(V:Config G c)(k:S.Choices)(a:Directions G f)(i j:Bond f)(u:G.Color× G.Color):ℝ:= rack T x V k (a+(Pi.single i u.1 + Pi.single j u.2))-rack T x V k a
def headed(T:Tube G S)(x:ℝ)(V:Config G c)(k:S.Choices)(A:Stores S)(F:Forest S.ratio)(a: Prices G (Active A x F)):Gaussian.Table (In x A F (G:=G)):= of fun i j=> if j∈panels A F i then
 iteratedFDeriv ℝ 2 (curveX T x V k (Rows.fresh x (shots S x) A F (tape a)) i.1.val.val j.1.val.val) 0 ![(epsI G i.2,0),(0,epsI G j.2)] else 0
abbrev columnX (T:Tube G S)(x:ℝ)(V:Config G c)(k:S.Choices)(A:Stores S)(F:Forest S.ratio):= per (panels A F) (Rows.gram T x V k (shots S x) A F)
def swingP (T:Tube G S)(x:ℝ)(V:Config G c)(k:S.Choices)(A:Stores S)(F:Forest S.ratio)(a: Prices G (Active A x F)):= a- (columnX T x V k A F).transpose *ᵥ pushed T x V k A F a
def orbitP (T:Tube G S)(x:ℝ)(V: Config G c)(k:S.Choices)(A:Stores S)(F:Forest S.ratio)(q: Chi)(d:ℝ)(Y:LinkArray G (Frozen A x F)):ℕ→ Prices G (Active A x F)| 0=> Offset.mean T x k A F q d Y V | j+1=>swingP T x V k A F (orbitP T x V k A F q d Y j)
variable {i j: Rows.In x A F (G:=G)}{i' j':Rows.In x A' F' (G:=G)} {a:Prices G (Active A x F)}{b:Prices G (Active A' x F')}
private lemma taxi (z:G.Color)(e:Bond f)(he:separation o (S.ratio.parent e.1)+2*span S.patch x≤r)(j: Bond f)(hj:r<separation o (S.ratio.parent j.1)+2*span S.patch x): (Pi.single (M:=fun _=>G.Color) e z) j=0:=Pi.single_eq_of_ne (fun (h:j=e)=> hj.not_ge (h.symm ▸he)) _
private lemma tandem(hr:Ready T x)(h:Scan S x o r A A' F F' k k' V W Y Y')(u v:Directions G f)(he:Next.SectorChange.echo S o r u v)(i j:Bond f)(hx:separation o (S.ratio.parent i.1)+2*span S.patch x≤r) (ht:separation o (S.ratio.parent j.1)+2*span S.patch x≤r): curveX T x V k u i j=curveX T x W k' v i j:= by
 ext1 z; apply echos hr.rules h u v he; intro j' hh; simp only [Pi.add_apply,taxi _ i hx j' hh,taxi _ j ht j' hh,add_zero]
lemma pairX(he:PatchReads.lift i=PatchReads.lift i'): i.1.val.val=i'.1.val.val∧i.2=i'.2:= ⟨congr_arg Prod.fst he,congr_arg Prod.snd he⟩
def mocks(o:Site c)(r:ℕ)(a: Prices G (Active A x F))(b:Prices G (Active A' x F')):Prop:=∀ i i',separation o (front A F i) ≤ r → PatchReads.lift i=PatchReads.lift i' → a i=b i'
lemma freshP(h:Scan S x o r A A' F F' k k' V W Y Y')(hp:mocks o r a b): Next.SectorChange.echo S o r (fresh x (shots S x) A F (tape a)) (fresh x (shots S x) A' F' (tape b)):=by
 intro i hi
 by_cases hx: i∈F.trunks
 · rw [fresh,fresh,dif_neg (not_not.mpr hx),dif_neg (not_not.mpr ((h.trunks i hi).mp hx))]
 let j:F.Free:= ⟨i,hx⟩; let j':F'.Free:=⟨i,mt (h.trunks i hi).mpr hx⟩; have he:=h.freeze_same (i:=j) (j:=j') hi (show j.val=j'.val from rfl)
 by_cases hv: chill A x F j
 · unfold fresh; rw [dif_pos j.property,dif_pos j'.property,dif_neg (not_not.mpr hv),dif_neg (not_not.mpr (he.mp hv))]
 let l:Active A x F:=⟨j,hv⟩; let l':Active A' x F':= ⟨j',mt he.mpr hv⟩; rw [Gap.freshly_read A F _ _ l,Gap.freshly_read A' F' _ _ l'] -- rw fails defeq
 ext m; exact hp (l,m) (l',m) hi rfl
lemma pushed_read(hr:Ready T x)(h:Scan S x o r A A' F F' k k' V W Y Y')(hp:mocks o r a b)(hi:separation o (front A F i)+2*span S.patch x≤r)(hh:PatchReads.lift i=PatchReads.lift i'): pushed T x V k A F a i=pushed T x W k' A' F' b i':=by
 let E:= i.1.val.val; let u:= fresh x (shots S x) A F (tape a); let v:= fresh x (shots S x) A' F' (tape b)
 obtain ⟨hv,he⟩:=pairX hh; have hu:drive T x V k u E=drive T x W k' v E:=by
    ext1 z; apply echos hr.rules h u v (freshP h hp); exact taxi z E hi
 unfold pushed; rw [← hv,← he,show i.1.val.val=E from rfl,hu]
lemma meetA(hi:PatchReads.lift i=PatchReads.lift i')(hh:PatchReads.lift j=PatchReads.lift j') : j∈panels A F i↔ j'∈panels A' F' i':=by change meeting _ _ _ _ ↔ meeting _ _ _ _; rw [(pairX hi).1,(pairX hh).1]
lemma head_read(hr:Ready T x)(h:Scan S x (front A F i) (radiusB x/5) A A' F F' k k' V W Y Y')(hp:mocks (front A F i) (radiusB x/5) a b)(hh:PatchReads.lift i=PatchReads.lift i')(he:PatchReads.lift j=PatchReads.lift j'): headed T x V k A F a i j=headed T x W k' A' F' b i' j':=by
 unfold headed; simp only [Matrix.of_apply]; by_cases hx:j∈panels A F i
 · rw [if_pos hx,if_pos ((meetA hh he).mp hx)]; have hy:=hr.inputs; rw [← (pairX hh).1,← (pairX he).1,tandem hr h _ _ (freshP h hp) _ _ (by change separation _ (front A F i)+_≤_; rw [separation_self]; omega) (by change separation _ (front A F j)+ _ ≤_; have hg:=ball_member hx; omega),(pairX hh).2,(pairX he).2]
 rw [if_neg hx,if_neg (mt ((meetA hh he).mpr) hx)]
lemma swing_read (hr:Ready T x)(h:Scan S x (front A F i) (radiusB x) A A' F F' k k' V W Y Y')(hp:mocks (front A F i) (radiusB x) a b)(hi: PatchReads.lift i=PatchReads.lift i'):
 swingP T x V k A F a i=swingP T x W k' A' F' b i':=by
 unfold swingP; rw [Pi.sub_apply, Pi.sub_apply,hp _ _ (by simp) hi]; congrm _- ?_
 unfold mulVec dotProduct; simp only [Matrix.transpose_apply]
 refine PatchReads.sum_eq (h.lower (r':=radiusB x/20) (by omega)) (fun j hj=>?_) (fun j hj=>?_) fun j j' hj he=>?_
 · rw [show columnX T x V k A F j i=0 from per_zero _ _ fun hv=>hj.not_ge (ball_member hv),zero_mul]
 · rw [show columnX T x W k' A' F' j i'=0 from per_zero _ _ fun hv=>hj.not_ge ((faces hi).symm ▸ ball_member hv),zero_mul]
 unfold columnX; rw [pushed_read hr h hp (i:=j) (by have he:=hr.inputs; omega) he,per_eq hr (h.lower (by omega)) hi he]
lemma orbitX(hr:Ready T x)(q:Chi)(d:ℝ)(l:ℕ)(h:Scan S x (front A F i) ((l+1)*radiusB x) A A' F F' k k' V W Y Y')(hp:PatchReads.lift i=PatchReads.lift i'):
 orbitP T x V k A F q d Y l i=orbitP T x W k' A' F' q d Y' l i':=by
 induction l generalizing i i' with
 | zero=> exact meetX hr (h.lower (by simp; omega)) hp q d -- tune
 | succ j ih=> rw [orbitP,orbitP]; rw [Nat.succ_mul] at h; exact swing_read hr (h.lower (by omega)) (fun i i' hi hh=> ih (h.shrink (by omega)) hh) hp
end YM.CF.Char
