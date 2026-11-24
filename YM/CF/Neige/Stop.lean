import YM.CF.Neige.Flat
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
open SectorNext.Vacuum.FlatTree Next.SectorChange.Rows
variable {E X D:ℝ}
section arc
variable (G: Gauge)(T:Tube G S)(h: T.up.Bounds T.high E X D)(hp:S.patch.Branches S.kernel G)(k k':S.Choices)(x:ℝ)
include hp
lemma rama : bump T x 1 k=bump T x 1 k':=by
 funext v i; obtain ⟨s,p|p⟩:=i; · exact show faceKick T x _ _ _ _=faceKick T x _ _ _ _ from rfl
 change -(_ • blockJet _ _ _ _ v)= -(_ • blockJet _ _ _ _ v); rw [ice_b (k:=k) (k':=k') hp]; -- tune
include h
lemma jour(g:Site f→G.Color)(ht:∀ i,g (S.ratio.embed i)=0): bump T x 1 k (SectorNext.Vacuum.FlatTree.climb g)=0:=by
 let Z(i:G.ColorIndex): Directions G f:= SectorNext.Vacuum.FlatTree.climb (fun a=> g a i • epsI G i)
 have hv: SectorNext.Vacuum.FlatTree.climb g= ∑ i:G.ColorIndex,Z i:=by
    funext i; simp only [Finset.sum_apply,Z, SectorNext.Vacuum.FlatTree.climb, Finset.sum_sub_distrib]; exact congr_arg₂ _ ((epsI G).sum_repr (g i.1)).symm ((epsI G).sum_repr (g (i.1+step i.2))).symm
 let C':Directions G f →ₗ[ℝ] LogArray G (Slots S):= { toFun:=bump T x 1 k, map_add':=bump_add _ _ _ _ h,map_smul':= fun w a=>bump_smul _ _ _ _ h a w }
 have hz(i): C' (Z i)=0:=lensX hp k (epsI G i) (fun a=>g a i) (fun i=>by rw [ht]; rfl)
 rw [hv]; change C' _=0; rw [map_sum]; simp_rw [hz,sum_const_zero]
end arc
lemma trays_b (a:Key F G→ℝ): trays S x F a = blank F (Push.Uniform.tint G _ a):=by
 funext i; by_cases he:i∈F.trunks
 · unfold blank trays fresh; rw [dif_neg (not_not.mpr he),dif_pos he]
 let j:Active (bareStores S) x F:= ⟨⟨i,he⟩,notChilled S F x _⟩; unfold blank; rw [dif_neg he,show trays S x F a i=tape (leaveX F x a) j from Gap.freshly_read _ _ _ _ j]; ext k
 change a ((pageX F x).symm (j,k))=_; rw [show (pageX (G:=G) F x).symm (j,k)=(j.val,k) from (pageX (G:=G) F x).symm_apply_apply (j.val,k)]; rfl
section integer
variable (F F':Forest S.ratio)
private lemma ranger {P Q:Type} [AddCommGroup P][AddCommGroup Q](A:P→+Q) (f : Links (Per f) P)(g:Links (Per _ ) Q)(x)(w:Walk)(h:∀ i,g i=A (f i)): A (cab f x w)=cab g x w:=by
 induction w generalizing x with
 | nil=>exact map_zero _
 | cons i w ih=>rw [cab,map_add,cab,ih]; unfold beam; split <;> simp_all
private lemma mails {P Q:Type}[AddCommGroup P][AddCommGroup Q](A:P→+Q)(U:F.Free→P)(i:F'.Free): (express F F' Q (fun i=>A (U i))) i=A (express F F' P U i):=by
 let W:=blank F U; let W':=blank F (A∘U); have hh(i): W' i=A (W i):=by unfold W' W blank; split; exact (map_zero A).symm; rfl
 change fleet F' W' i=A (fleet F' W i); unfold fleet SectorNext.Vacuum.FlatTree.erase
 simp only [Pi.add_apply, SectorNext.Vacuum.FlatTree.climb,leafWard,map_add,map_sub,map_neg,ranger _ _ _ _ _ hh, hh]
abbrev SpinK (R:Type)[CommRing R](G:Gauge):=roll F F' G.ColorIndex R
def testD(F:Forest S.ratio)(T:Tube G S)(x:ℝ)(k:S.Choices): Matrix (Receipt G S) (Key F G) ℝ:= (move T x 1 k (shots S x) (bareStores S) F).submatrix id (pageX F x)
lemma around(a:Key F G→ℝ): testD F T x k *ᵥ a=move T x 1 k (shots S x) (bareStores S) F *ᵥ leaveX F x a:=by
 ext i; let p:= pageX F x (G:=G); let L:= move T x 1 k (shots S x) (bareStores S) F
 change ∑ j,L i (p j)*a j=∑ j,L i j * a (p.symm j); rw [← p.sum_comp]; simp
lemma world(a:Key F G→ℝ): trays S x F' (SpinK F F' ℝ G *ᵥ a)=erase F' (trays S x F a):=by
 unfold SpinK roll; rw [LinearMap.toMatrix'_mulVec, trays_b, trays_b]; let v:=Push.Uniform.tint G _ a
 rw [show Push.Uniform.tint G _ ((fluid F F' G.ColorIndex ℝ).toLinearMap a) = fleet F' (blank F v) from ?_,SectorNext.Vacuum.FlatTree.clear]
 ext i j
 exact mails F F' (PiLp.proj (𝕜:=ℝ) 2 (fun _ : G.ColorIndex=>ℝ) j|>.toLinearMap.toAddMonoidHom) v i
lemma spun(hp:S.patch.Branches S.kernel G)(ht:T.up.Bounds T.high E X D): testD F' T x k'*SpinK F F' ℝ G=testD F T x k:=by
 apply Matrix.ext_iff_mulVec.mpr; intro v; rw [←mulVec_mulVec,around,around,moved _ _ _ _ _ _ _ ht,moved _ _ _ _ _ _ _ ht, selected_all T _ _ _ _ _ _ hp, selected_all T _ _ _ _ _ _ hp]; congrm tape.symm (_ • ?_); rw [rama G T hp k' k]; change bump T x 1 k (trays S x F' _)=bump T x 1 k (trays S x F _); rw [world,SectorNext.Vacuum.FlatTree.erase,bump_add _ _ _ _ ht,jour G T ht hp k x _ (fun i=>root_clear ..),add_zero] -- tune
lemma roll_real(G:Gauge): SpinK F F' ℝ G=(SpinK F F' ℤ G).map (Int.castRingHom ℝ):=by
 ext i j; let A:=Int.castRingHom ℝ; unfold SpinK roll; rw [Matrix.map_apply]; simp_rw [LinearMap.toMatrix'_apply]; let a:Page G.ColorIndex F→ℤ:= Pi.single j 1
 rw [show (Pi.single j (1:ℝ) : Key F G→ ℝ)=fun i=>A (a i) from funext fun i=>by by_cases h:i=j <;> simp [h,A,a]]; exact mails F F' A.toAddMonoidHom (fun k=>a (k,i.2)) i.1 -- tune
lemma gramK : (testD F T x k).transpose * testD F T x k=(baseX T x (bareStores S) F k 1).submatrix (pageX F x) (pageX F x):=by ext i j; simp only [testD, Matrix.transpose_apply, Matrix.mul_apply,Matrix.submatrix_apply]; rfl
lemma mountain (G:Gauge)(T:Tube G S)(x:ℝ)(k k':S.Choices)(hp:S.patch.Branches S.kernel G)(ht:T.up.Bounds T.high E X D):
 Matrix.det (baseX T x (bareStores S) F k 1)=Matrix.det (baseX T x (bareStores S) F' k' 1):=by
 rw [← det_submatrix_equiv_self (pageX F x),← det_submatrix_equiv_self (pageX F' x),← gramK F, ← gramK F',← spun (k':=k') F F' hp ht]
 let p:Key F' G≃ Key F G:= Fintype.equivOfCardEq (pages F' F G.ColorIndex); let A:=SpinK F F' ℝ G; let L:= SpinK F F' ℤ G; let U:= L.submatrix (_root_.id) p
 let E:=testD F' T x k'; rw [← det_submatrix_equiv_self p]; -- maybe rewrites wrong side
 change ((Matrix.submatrix ((E*A).transpose*(E*A)) p p).det) =_
 let Q:=A.submatrix id p; let I:= Equiv.refl (Key F' G)
 have he:((E*A).transpose*(E*A)).submatrix p p= Q.transpose*(E.transpose*E)*Q:=by
    rw [transpose_mul,← Matrix.mul_assoc, Matrix.mul_assoc A.transpose E.transpose E]
    change _= (A.submatrix I p).transpose*(E.transpose*E)*(A.submatrix I p)
    rw [show (A.submatrix I p).transpose=A.transpose.submatrix p I from rfl]; nth_rw 2 [show E.transpose*E=(E.transpose*E).submatrix I I from rfl]
    rw [submatrix_mul_equiv, submatrix_mul_equiv]
 have hy:L*SpinK F' F ℤ G=1:=by
    apply Matrix.ext_iff_mulVec.mpr; intro i; rw [← mulVec_mulVec]; unfold L SpinK roll; simp_rw [LinearMap.toMatrix'_mulVec]; rw [one_mulVec]; exact (fluid F F' G.ColorIndex ℤ).apply_symm_apply i -- defeq inverse?
 let v:= (SpinK F' F ℤ G).submatrix p I
 have hu:U*v=1:=by
    change L.submatrix I p*(SpinK F' F ℤ G).submatrix p I=_
    rw [submatrix_mul_equiv,hy]; rfl
 let P:= Int.castRingHom ℝ
 have hZ: Q.det=P U.det:=by
    rw [P.map_det]; rw [show Q=U.map P from ?_]; rfl
    unfold Q U A L; rw [roll_real]; rfl
 have hm : |Q.det|=1:=by rw [hZ]; change |(U.det:ℝ)|=1; exact_mod_cast (Int.isUnit_iff_abs_eq.mp (Matrix.isUnit_det_of_right_inverse hu)) -- tune wrong
 rw [he,det_mul,det_mul,det_transpose, show Q.det*(E.transpose*E).det*Q.det=(E.transpose*E).det*Q.det^2 by ring,←sq_abs,hm,one_pow,mul_one] -- E def
end integer
end YM.CF.Neige
