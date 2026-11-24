import YM.SU5.FiniteGaugeData.Pannier.Filigree
/-! # Lift mixed Haars to the all-period corpus with continuity. -/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Pannier.Chancel
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye Cliplet RG Brace
open Window (mem_Tset family)
open Py.Rate.Pannier
open Lifted
open Reed (Fine)
open Afterglow
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {K:Calibration}{k:ℕ}{b:Fin k→ Cover}{S:Finset Cover}{s:SU.Slot}{W:Window.Family}{L:List (Fin k)}{v:Buffered.Family K}
namespace Filigree
open Tapestry Satin Tapestry.Roomy
-- finite-period bridge. support is fixed and S suffices (all born)
variable {n m:Side}
private lemma touchCont (n: Side) : Continuous (graft S n) := by
 apply continuous_pi; intro t; unfold Satin.graft; split; exact continuous_apply _; exact continuous_const
lemma shaft (w:Roomy S (K.c m))(f:Mark (K.c m))(t:AtSupport false (region S (K.c m)) f)(u:Continuous f) (g:∀ x y:Fields _, x.1=y.1 → f x=f y) (x:∀ i, nodeC (b i)∈S)
    (p:∀ v,f v∈ Hap W ((wrap (K.c m)) ∘ b) (region S (K.c m))) :
    ∃ F:Buffered.Family K,F∈ Filigree K W b S ∧ F m=f:=by
 classical
 let n:=K.c m; let H:= Hap W (wrap n ∘ b) (region S n); let B:= Module.finBasis ℂ H
 let I:=Fin (Module.finrank ℂ H); let A (i:Pane n):↥H:=⟨f (i,i),p _⟩
 choose Y h v using (fun i:I=>hap_one K m (C:=(B i).val) (W:=W) (b:=b) (S:=S) (B i).property x)
 let X (i:I)(z:LinksC):= B.coord i (A (graft S n z)); let U(i:I):PairsC→ℂ:=X i ∘ Prod.fst
 have hv(i:I):Coeff false S (U i):=by
    refine Coeff.fromC false S ((B.coord i).continuous_of_finiteDimensional.comp (((u.comp (continuous_id.prodMk continuous_id)).subtype_mk (fun _=> p _)).comp ?_)) (fun a s p=>?_)
    · exact touchCont _
    exact congrArg (B.coord i) (Subtype.ext (t.dep _ _ (tack S n w a s p) (tack S n w a s p)))
 let T:=∑ i,scalar K (U i)*Y i; refine ⟨T,Submodule.sum_mem _ fun i _=>Submodule.subset_span (show _∈_ from ⟨_,_,h i,hv i,rfl⟩),?_⟩
 funext y; let P:=A y.1; have he: A (graft S n (onC n y.1))=P:= Subtype.ext (t.dep _ _ (untack S n (seats w) y.1) (untack S n (seats w) y.1)); have hg(i:I): (scalar K (U i)*Y i) m y=(B.coord i P) • (B i).val:=by rw [Pi.mul_apply,Pi.mul_apply, v]; change (X i _ • (1: FC _))* (B i).val= _; unfold X; rw [he, Algebra.smul_mul_assoc,one_mul]
 unfold T; simp_rw [Finset.sum_apply,hg]; have ht:f y=P.val:=g y _ rfl
 rw [ht]; have hp:P=∑ i:I,(B.coord i P) • B i:=(B.sum_repr P).symm
 conv_rhs=>rw [hp];
 rw [Submodule.coe_sum]
 try rfl
end Filigree
end YM.CF.Pannier.Chancel
#print axioms YM.CF.Pannier.Chancel.Filigree.shaft
