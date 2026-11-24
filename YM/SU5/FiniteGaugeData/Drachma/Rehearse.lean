import YM.SU5.FiniteGaugeData.Drachma.Gamut
import YM.CF.Neige.Stop
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Bed
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 16000
set_option linter.flexible false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Drachma
open Function Finset Filter Matrix Lattice Wilson RG Precision Exterior Tree Laurent Bloch
open Pressure Pressure.Tube Stores AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
 AnalyticBridge.NonflatCovarianceLocality.Matching PatchReads
open CF.Newt CF.Neige CF.Char Next.Fluctuations Next.SectorChange Next.SectorChange.Wisps Next.SectorChange.Schur PhysicalNext.JointLoad Work.F03
open SectorNext.Vacuum.FlatTree Next.SectorChange.Rows Push.SectorMeasure
open scoped Topology ContDiff BigOperators Matrix Classical InnerProductSpace Kronecker Matrix.Norms.Frobenius
variable {c f:Side}{G:Gauge} {S:StepData c f} {T:Tube G S}{p:Clip} {a A σ C Λ x:ℝ} {P Q:Bed}
local notation "λ₀" => S.kernel.penalty
variable (F : Forest S.ratio)
def vitae(S:StepData c f)(P:Bed)(x y:Bid.Dir G f):=Bid.gaugeFiscal P x y + S.kernel.penalty * ∑ i:Bond c, inner ℝ (Bid.bills S x (pole i)) (Bid.bills S y (pole i))
abbrev air(Q:Slots S→G.Color)(R:Slots S→G.Color):=∑ i,inner ℝ (Q i) (R i)
lemma virtue(h:Floor P T.high f a A)(ht:T.up.Bounds T.high σ C Λ)(he:Attached P T.up)(x y:Bid.Dir G f): ∑ i:Twin f,inner ℝ (xLin T.high T.up x i) (xLin T.high T.up y i)=Bid.gaugeFiscal P x y:=by
 rw [Fintype.sum_prod_type,metric_pair P ht he _ _ h]; refine sum_congr rfl fun i _=>?_; rw [Fintype.sum_bool]; simp only [xLin,Bool.false_eq_true,↓reduceIte]; rw [real_inner_smul_left,real_inner_smul_right,← mul_assoc,Real.mul_self_sqrt T.high.quadratic_pos.le, add_comm]
lemma odore(x y:Bid.Dir G f)(S:StepData c f)(i:Bond c): inner ℝ (zLin S x 0 i) (zLin S y 0 i) = S.kernel.penalty *inner ℝ (Bid.bills S x (pole i)) (Bid.bills S y (pole i)) := by
 simp only [zLin,Bid.bills, Pi.zero_apply, zero_sub, real_inner_smul_left,real_inner_smul_right, inner_neg_left,inner_neg_right,mul_neg,neg_neg]; rw [←mul_assoc,Real.mul_self_sqrt S.kernel.penalty_pos.le]
lemma collinear(x y:Bid.Dir G f)(s:Signed)(i: Bond f):inner ℝ (Bid.pulled x s (pole i)) (Bid.pulled y s (pole i))=inner ℝ (x (pole (sendEdge s 0 i))) (y (pole (sendEdge s 0 i))):=by
 simp only [Bid.pulled,sendEdge,pole,show axisEquiv.symm (coord i.2)=i.2 from axisEquiv.symm_apply_apply _]; split <;> simp [*] -- tune
lemma vitae_spin(P:Bed)(x y:Bid.Dir G f)(s:Signed)(k:S.Choices)(he:S.patch.Branches S.kernel G)(h:Bid.Sworn P f G):vitae S P (Bid.pulled x s) (Bid.pulled y s)=vitae S P x y:=by
 simp_rw [vitae,h s x y,Flat.bills_signed S s k _ _ he,collinear]
 let U : Bond c ≃ Bond c:= Equiv.ofBijective _ (Finite.injective_iff_bijective.mp (sendEdge_injective s (0:Site c)))
 have he:= U.sum_comp (fun i: Bond c=> inner ℝ (Bid.bills S x (pole i)) (Bid.bills S y (pole i)))
 exact congr_arg (fun t:ℝ=> Bid.gaugeFiscal P x y + λ₀ * t) he
lemma aft (S:StepData c f)(P:Bed)(x y:Bid.Dir G f): vitae S P x y=∑ i:G.ColorIndex,dotProduct (parts _ _ x i) (subB (S:=S) (P:=P)*ᵥ (parts _ _ y i)) :=by
 simp_rw [subB,plus_bill,smid,prize_bill,sum_add_distrib,←mul_sum,vitae]; congr 2
 simp_rw [inner_color]; rw [sum_comm]; apply sum_congr rfl; intro i _; exact (portfolio c).sum_comp fun j=> (probe S*ᵥ parts _ _ x i) j*(probe S *ᵥ parts _ _ y i) j

lemma conifer (k:S.Choices)(h:Floor P T.high f a A)(ht:T.up.Bounds T.high σ C Λ)(he:Attached P T.up)(hp:S.patch.Branches S.kernel G)(hs:Bid.Sworn P f G)(x y:Directions G f): air (slip • Flat.ideal T x) (slip • Flat.ideal T y)=vitae S P (Flat.labels x) (Flat.labels y):=by
 let X:=vitae S P (Flat.labels x) (Flat.labels y)
 unfold air; simp_rw [Pi.smul_apply,real_inner_smul_left,real_inner_smul_right, ←mul_sum]; rw [Fintype.sum_prod_type]
 have hl(s:Signed): ∑ i:(Twin f ⊕ Bond c), inner ℝ (Flat.ideal T x (s,i)) (Flat.ideal T y (s,i))= X:=by
    rw [Fintype.sum_sum_type]; simp only [Flat.ideal,Sum.elim_inl,Sum.elim_inr]
    simp_rw [virtue h ht he,odore,←mul_sum]; exact vitae_spin P _ _ _ k hp hs
 rw [show (∑ s:Signed,_)=(∑ _ : Signed,X) from sum_congr rfl fun s _=> hl s]; rw [sum_const,card_univ,nsmul_eq_mul]; have ht:0<(Fintype.card Signed:ℝ):=Nat.cast_pos.mpr Fintype.card_pos
 change slip * (slip * ((Fintype.card Signed:ℝ)*X))=X; unfold slip; rw [←mul_assoc,← mul_assoc, show (Real.sqrt (Fintype.card Signed:ℝ))⁻¹ * (Real.sqrt (Fintype.card Signed:ℝ))⁻¹*_= 1 from ?_,one_mul]
 field_simp; nlinarith only [Real.sq_sqrt ht.le] -- tune

-- restrict planos. counting basis along colors
abbrev music(G:Gauge)(F:Forest S.ratio)(P:Bed):= jazz F P ⊗ₖ (1:sp G.ColorIndex)
abbrev bank(F:Forest S.ratio)(p:Key F G→ℝ)(s:G.ColorIndex):coin F.Free:=fun i=>p (i,s)
lemma dot_crate (p r:Key F G→ℝ): dotProduct p (music G F P *ᵥ r) = ∑ i:G.ColorIndex,dotProduct (bank F p i) (jazz F P*ᵥ bank F r i):=by
 have he(i:Key F G): (music G F P *ᵥ r) i=(jazz F P*ᵥ bank F r i.2) i.1:=by
    rw [mulVec,dotProduct,Fintype.sum_prod_type]; refine sum_congr rfl fun j _=>?_; simp [music,one_apply] -- tune
 simp_rw [dotProduct, he,Fintype.sum_prod_type]; rw [sum_comm]
lemma hueTrunk(X:Key F G→ℝ)(s:G.ColorIndex)(r:ℝ): parts G 1 (Flat.labels (trays S r F X)) s∘ bail F=swapper 0 (bank F X s):=by
 rw [trays_b]; funext i; cases i with
 | inl j=> change blank F (Push.Uniform.tint G F.Free X) ((portfolio f).symm (portfolio f j.val)) s=0; rw [Equiv.symm_apply_apply]; unfold blank; rw [dif_pos j.2]; rfl
 | inr j=> change blank F (Push.Uniform.tint G F.Free X) ((portfolio f).symm (portfolio f j.val)) s=X (j,s); rw [Equiv.symm_apply_apply]; unfold blank; rw [dif_neg j.2]; rfl
lemma congr_dot{X Y:Type}[Fintype X][Fintype Y](e:X≃Y)(T:sp Y)(x y:coin Y):dotProduct x (T*ᵥ y)=dotProduct (x∘e) ((T.submatrix e e)*ᵥ (y∘e)):=by
 rw [submatrix_mulVec_equiv]; simp only [Function.comp_assoc,Equiv.self_comp_symm, Function.comp_id] -- tune
 exact (e.sum_comp (fun i=> x i*(T*ᵥ y) i)).symm
lemma perf_dot(T:sp (LT f))(x y:coin F.Free): dotProduct (swapper (0:coin (stem F)) x) ((T.submatrix (bail F) (bail F))*ᵥ swapper (0:coin (stem F)) y)=dotProduct x ((T.submatrix (ηT F) (ηT F))*ᵥ y):=by
 rw [bills,born_l,born_r,zero_dotProduct,zero_add]; congr 1; ext i; change ∑ j:stem F⊕F.Free,T (ηT F i) (bail F j)*swapper (0:coin (stem F)) y j=_; rw [Fintype.sum_sum_type]; simp [swapper]; rfl
lemma vitae_value(X Y:Key F G→ℝ)(r:ℝ): vitae S P (Flat.labels (trays S r F X)) (Flat.labels (trays S r F Y))=dotProduct X (music G F P*ᵥ Y):=by
 rw [dot_crate,aft]; apply sum_congr rfl; intro i _; rw [congr_dot (bail F),hueTrunk,hueTrunk]; exact perf_dot ..
lemma detaine(G:Gauge)(P:Bed): (music G F P).det=(jazz F P).det^Fintype.card G.ColorIndex:=by rw [music,det_kronecker]; simp
-- compared Gram using bareStores
lemma fair (k:S.Choices)(p r:Key F G→ℝ)(h:S.patch.Branches S.kernel G)(v:T.up.Bounds T.high σ C Λ): dotProduct p (((baseX T x (bareStores S) F k 1).submatrix (pageX F x) (pageX F x))*ᵥ r)=air (slip•bump T x 1 k (trays S x F p)) (slip •bump T x 1 k (trays S x F r)):=by
 rw [←gramK F]; change dotProduct p (prizes _*ᵥ r)=_
 have he(y:Key F G→ℝ): testD F T x k*ᵥ y=tape.symm (slip• bump T x 1 k (trays S x F y)):=by rw [around,moved _ _ _ _ _ _ _ v, selected_all T _ _ _ _ _ _ h] -- tune
 rw [prize_bill,he,he]; simp_rw [air,inner_color,dotProduct,Fintype.sum_prod_type]; rfl
end YM.SU5.FiniteGaugeData.Drachma
