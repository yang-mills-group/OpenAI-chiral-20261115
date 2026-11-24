import YM.SU5.Relativistic.TangentPrec
/-! # relative determinant. Pin invariance + sheared orthogonality. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Papyrus.GaugeFlux
open Function Finset Filter MeasureTheory Lattice Wilson RG Precision Exterior MinorPins Tree Matrix Bid Laurent
open scoped Matrix BigOperators Matrix.Norms.Frobenius InnerProductSpace ContDiff
variable {N C:Side}(S:StepData C N)(G:Gauge)
section jac
variable {J K L M:Type}[DecidableEq J][Fintype J][DecidableEq K][Fintype K][DecidableEq L][Fintype L][DecidableEq M][Fintype M]
private lemma fblocks (A: Matrix J J ℝ)(B:Matrix J K ℝ)(C:Matrix K J ℝ)(D:Matrix K K ℝ)(x y:J ⊕ K→ℝ) :
 dotProduct x (fromBlocks A B C D *ᵥ y)=dotProduct (x∘Sum.inl) (A *ᵥ (y∘Sum.inl)+ B*ᵥ (y∘Sum.inr))+dotProduct (x∘Sum.inr) (C *ᵥ (y∘Sum.inl)+ D*ᵥ (y∘Sum.inr)):=by
 unfold dotProduct; rw [Matrix.fromBlocks_mulVec,Fintype.sum_sum_type]; rfl
def duo (x:J↪L)(y:K↪M): J⊕ K ↪ L⊕ M:=x.sumMap y
lemma paste (x:J↪L)(y:K↪M)(v:J⊕K→ℝ) :
 (smear (duo x y)*ᵥ v)∘Sum.inl=smear x *ᵥ (v∘Sum.inl) ∧
 (smear (duo x y)*ᵥ v)∘Sum.inr=smear y *ᵥ (v∘Sum.inr):=by
 constructor
 · funext i; by_cases p:i∈Set.range x
   · obtain ⟨i,rfl⟩:=p; rw [smear_t]; exact smear_t (e:=duo x y) _ (.inl i)
   rw [smear_f _ _ p]; apply smear_f; rintro ⟨i,h⟩; cases i with| inl i=> exact p ⟨i,Sum.inl.inj h⟩ | inr i=> nomatch h
 funext i; by_cases p:i∈Set.range y
 · obtain ⟨i,rfl⟩:=p; rw [smear_t]; exact smear_t (e:=duo x y) _ (.inr i)
 rw [smear_f _ _ p]; apply smear_f; rintro ⟨i,h⟩; cases i with| inr i=> exact p ⟨i,Sum.inr.inj h⟩ | inl i=> nomatch h
lemma shade (e:J ↪ L) (A:Matrix L L ℝ)(x y): dotProduct x (A.submatrix e e *ᵥ y)=dotProduct (smear e*ᵥ x) (A *ᵥ(smear e *ᵥ y)):=by rw [←smeared, ←mulVec_mulVec,←mulVec_mulVec,dotProduct_mulVec,vecMul_transpose]
-- block elimination via mixed tests! choose C column for cross.
lemma plane_det (Q:Matrix (J⊕K) (J⊕K) ℝ)(A:Matrix J J ℝ)(B:Matrix K K ℝ)(p:(Q).transpose=Q)(t: Q.toBlocks₁₁=A)
  (T:∀ y:K→ℝ, ∃ x:J⊕K→ℝ, x∘Sum.inr=y∧ ∀ v,dotProduct v (Q*ᵥ x)=dotProduct (v∘ Sum.inr) (B*ᵥ y)) : Q.det=A.det*B.det:=by
 choose x h V using T; let R:= Matrix.of (fun (i:J)(j:K)=>x (Pi.single j 1) (Sum.inl i))
 let M:= fromBlocks (1:Matrix J J ℝ) R 0 (1:Matrix K K ℝ); let L:= M.transpose*Q*M
 have hm (i): M *ᵥ Pi.single (Sum.inl i) 1= Pi.single (.inl i) 1:=by funext j; rw [mulVec_single_one]; cases j <;>simp [M,Matrix.col,Matrix.one_apply,Pi.single_apply] -- name
 have hn (i): M *ᵥ Pi.single (Sum.inr i) 1=x (Pi.single i 1):= by
    funext j; rw [mulVec_single_one]; change M j _=_; cases j with
    | inl j=> rfl
    | inr j=> rw [show M (Sum.inr j) (Sum.inr i)=(1:Matrix K K ℝ) j i from rfl, show x _ (Sum.inr j)= _ from congrFun (h (Pi.single i 1)) j]; simp [Matrix.one_apply, Pi.single_apply]
 have hi(v:J⊕ K→ℝ): (M *ᵥ v) ∘ Sum.inr=v∘ Sum.inr:=by funext j; unfold M; simp only [Matrix.fromBlocks_mulVec,Matrix.zero_mulVec,one_mulVec,zero_add]; rfl
 have he (i j):L i j=dotProduct (M *ᵥ Pi.single i 1) (Q *ᵥ (M*ᵥ Pi.single j 1)) := by
    rw [mulVec_mulVec]; calc
     _ = dotProduct (Pi.single i 1) (L *ᵥ Pi.single j 1) := by simp
     _ = _ := by unfold L; rw [Matrix.mul_assoc,←mulVec_mulVec,dotProduct_mulVec,vecMul_transpose]
 have hv (j:K)(i:J⊕K) : L i (Sum.inr j)=fromBlocks A (0:Matrix J K ℝ) 0 B i (.inr j):=by
    rw [he,hn,V,hi]; cases i with
    | inl i=> rw [show Pi.single (Sum.inl i) (1:ℝ) ∘ (Sum.inr:K→J⊕K)=0 by ext; simp]; simp
    | inr i=> rw [show Pi.single (Sum.inr i) (1:ℝ) ∘ (Sum.inr:K→J⊕K)=Pi.single i (1:ℝ) by ext; simp [Pi.single_apply]]; simp
 have hQ:L=fromBlocks A 0 0 B:=by
   have hx:L.transpose=L:= by unfold L; simp only [Matrix.transpose_mul,Matrix.transpose_transpose,p,Matrix.mul_assoc]
   ext i j; cases j with
   | inr j=> exact hv _ _
   | inl j=> cases i with
     | inr i=> exact ((congrFun (congrFun hx (.inr i)) (.inl j)).symm).trans (hv i (.inl j))
     | inl i=> rw [he,hm,hm]; simp [← t]; rfl -- tune
 have ha:M.det=1:=by unfold M; rw [Matrix.det_fromBlocks_zero₂₁]; simp
 rw [show Q.det=L.det from (by unfold L; rw [Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,ha,one_mul,mul_one]),hQ]; exact Matrix.det_fromBlocks_zero₂₁ ..
end jac
variable (B:Bed)
def forecast:Matrix (Ink G C) (Ink G N) ℝ := (FreeResolvent.tensor G (probe S)).submatrix (brew G C) (brew G N)
lemma predicts_g (x:Dir G N) : forecast S G *ᵥ coil G x=coil G (bills S x) := by
 funext i; trans ((FreeResolvent.tensor G (probe S)) *ᵥ FreeResolvent.flatten x) (brew G C i); · exact Equiv.sum_comp (brew G N) (fun j=> FreeResolvent.tensor G (probe S) (brew G C i) j* FreeResolvent.flatten x j)
 exact congrFun (FreeResolvent.component_mul (probe S) (FreeResolvent.flatten x) _) (i.1.1,coord i.1.2)
lemma acts_at (x:Lace G N)(j:Ink G C): (forecast S G*ᵥ x) j=pressB S (fun p=> x (p,j.2)) j.1:=by
 rw [←coil_wrap G x,predicts_g,press_r]; rw [show contour (fun p=>coil G (laced G x) (p,j.2))=parts G 1 (laced G x) j.2 by funext i; obtain ⟨y,rfl⟩:=(coding N).surjective i; rw [coded y,contours _ y]; rfl]; rfl
local notation "Tn" => Ink G N
local notation "Tc"=> Ink G C
local notation "Fr"=> forecast S G
local notation "κ"=> S.kernel.penalty
def notice: Matrix (Tn⊕Tc) (Tn⊕Tc) ℝ := Matrix.fromBlocks (hess G B N+κ • ((Fr).transpose*Fr)) (-(κ • (Fr).transpose)) (-(κ • Fr)) (κ • (1:Matrix Tc Tc ℝ))
local notation "Q"=> notice S G B
lemma notion (x y:Tn ⊕ Tc→ℝ):
 let X:= x ∘ Sum.inl; let Y:= y ∘ Sum.inl
 dotProduct x (Q *ᵥ y)=dotProduct X (hess G B N *ᵥ Y)+κ*dotProduct (x∘ Sum.inr-Fr *ᵥ X) (y∘Sum.inr-Fr*ᵥ Y):=by intro X Y; unfold notice; rw [fblocks]; simp only [Matrix.add_mulVec,Matrix.neg_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_add,dotProduct_smul,dotProduct_neg,sub_dotProduct,dotProduct_sub]; simp only [←Matrix.mulVec_mulVec,dotProduct_transpose_mulVec,X,Y,smul_eq_mul]; rw [dotProduct_comm (y∘Sum.inr) (Fr *ᵥ (x∘Sum.inl)),dotProduct_comm (Fr*ᵥ(y∘Sum.inl)) (Fr *ᵥ (x∘Sum.inl))]; ring
lemma symmetric_m {p:Clip}{a b:ℝ}(h:Floor B p N a b): (Q).transpose=Q :=by unfold notice; simp only [Matrix.fromBlocks_transpose,Matrix.transpose_add,Matrix.transpose_neg,Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.transpose_smul,Matrix.transpose_one,hess_symm G B h]
lemma lemma_kg : probePair S G.ColorIndex≤LinearMap.ker (Q).mulVecLin:=by
 intro x h; obtain ⟨p,t⟩:=h; let X:=x∘Sum.inl; let Y:=x∘Sum.inr; have hp:x∘Sum.inr= Fr*ᵥ (x∘Sum.inl):= funext fun i=> (t i.2 i.1).trans (acts_at S G X i).symm; funext i; change (Q*ᵥ x) i=0; rw [show (Q*ᵥ x) i=dotProduct (Pi.single i 1) (Q *ᵥ x) by simp]; have ht:= notion S G B (Pi.single i 1) x; rw [ht]; simp [hp, show hess G B N *ᵥ (x∘Sum.inl)=0 from hess_ker G B p] -- hp rewrites F? tune

def solo (N C:Side): ScrollB G N ⊕ Ink G C ↪ Ink G N ⊕ Ink G C:=duo (fast G N) (Embedding.refl _)
local notation "T"=>solo G N C
end YM.CF.Papyrus.GaugeFlux
