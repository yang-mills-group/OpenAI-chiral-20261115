import YM.OS.Core
import Acacia.Crema
import HectorA.Iota
import HectorA.InShift
import Acacia.Rill
import Acacia.Smith
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 300000
set_option quotPrecheck false
noncomputable section
namespace Acacia
open Filter Function Finset Set YM.OS YM Yoland
open scoped Topology NNReal BigOperators Classical InnerProductSpace
attribute [local instance] InnerProductSpace.complexToReal
variable {H:Hilbert}{a:Axis}(S:OS.Semigroup H a)
lemma swing_pay(k:ℕ){t:ℝ}(v:0<t)(x y:H): inner ℂ (_root_.Yoland.pay S k t x) y=inner ℂ x (_root_.Yoland.pay S k t y):=by
 let L(x:H):H.space→L[ℝ]ℂ:= (innerSL ℂ x).restrictScalars ℝ
 let A: H.Op→L[ℝ] H := (ContinuousLinearMap.apply ℂ H.space x).restrictScalars ℝ
 let f:=Complex.conjCLE.toContinuousLinearMap
 let g(z:ℝ):=dawn S z
 let K:H.Op→L[ℝ] H := (ContinuousLinearMap.apply ℂ H.space y).restrictScalars ℝ
 have hx:(f.comp ((L y).comp A)) ∘ g=(L x).comp K ∘ g:=by funext r; change (starRingEnd ℂ) (inner ℂ y (g r x))=inner ℂ x (g r y); rw [inner_conj_symm]; exact S.swing _ _ _
 have hp : AnalyticAt ℝ g t:=dawnRise S _ v
 have e:= congrArg (fun g:ℝ→ℂ=>iteratedDeriv k g t) hx
 rw [transport hp,transport hp] at e
 rw [←inner_conj_symm (𝕜:=ℂ)]; exact e
-- positive-preserving removal paste for derivative. 
lemma pay_ortho (L:H)(k:ℕ)(e:0<k){t:ℝ}(q:0<t)(s:∀ i,S.E i L=L)(z:H):inner ℂ L (_root_.Yoland.pay S k t z)=0:=by
 rw [←swing_pay S k q,keeps S L k q (fun r=>s _) e, inner_zero_left]
#print axioms swing_pay
end Acacia
