import YM.CF.Tale.Drum
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
set_option quotPrecheck false
namespace YM.CF.Tale
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Next Next.Free PhysicalNext.JointLoad Cube SU Exterior Cascade Bloch
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open Heir AnalyticBridge.SectorAffine.Offset AnalyticBridge.VerifiedReset
open Pressure Tube Siete
variable {c f:Side} 
variable{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{x C M A a η δ α γ Ω:ℝ}{J:S.Choices}{n m:ℕ}
local notation "G5"=> SU.group
open StressFlux
variable (k:ℝ)(j t:ℕ)(h:0<k)(pM:4≤j)(v:4≤t)(P:Flight j t)(w:f.val=c.val*P.L.val)
local notation "L"=> (P.L)
local notation "G_"=> (deckY j t P w)
-- use receipt quantified over any trajectory. constants projection.M
private lemma love_p {x y v w: SU.group.Color}{ε t:ℝ}(hx:‖x-v‖ ≤ ε)(hy:‖y-w‖ ≤ ε)(hp:‖v‖≤ t)(hq:‖w‖ ≤ t): ‖inner ℝ x y-inner ℝ v w‖≤ ε*(2*t+ε):=by
 have h:‖x‖≤ ε+t:= (norm_le_norm_sub_add x v).trans (add_le_add hx hp)
 have ht:‖y‖≤ε+t:=(norm_le_norm_sub_add y w).trans (add_le_add hy hq)
 rw [show inner ℝ x y-inner ℝ v w=inner ℝ (x-v) y+inner ℝ v (y-w) from (by rw [inner_sub_left,inner_sub_right]; abel)]
 exact (norm_add_le ..).trans ((add_le_add ((norm_inner_le_norm ..).trans (mul_le_mul hx ht (norm_nonneg _) ((norm_nonneg _).trans hx))) ((norm_inner_le_norm ..).trans (mul_le_mul hp hy (norm_nonneg _) ((norm_nonneg _).trans hp)))).trans_eq (by ring))
private lemma joy_k(a b c d u v x z:ℝ)(hq:‖a‖≤x)(hp:‖d‖≤x)(hx:‖b-u‖≤ z)(hv:‖c-v‖≤ z): ‖a+b+c+d-(u+v)‖≤ 2*(x+z):=by rw [show a+b+c+d-(u+v)=a+(b-u)+(c-v)+d by ring]; exact (norm_add_le ..).trans ((add_le_add ((norm_add_le ..).trans (add_le_add ((norm_add_le ..).trans (add_le_add hq hx)) hv)) hp).trans_eq (by ring))
variable (o:Site c)(p:BudgetPoint)(r l:ℕ)(q:l≤ r)(he:2*l<c.val)(hL:5≤ P.L.val)
local notation "θ"=> (p.threshold)
local notation "π'"=> (((P.L.val:ℝ)⁻¹)^2)
local notation "Xq"=> (deckY j t P w).embed o
local notation "Zt"=> clipT p o
variable {X:townX c→ townX f}(TH:Thy j t k a C)(hx: Guide (townX c) (p.dirBound o) 0 X m γ)(hg:Guide (townX c) (p.dirBound o) 0 (X- ⇑(trade_L k j t P w o r)) m δ)(h2: δ ≤1)(hM:2 ≤ m)
include TH hx hg h2 hM q he hL
abbrev a_Op(n:Side)(o:Site n)(a b:PlaqAxes)(V:Config SU.group n):ℝ:= inner ℝ (petals V o a) (petals V o b)
local notation "Λ"=>lens_k L p
local notation "Qt"=> (C*δ*γ+C*δ+C*θ*π'*Real.exp (-a*l))
abbrev zolo (p:BudgetPoint)(L':Side)(s a b r:PlaqAxes):= inner ℝ (lens_k L' p s a) (lens_k L' p b r)
local notation "Γ"=> (fun x:townX c=>increment (G:=SU.group) 1 (X x))
abbrev perkV (a C ε δ p l t:ℝ):= C*δ*ε+C*δ+C*p*l*Real.exp (-a*t)
abbrev humpV (a C ε δ p l t:ℝ):= let d:=perkV a C ε δ p l t; 2*((C*(ε^2+δ))*(C*δ)+d*(2*(l*p)+d))
local notation "QK"=> humpV a C γ δ θ π' l
lemma sonic_S (A B:PlaqAxes) (Y Z:PlaqAxes): ‖iteratedFDeriv ℝ 2 ((a_Op f Xq A B) ∘ Γ) 0 ![Zt Y,Zt Z]- (zolo p L Z A Y B+ zolo p L Y A Z B)‖ ≤ QK:=by
 let V(Q:PlaqAxes):= (fun x:townX c=> petals (Γ x) Xq Q); let U:=V A; let P':=V B; let v(Q):=fderiv ℝ (V Q) 0
 have he(i Jx k':PlaqAxes):=leo_P k j t P w o p r l q he hL i Jx TH hx hg h2 hM k' -- ordering conflict notation
 have hp:=he Y Z A; have hr:=he Y Z B
 let H:ℝ:=C*(γ^2+δ); let h:ℝ:=C*δ; let hx':ℝ:=Qt*(2*(π'*θ)+Qt)
 have hh(A B): ‖Λ A B‖ ≤ π'*θ:=by
    have ht:=p.threshold_pos; unfold lens_k; split; rw [norm_smul,norm_smul,Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg ht.le,spike_norm Thera.yet_one,mul_one]
    rw [smul_zero,norm_zero]; positivity
 have h0(A B K J):‖inner ℝ (v B (Zt A)) (v J (Zt K))- zolo p L A B K J‖ ≤ hx':=love_p (he A A B).2.1 (he K K J).2.1 (hh ..) (hh ..) -- type tune
 change ‖iteratedFDeriv ℝ 2 (fun z=>inner ℝ (U z) (P' z)) 0 _ - _‖≤ _
 rw [duet_2 (f:=U) (g:=P') (Zt Y) (Zt Z) hp.2.2.1 hr.2.2.1] -- def
 refine joy_k _ _ _ _ _ _ (H*h) hx' ?_ ?_ (h0 Z A Y B) (h0 Y A Z B)
 · exact (norm_inner_le_norm ..).trans (mul_le_mul hp.2.2.2 hr.1 (norm_nonneg _) ((norm_nonneg _).trans hp.2.2.2))
 rw [mul_comm H]; exact (norm_inner_le_norm ..).trans (mul_le_mul hp.1 hr.2.2.2 (norm_nonneg _) ((norm_nonneg _).trans hp.1))
variable {S':StepData (More c) (More f)}
end YM.CF.Tale
