import YM.CF.Cay.Chic
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Cay
open Slate Forge Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.Uniform (curve Slope tint partSpace meetVar)
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
variable {G:Gauge}{c f:Side}{S:StepData c f}{r v l n:ℕ}{w x β d:ℝ}{q:Chi}{T:Tube G S}{F:Forest S.ratio}{E A:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup A][NormedSpace ℝ A]
local notation "G"=>SU.group
variable {K:Teller SU.group}{T:Tube SU.group S}
def stars(T:Tube G S)(x:ℝ)(M:Monk G S)(q:Chi)(d:ℝ)(l:ℕ)(β:ℝ)(s:Signed):Along S → ℝ:= Sum.elim (Slate.payer T x M q d l β s) (Sum.elim (turF T.up (Stores.till x) (pull s 0 (M.sent x T q d l β))) (-turF T.down (Hors.cart x S.patch.L) (pull s 0 M.V)))
section
variable (T:Tube G S)(x:ℝ)(M:Monk G S)(q:Chi)(d:ℝ)(l:ℕ)(β:ℝ)
local notation "u"=> M.sent x T q d l β
local notation "y"=> M.fuel x T q d l β
local notation "μ"=> liftN T x M.V M.k M.key M.park q d (M.bush x) l
local notation "z₀"=> M.bush x
local notation "χ " z:arg=>Esti.axle M.key M.park T x M.k q d (M.bush x) z M.V -- notation may invalid
abbrev sepB := duty T M.key M.park M.V M.k q β d x z₀ l (M.bell x)
abbrev sepQ := phere T M.key M.park M.V M.k q d x z₀ l (M.bell x)
def potH:= -β*(averaged fun s=>∑ i:Along S,stars T x M q d l β s i)
def aster:=potH T x M q d l β+ sepB T x M q d l β +sepQ T x M q d l
lemma media_q (S:StepData c f)(a:Prices G (Slots S)) : (Fintype.card Signed:ℝ)⁻¹ * (∑ i,media i (tape a))=(a ⬝ᵥ a)/2:=by
 let C:ℝ:=Fintype.card Signed; have ht:0<C:= Nat.cast_pos.mpr Fintype.card_pos; simp_rw [SectorChange.price_square,sum_div,mul_sum]; apply Finset.sum_congr rfl; intro i _; unfold media Rows.slip; rw [norm_smul, Real.norm_eq_abs,mul_pow,sq_abs,inv_inv,Real.sq_sqrt ht.le]; change C⁻¹* _= _; field_simp
lemma dawn(S:StepData c f)(p:Slots S→ℝ): averaged (fun s=>∑ i:Along S, Sum.elim (Gloss S s p) (fun _=>0) i)=(Fintype.card Signed:ℝ)⁻¹ * (∑ i,p i):=by
 unfold Along Gloss averaged; simp [Fintype.sum_sum_type,Fintype.sum_prod_type]
open Matrix
lemma trim(h:0<β): let a:= M.fuel x T q d l β; (β*((χ a) ⬝ᵥ (χ a))/2 -β*((χ μ) ⬝ᵥ (χ μ))/2)+sepB T x M q d l β + sepQ T x M q d l=costU (M.bell x)/2:=by
 intro a; let γ:=coupling β; let Y:= tape.symm (M.bell x); let P:= Rows.move T x M.V M.k (shots S x) M.key M.park; let Q:= credW T M.key M.park M.k q d x z₀ l M.V; let U:= P*(Q); let W:= U*ᵥ Y; let N:=χ μ; have he : χ a=N+γ • W:=by
    change P *ᵥ (μ +γ • (Q *ᵥ Y))+Offset.f0 T x M.key M.park M.k M.V q d z₀= _; unfold N W U axle; rw [mulVec_add,mulVec_smul,←mulVec_mulVec]; unfold P; abel
 rw [he]; have hb:Dira T M.key M.park M.k q d x z₀ l M.V= U.transpose *ᵥ N:=by
    change Q.transpose *ᵥ ((P.transpose*P)*ᵥ μ + P.transpose *ᵥ (Offset.f0 T x M.key M.park M.k M.V q d z₀))= _; rw [show U.transpose= Q.transpose * P.transpose from Matrix.transpose_mul ..]; unfold N axle P; simp only [←mulVec_mulVec,mulVec_add]
 have ht : fullV T M.key M.park M.k q d x z₀ l M.V=U.transpose*U-1:=by unfold U fullV perturb fuseQ baseX Rows.gram; unfold Q P; rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
 unfold sepB sepQ duty phere; rw [hb,ht]; rw [add_dotProduct]
 have hy:β=(γ^2)⁻¹:= (by_coupling h).symm; have hg:γ ≠0:=(coupling_pos h).ne'
 change (β*((N ⬝ᵥ (N + γ • W))+ ((γ • W) ⬝ᵥ (N+γ • W)))/2-β*(N ⬝ᵥ N)/2)+-γ⁻¹*(U.transpose *ᵥ N ⬝ᵥ Y)+(-(Y ⬝ᵥ ((U.transpose*U-1)*ᵥ Y))/2)=(Y ⬝ᵥ Y)/2; rw [dotProduct_add,dotProduct_add,smul_dotProduct,smul_dotProduct,dotProduct_smul,dotProduct_smul,dotProduct_comm W N]
 -- tune priority; no rw hy directly target as U N β dep fixed.
 rw [dotProduct_comm (U.transpose *ᵥ _),Matrix.dotProduct_transpose_mulVec,Matrix.sub_mulVec,one_mulVec,dotProduct_sub,← mulVec_mulVec Y U.transpose U,Matrix.dotProduct_transpose_mulVec,hy]; simp only [smul_eq_mul]; unfold W; field_simp; ring -- dot orientation
lemma deck_x (h:0<β)(p:K.Funds S T):aster T x M q d l β= -β*(mainTerm T.high (grainA T.up (Stores.till x)) u + noiseTaylor S M.V u M.k-mainTerm T.low (grainA T.down (Hors.cart x S.patch.L)) M.V)+costU (M.bell x)/2:=by
 let Z:=χ y; let X:=χ μ; let P(i):=media i (tape Z)-media i (tape X); have he(s:Signed):stars T x M q d l β s=ballot T x (pull s 0 M.V) (pull s 0 u) (choice s M.k) - Sum.elim (Gloss S s P) (fun _=>0):= by funext i; rcases i with i|i|i; exact rfl; exact (sub_zero _).symm; exact (sub_zero _).symm
 unfold aster potH; simp_rw [he,Pi.sub_apply,sum_sub_distrib]; rw [av_sub,wise T p,dawn S]; unfold P; rw [sum_sub_distrib,mul_sub ((Fintype.card Signed:ℝ)⁻¹),media_q S,media_q S]; have hp:=trim T x M q d l β h; unfold X Z; rw [←hp]; ring
end
end YM.CF.Cay
