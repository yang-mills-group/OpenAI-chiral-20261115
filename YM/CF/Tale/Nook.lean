import YM.CF.Tale.Pace
import YM.CF.Siete.Tree
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Tale
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Next Next.Free PhysicalNext.JointLoad Cube SU Exterior Cascade Bloch
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open Heir AnalyticBridge.SectorAffine.Offset AnalyticBridge.VerifiedReset
open Pressure Tube Siete
variable {c f:Side} 
-- main to compute jet estimate for any authorized step T after L. Crop identity. Portrait receipts grant
variable {S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{x h C M A a t r η δ ε:ℝ}{J:S.Choices}{n m:ℕ}
local notation "G5"=> SU.group
variable (o:Site f) (v:Directions SU.group f) (p:BudgetPoint)(w:p.power=n)
local notation "K"=> (S.ratio.parent o)
-- crop cuts
abbrev clipT (p: BudgetPoint)(o:Site c)(V:PlaqAxes): Directions SU.group c:= (AnalyticBridge.VerifiedReset.wedge V (p.threshold • AnalyticBridge.VerifiedReset.spike SU.group)).field o
private lemma wedge_s (a:ℝ)(o:Site c)(U:PlaqAxes)(K':group.Color): (AnalyticBridge.VerifiedReset.wedge U (a• K')).field o=a • (AnalyticBridge.VerifiedReset.wedge U K').field o:=by
 ext1 i; simp only [wedge_field,Pi.smul_apply]; split; exact smul_comm _ _ _; exact (smul_zero a).symm
lemma fore_l (o:Site c)(s:PlaqAxes): p.dirBound o (clipT p o s):=by
 rw [clipT,wedge_s]; apply wedge_dir; exact (spike_norm Thera.yet_one).le
lemma curt_q (o:Site c)(p:BudgetPoint)(r:ℕ)(n:ℕ): Guide (townX c) (p.dirBound o) 0 (curt r o) n (loom p r 1):=by
 let L:= curt r o; have hx:0≤ loom p r 1:=by unfold loom; have ht:=p.threshold_pos; positivity
 refine ⟨L.contDiff.contDiffAt,fun i v u h=>?_⟩; change ‖iteratedFDeriv ℝ i L 0 u‖ ≤ _; obtain (_|(_|i)):=i -- incorrect pattern
 · simpa [hx] using hx
 · rw [show (u)=![u 0] from (by funext i; fin_cases i;rfl),iteratedFDeriv_one_apply,L.fderiv]; unfold L; refine (pi_norm_le_iff_of_nonneg hx).mpr fun i=>?_ ; rw [curtP]; split; rename_i t; swap; · rw [norm_zero]; exact hx
   have ht:= h 0 i; unfold loom; rw [one_mul]; refine ht.trans ?_; rw [separation_comm]; gcongr; exact p.threshold_pos.le
 rw [sterile L _ (by omega)]; simp [hx] -- tune
variable (X:Directions G5 c→ Directions G5 f)
lemma exhib (B:Directions G5 c→Prop){y:Directions G5 c}{D:Directions G5 c→Deck G5 c f}(P:Guide (Directions G5 c) B y D m C)(q:Tour T F x J m r A)(h0:temp x≤ C)(p:1≤ A)(k:C≤1)(hr:C≤ r)(t:2≤ m): let G:=display T F x J true; let Ψ:=mainStroke T F true; Guide (townX c) B y (G∘ D- Ψ ∘ D) m (clinicFee m A*C^2)∧ Guide (townX c) B y (G∘ D) m (clinicFee m A*C^2+ ‖Ψ‖*C):=by
 intro G L
 have hv:Guide _ B y (G ∘ D- L ∘ D) m (clinicFee m A*C^2):=handle (q.costs true) h0 (zero_le_one.trans p) k hr P t
 refine ⟨hv,?_⟩; have hx:Guide _ B y (L∘ D) m (‖L‖*C):=by
    refine ⟨L.contDiff.contDiffAt.comp _ P.1,fun i l z q=>?_⟩; rw [L.iteratedFDeriv_comp_left P.1 (Nat.cast_le.mpr l)]; exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (P.2 i l z q) (norm_nonneg _))
 rw [show G∘ D=(G∘ D- L ∘ D)+(L∘D) by abel]; refine ⟨hv.1.add hx.1,fun i l z p=>?_⟩; rw [iteratedFDeriv_add_apply (hv.1.of_le (Nat.cast_le.mpr l)) (hx.1.of_le (Nat.cast_le.mpr l))]; exact (norm_add_le ..).trans (add_le_add (hv.2 _ l z p) (hx.2 _ l z p))
-- cheaper bound via direct composition (norm of main not needed). D= (clipped linear,Y noise map) Guide~l; derivatives value output of jets. RHS.Guide Hess.
lemma exhibit (X:Directions G5 c→ Directions G5 f)(o:Site c)(r':ℕ){D:Directions G5 c→Directions G5 f} (h:Guide (Directions G5 c) (p.dirBound o) 0 D m δ)(hr:δ ≤ C)(q:Tour T F x J m r A)(h0:temp x ≤ C)(hP:1≤ A)(k:C ≤1)(u:C ≤ r)(t:2≤ m)(hx:loom p r' 1 ≤ C) (hX:X=display T F x J true ∘ fun v=>(curt r' o v,D v)) (H: ℝ)(hL:‖mainStroke T F true‖ ≤ H): let τ:=clinicFee m A*C^2; let R:= (Heir.route T ∘ (curt r' o)); Guide (Directions G5 c) (p.dirBound o) 0 X m (τ+ H*C) ∧ Guide (Directions G5 c) (p.dirBound o) 0 (X- R) m (τ+δ):=by -- tune expr
 intro τ R; let E(v):=(curt r' o v, D v); have he: Guide (Directions G5 c) (p.dirBound o) 0 E m C:=((curt_q o p r' m).rise hx).duo (h.rise hr)
 obtain ⟨i,z⟩:=exhib _ he q h0 hP k u t; rw [hX]; let Z:= mainStroke T F true; refine ⟨(z.rise (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hL ((norm_nonneg _).trans he.size)))),?_⟩; let X':=display T F x J true
 change Guide _ _ _ (X' ∘ E- R) _ _; rw [show X' ∘ E- R=(X' ∘ E-Z ∘ E)+D from ?_]; swap; · rw [show Z ∘ E= R+D from rfl]; abel
 refine ⟨i.1.add h.1,fun k l z v=>?_⟩; rw [iteratedFDeriv_add_apply (i.1.of_le (Nat.cast_le.mpr l)) (h.1.of_le (Nat.cast_le.mpr l))]; exact (norm_add_le ..).trans (add_le_add (i.2 k l z v) (h.2 k l z v))
end YM.CF.Tale
