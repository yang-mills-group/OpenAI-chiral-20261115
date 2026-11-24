import YM.CF.Esti.Sea
import YM.CF.Vol.Celt
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Baton
import YM.CF.Palot.End
import YM.CF.Appel.Sat
import YM.Next.FLUCTUATIONS.Grants
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Wind
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Esti
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD
open Ac
variable {c f:Side}(S:StepData c f){r v:ℕ}
open CF.Jet
local notation "G"=> SU.group
variable {S}{n:ℕ}{θ a b m x t w K C d:ℝ}
variable {K': Teller G}{A B:Stores S}{T:Tube G S}{V:Config G c}{U:Config G f}{k:S.Choices}{q:Chi}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Nonempty E]{x':E}
open AnalyticBridge.Annulus1AD Push.SectorMeasure.Oriented Pressure.Tube
variable {F:Forest S.ratio}{Y:LinkArray G (Frozen A x F)}{β c' D L v':ℝ}
def cardsQ (p: Affine.Window S):= p.face.card+p.noise.card+p.coarse.card+p.rows.card
abbrev media(P:Slots S) (X:LogArray G (Slots S)):= ‖Rows.slip⁻¹ • X P‖^2/2
def columnP(s:Signed)(X:LogArray G (Slots S))(p:Affine.Window S):= (∑ i∈p.face,∑ j:Bool, media (s,.inl (i,j)) X)+(∑ i∈p.noise,media (s,.inr i) X)
lemma sells(s:Signed)(p:Affine.Window S)(z:Prices G (Active A x F))(h: f0 T x A F k V q d Y=Rows.source T x V k (shots S x) A F q d Y) (hx:K'.Funds S T): columnP s (wheel A F T x k q d Y z V) p= columns V x k T F A q d Y z s p:=by
 obtain ⟨i,j,K,-⟩:=hx.feeds; rw [←hx.high] at K; rw [along _ _ _ _ _ _ _ _ _ _ h K]; unfold columnP columns
 have he(X:Where S)(u:SU.group.Color)(p:Prop)[Decidable p]: ‖Rows.slip⁻¹ • (if p then Rows.slip • u else 0)‖^2/2= if p then ‖u‖^2/2 else 0:=by split <;> simp [inv_smul_smul₀ Rows.slip_pos.ne']
 congr 1; exact sum_congr rfl fun i _=> sum_congr rfl fun j _=>he (.inl i) _ _; exact sum_congr rfl fun i _=>he (.inr i) _ _
variable {W:E→ LogArray G (Slots S)}{F':Finset (Cell f)}{Q':Finset (Cell c)}{U':E→ Config G f}{V':E→ Config G c}{M':E→ Bond c→ SU.group.Mat}
def carV (n:ℕ)(D:ℝ):=let p:=Rows.slip⁻¹*D; (2:ℝ)^n*p*p
lemma me_p (H: Allows n W x' C)(s:Slots S):Allows n (fun y=> media s (W y)) x' (carV n C):=by
 let p:= ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:Slots S=>SU.group.Color) s; have hp : ‖p‖ ≤ 1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun i=> (norm_le_pi_norm i s).trans_eq (one_mul _).symm
 have hh:= ((H.linear p hp).smul Rows.slip⁻¹); rw [one_mul,abs_of_nonneg (inv_nonneg.mpr Rows.slip_pos.le)] at hh; exact cow hh
lemma summed{E D:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup D][NormedSpace ℝ D]{x:E}{I:Type}(X:Finset I)(V:I→E→ D)(p:∀ i∈X, Allows n (V i) x C): Allows n (fun y=>∑ i∈X,V i y) x (X.card*C):= by simpa only [sum_const,nsmul_eq_mul] using Jet.allows_sum (s:=X) p -- tune implicit
lemma col_p (H: Allows n W x' C)(s:Signed)(p:Affine.Window S){N:ℝ}(h:(cardsQ p:ℝ) ≤N):Allows n (fun y=> columnP s (W y) p) x' (2*N*carV n C):=by
 have ht:= H.nonneg; have hv:0 ≤ carV n C:=by unfold carV; dsimp only; have hx:0<Rows.slip:=Rows.slip_pos; positivity
 apply Allows.mono ((summed p.face _ (fun i _=>summed univ _ (fun (j:Bool) _=> me_p H (s,.inl (i,j))))).add (summed p.noise _ (fun i _=>me_p H (s,.inr i))))
 simp only [card_univ, Fintype.card_bool,Nat.cast_ofNat]; unfold cardsQ at h; push_cast at h; nlinarith [Nat.cast_nonneg (α:=ℝ) p.rows.card, Nat.cast_nonneg (α:=ℝ) p.coarse.card, Nat.cast_nonneg (α:=ℝ) p.noise.card, Nat.cast_nonneg (α:=ℝ) p.face.card] -- tune
lemma vsum (p:Circus T t v' F' Q' U' V' M' x' r n C) (h:0≤C)(Q:Affine.Window S){X:ℝ}(hx:(cardsQ Q:ℝ)≤X): Allows n (fun y=> ore T r t v' F' Q' (V' y) (U' y) (M' y) Q) x' (X*C):=by
 apply Allows.mono ((((summed Q.face _ (fun i _=> p.L1 i)).add (summed Q.noise _ (fun i _=>p.L2 i))).add (summed Q.coarse _ (fun i _=>p.L3 i))).add (summed Q.rows _ (fun i _=>p.L4 i)))
 simp_rw [←add_mul]; unfold cardsQ at hx; push_cast at hx; gcongr
-- total payment at real.T=YT & A^ flags
variable (T:Tube G S)(V:E → Config G c)(n:ℕ)(x:ℝ)(A:Stores S)(F:Forest S.ratio)(u:S.Choices)(q:Chi)(θ:ℝ)(Y: LinkArray G (Frozen A x F))(a δ:E→Prices G (Active A x F))(s:ℝ)
local notation "B_"=>fun y=>landed x A F (V y) Y (a y)
def pist (M:Signed→Affine.Window S)(β:ℝ) := fun y=> -β*averaged (fun z:Signed=> caseP T x A u q s ((B_) y) (V y) z (M z)- columnP z (wheel A F T x u q θ Y (a y) (V y)) (M z)+columnP z (wheel A F T x u q θ Y (δ y) (V y)) (M z))
variable (h:∀ z:Signed,Circus T (fiery G x S.patch.L) (temp x) ((turnStore z A).costs) (traceZ (turnStore z A).flags) (pull z 0 ∘ fun y=>landed x A F (V y) Y (a y)) (pull z 0 ∘ V) (fun y=>layS q u A x s (landed x A F (V y) Y (a y)) (V y) z) x' (Stores.till x) n C)
include h
lemma past {X:ℝ}(M:Signed→Affine.Window S) (p:Allows n (fun y=>wheel A F T x u q θ Y (a y) (V y)) x' D) (t:Allows n (fun y=>wheel A F T x u q θ Y (δ y) (V y)) x' D)(hx:∀ s,(cardsQ (M s):ℝ)≤X)(hp:0≤C): Allows n (pist T V x A F u q θ Y a δ s M β) x' (|β| *(X*C+2*X*carV n D+2*X*carV n D)):=by
 let t':=(Fintype.card Signed:ℝ)⁻¹; let g:= Jet.allows_sum (s:=univ) (fun (z:Signed) _=> (minus_e (vsum (h z) hp (M z) (hx z)) (col_p p z (M z) (hx z))).add (col_p t z (M z) (hx z))); let H:=pist T V x A F u q θ Y a δ s M β
 have hx := (g.smul t').smul (-β); apply hx.mono _ -- tune comm
 simp only [abs_neg,sum_const,card_univ,nsmul_eq_mul]; unfold t'; rw [abs_of_nonneg (show (0:ℝ) ≤ (Fintype.card Signed:ℝ)⁻¹ by positivity),inv_mul_cancel_left₀]; exact_mod_cast Fintype.card_ne_zero
end YM.CF.Esti
