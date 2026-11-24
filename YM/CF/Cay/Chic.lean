import YM.CF.Slate.Fast
import YM.CF.Vol.Pallas
import YM.CF.Appel.Font
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
def euro (T:Tube G S)(R:ℕ)(U:Config G f)(V:Config G c)(t s:ℝ)(Y: Bond c→ SU.group.Mat) :=(∑ i:Cell f, kF T R t s ∅ ∅ V U i)+(∑ i:Bond c, kI T R s ∅ V Y i)+((∑ i:Cell c,(kC T R s ∅ V i+(kL T R s ∅ V U Y i+ kD T R s ∅ V i))) + (∑ i:Co c Gain,kN T R s ∅ V i))
lemma lilo (U:Config G f)(V:Config G c)(t s:ℝ)(Y:Bond c→SU.group.Mat): euro T r U V t s Y= (∑ i:Cell f,king ∅ T.up T.high r 1 t U i)+ (∑ i:Bond c,S.kernel.penalty*fareG G (Y i))- (∑ i:Cell c,king ∅ T.down T.low r S.patch.L.val s V i):=by
 let w:=wV T r s ∅ V; let e:=zF T r s ∅ V; let f:=zI T r s ∅ V; let G':= Pressure.zip (T.N r V) w
 have hN:=arity (T.N r V) G' w; have hF:=arity (T.Φ r V) e w; have hf:=arity (T.Φ' r V) f w; have h1:=arity (T.Φ r V) (T.Xf r U) w; have h2:=arity (T.Φ' r V) (kZ (S:=S) Y) w
 unfold G' w e f zI zF at *; simp_rw [euro,kF,kI,kC,kL,kD,kN,zI,zF,inner_sub_right,inner_add_right,real_inner_self_eq_norm_sq,sum_sub_distrib,sum_add_distrib,← sum_div]; unfold Twin at *; simp_rw [Fintype.sum_prod_type, real_inner_self_eq_norm_sq] at *; simp only [sum_sub_distrib,sum_add_distrib,← sum_div]; linarith only [hN,hF,hf,h1,h2]
open Hors
lemma lilo_Y (U:Config G f)(V:Config G c)(k:S.Choices)(t s:ℝ) : let Q:=S.prediction U k; (∑ i:Dill S,Yaught T r t s V U k i)=(∑ i,king ∅ T.up T.high r 1 t U i)+(∑ i,Tube.monetary S Q V i)-∑ i,king ∅ T.down T.low r S.patch.L.val s V i:=by
 intro Q; rw [show (∑ i:Dill S,_) = euro T r U V t s (wit V Q) from ?_,lilo]; swap
 · unfold Dill; simp only [Fintype.sum_sum_type]; unfold euro Yaught; simp only [Sum.elim_inl,Sum.elim_inr,Q,add_assoc]
 congr 1; congr 1; refine sum_congr rfl fun i _=>?_ ; unfold wit Tube.monetary Pressure.wire; rw [fare_h,SU.group.chord_price]; ring
lemma kin_q (d:ℕ)(h:0<d)(u:PathData G)(q:Clip)(x:ℝ)(V:Config G c)(i:Cell c): king ∅ u q r d x V i=q.direct*SU.group.price (faceValue V i)+ ‖(grainA u (r/d)).ell V i‖^2/2:=by
 rw [manta,Fintype.sum_bool]; unfold sore plotted shoot; simp only [if_true,Bool.false_eq_true,↓reduceIte,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,Real.sq_sqrt q.quadratic_pos.le]
 rw [show shorten u r d V i= (grainA u (r/d)).ell V i from ?_]; ring
 refine tsum_congr fun j=>?_ ; unfold shortenTerm PathData.ellTerms grainA; dsimp only; simp only [Nat.le_div_iff_mul_le h]; split <;> simp [*]
def turF(u:PathData G)(q:ℕ)(V:Config G c)(i:Site c):= gplot (batch u.cubic q) V i + gplot (batch u.quartic q) V i
abbrev Along(S:StepData c f):= Dill S⊕ Site f⊕Site c
def ballot (T:Tube G S)(x:ℝ)(V:Config G c)(U:Config G f)(k:S.Choices): Along S→ℝ:= Sum.elim (Yaught T (Stores.till x) (fiery G x S.patch.L) (temp x) V U k) (Sum.elim (turF T.up (Stores.till x) U) (- turF T.down (Hors.cart x S.patch.L) V))
lemma plus_q (d:ℕ)(hd:0<d)(V:Config G c)(u:PathData G)(q:Clip)(t:ℝ): (∑ i,king ∅ u q r d t V i)+(∑ i,turF u (r/d) V i)= ∑ i,fOre q (grainA u (r/d)) V i :=by
 simp_rw [kin_q d hd]; change (∑ x:Site c × PlaqAxes,_) +_= _; rw [Fintype.sum_prod_type]; unfold fOre turF; simp_rw [sum_add_distrib,gplot,batch,grainA]; simp only [add_assoc]
lemma poseA(U:Config G f)(V:Config G c)(k:S.Choices)(x:ℝ) : (∑ i:Along S,ballot T x V U k i) = (∑ i:Site f,fOre T.high (grainA T.up (Stores.till x)) U i)+ (∑ i:Bond c,Tube.monetary S (S.prediction U k) V i)-(∑ i:Site c,fOre T.low (grainA T.down (cart x S.patch.L)) V i):=by
 let a:= plus_q 1 Nat.one_pos U T.up T.high (fiery G x S.patch.L) (r:=Stores.till x); rw [Nat.div_one] at a; let b:=plus_q S.patch.L.val S.patch.L.property V T.down T.low (temp x) (r:=Stores.till x)
 unfold Along; rw [Fintype.sum_sum_type]; rw [show ∀ g:Site f ⊕ Site c → ℝ,(∑ i,g i)=(∑ i,g (.inl i))+(∑ i,g (.inr i)) from fun i=> Fintype.sum_sum_type ..]; unfold ballot; simp only [Sum.elim_inl,Sum.elim_inr]; rw [lilo_Y,← a,← b]; simp only [Pi.neg_apply,sum_neg_distrib]; abel
lemma wonB (p:Clip)(t:PathData G)(V:Config G c): averaged (fun s=> ∑ i,fOre p t (pull s 0 V) i)= mainTerm p t V:=by unfold mainTerm Patch.average quadratic uncut fOre averaged; simp_rw [Fintype.sum_prod_type]; simp only [mul_add,sum_add_distrib,mul_sum]
lemma wise(T:Tube G S)(p:K.Funds S T)(U:Config G f)(V:Config G c)(k:S.Choices): averaged (fun s=> ∑ i:Along S,ballot T x (pull s 0 V) (pull s 0 U) (choice s k) i)=mainTerm T.high (grainA T.up (Stores.till x)) U+noiseTaylor S V U k-mainTerm T.low (grainA T.down (cart x S.patch.L)) V:=by
 let W:= S.prediction U k; let M:=∑ i:Bond c,Tube.monetary S W V i; have he(s:Signed):(∑ i, Tube.monetary S (S.prediction (pull s 0 U) (choice s k)) (pull s 0 V) i)=M:=by
    rw [(carry s (funds_branch p) k U).2]; unfold Tube.monetary; simp_rw [wire_pulled]; exact Equiv.sum_comp (StepData.sendBonds s 0) fun i=> Tube.monetary S W V i
 simp_rw [poseA,he]; rw [av_sub,av_add,av_const,wonB,wonB]; suffices h : M=noiseTaylor S V U k by rw [h]
 unfold M noiseTaylor; rw [mul_sum]; refine sum_congr rfl fun i _=>?_ ; unfold Tube.monetary Pressure.wire W; rw [SU.group.chord_price]; ring
end YM.CF.Cay
