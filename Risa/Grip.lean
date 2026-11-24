import Risa.Weak
import LusterS.Rogue
import YM.SU5.Regis.Trophy
/-! # Sparse defect treatment under outer-threshold tree purchase -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.flexible false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.Gleam.Luster
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ v' ν θ ω':ℝ}{U:Config G n}{A:Support c}{m:ℕ} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}{J:ChartRatio G}
variable {X Y:fieldDir G n 1}{D:Finset (Cell n)}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L:Floor H q n δ w)(D':LocalRatio J)
namespace Risa
open Regis ProbabilityTheory
variable {χ fuel :ℝ}
include B
lemma weak_grip (hD:D=weak p.threshold U)(d:A=broken r v' U)(hr:p.threshold≤v')(l:EnoughMark q p m)(d':0<β)(f:ProbeBox X (2*v))(g:ProbeBox (X+Y) (2*v))(h:TrustLogs (X+Y) U r A v)(u:abandon X r A m)(uD:vacuumR X D (hallBill m))(s:0≤v)(t:v≤ R.c)(p':0 ≤ C)(hx:0 ≤ ξ)(hz:κ+(χ+ν) ≤ β*(q.linear*p.threshold^2/2))(hs:χ+ν ≤ β*(q.direct*p.threshold^2/2))(hm:fuel+21^4*ξ ≤ β*(q.linear*p.threshold*v'/2)): goods Z q p β κ fuel v' U ≤ Real.exp ((-β*∑ b:Cell n,flash Z q r D A m b X Y) + ((taxΔ R q n p β v η C S m - ξ*A.card)-(χ+ν)*D.card)):=by
 let T:= CF.Graph.taxY n β p.threshold C S; let F(b:Cell n):=flash Z q r D A m b X Y; let Y'(b:Cell n):= Z.baseTerm q p U b; let t':=κ/β; let χ0:= (χ+ν)/β; let v'':=q.linear*p.threshold*v'/2; let m':ℝ:=(misdemean p.threshold U).card; let uT:ℝ:=D.card; let l':ℝ:=(misdemean v' U).card; let R':=(21:ℝ)^4
 apply Real.exp_monotone
 have hr:(∑ b:Cell n,F b)+(t'*m'+χ0*uT+v''*l')≤ (∑ b:Cell n,Y' b)+(Fintype.card (Cell n):ℝ)*Δ₁ R q v m η C:=by
    unfold l' m' uT F t' Y' v''; have hu: κ/β + (χ+ν)/β ≤ q.linear*p.threshold^2/2:=by rw [← add_div,div_le_iff₀ d']; linarith only [hz]
    have ht:(χ+ν)/β≤ q.direct*p.threshold^2/2:=by rw [div_le_iff₀ d']; linarith only [hs]
    subst D; have he:= sum_le_sum (s:=univ) (g:=fun b=> Z.baseTerm q p U b+ Δ₁ R q v m η C) fun i _=> weak_line (b:=i) B hu ht hr f g h u uD l s t p'; simp_rw [sum_add_distrib,sum_const,nsmul_eq_mul,card_univ,counts_tax,counts_weak] at he; simpa only [Δ₁,mul_add] using he
 have hC:= mul_le_mul_of_nonneg_left (show (A.card:ℝ)≤ l'*R' from (by unfold R' l'; rw [d]; exact_mod_cast (broken_charge (U:=U) (r:=r) (t:=v')))) hx
 have ht:= mul_le_mul_of_nonneg_right hz (show 0 ≤ m' from Nat.cast_nonneg _); have hi:=mul_le_mul_of_nonneg_right hm (show 0≤l' from Nat.cast_nonneg _)
 obtain ⟨a,b⟩:=CF.Graph.oath B p U
 have hΔ: T ≥ β*(∑ x:Site n, -(PathData.atomSeries Z.cubic p U x + PathData.atomSeries Z.quartic p U x)) + ∑ x:Site n,-PathData.atomSeries Z.loop p U x:=by
    rw [sum_neg_distrib,sum_neg_distrib]; exact add_le_add (mul_le_mul_of_nonneg_left ((neg_le_neg (neg_le_of_abs_le a)).trans_eq (neg_neg _)) d'.le) ((neg_le_neg (neg_le_of_abs_le b)).trans_eq (neg_neg _))

 change -(Z.principal q p β U) + _ ≤ (-β*∑ b:Cell n,F b) + _
 unfold PathData.principal taxΔ;  change -(β*((∑ b:Cell n,Y' b)+_)+_)+(κ*m'+fuel*l') ≤ (-β * ∑ b:Cell n,F b) + ((T+β*(Fintype.card (Cell n):ℝ)*_ - _)- (χ+ν)*uT) -- regroup β*card*Δ
 rw [sum_neg_distrib,sum_neg_distrib] at hΔ; unfold v'' at hr; unfold R' at hC; have hF:=mul_le_mul_of_nonneg_left hr d'.le; unfold χ0 t' at hF; rw [mul_add,mul_add,mul_add] at hF;  rw [show β*(κ/β* m')=κ*m' by field_simp,show β*((χ+ν)/β*uT)=(χ+ν)*uT by field_simp] at hF; nlinarith only [hF,hC,hΔ,hi]

abbrev trip₂ (Z:PathData G)(q:Clip)(p:BudgetPoint) (A:Support c) (D:Finset (Cell n))(T:Forest r)(β κ fuel v':ℝ)(U:T.Slice G):ℝ:=if broken r v' (T.drape U)=A ∧ weak p.threshold (T.drape U)=D then goods Z q p β κ fuel v' (T.drape U) else 0
omit B in
lemma weak_test (v:ℝ):MeasurableSet {U:Config G n| weak v U=D}:=by
 simp only [Finset.ext_iff,Set.setOf_forall]; apply MeasurableSet.iInter; intro j; by_cases h:j∈D; · simp only [h,iff_true]; exact poll ..
 simp only [h,iff_false]; exact (poll ..).compl
lemma through_sharp (A:Support c)(D:Finset (Cell n)):Envelope (trip₂ Z q p A D T β κ fuel v'):=by
 let M:= T.drape (G:=G); have hm:Measurable M:= T.continuous_drape.measurable
 have he:= env_grow (n:=n) (p:=p) (β:=β) (κ:=κ) (v':=v') (fuel:=fuel) B; let f:=goods Z q p β κ fuel v' (n:=n); obtain ⟨C,hC⟩:=he.cost
 have hf:Envelope (fun x=> f (M x)):= ⟨he.meas.comp hm,C,fun i=>hC _⟩
 exact Envelope.piece (p:=fun x=> broken r v' (M x)=A ∧ weak p.threshold (M x)=D) (hm ((malaise_selector A r v').inter (weak_test _))) hf (Envelope.const 0)
#print axioms weak_grip
end Risa
end YM.Gleam.Luster
