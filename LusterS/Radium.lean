import LusterS.Gates
import Refrain.Shrift
import Refrain.Kernel
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
-- reserves split for labels
variable {χ fuel :ℝ}
abbrev goods (Z:PathData G)(q:Clip)(p:BudgetPoint) (β κ fuel v':ℝ)(U:Config G n):ℝ:= Real.exp (-(Z.principal q p β U)+(κ*(misdemean p.threshold U).card+fuel*(misdemean v' U).card))
include B
lemma prism_e (hD:D=misdemean p.threshold U)(d:A=broken r v' U)(hr:p.threshold≤v')(l:EnoughMark q p m)(d':0≤β)(f:ProbeBox X (2*v))(g:ProbeBox (X+Y) (2*v))(h:TrustLogs (X+Y) U r A v)(u:abandon X r A m)(uD:vacuumR X D (hallBill m))(s:0≤v)(t:v≤ R.c)(p':0 ≤ C)(hx:0 ≤ ξ)(hz:κ+(χ+ν) ≤ β*(q.linear*p.threshold^2/2))(hm:fuel+21^4*ξ ≤ β*(q.linear*p.threshold*v'/2)): goods Z q p β κ fuel v' U ≤ Real.exp ((-β*∑ b:Cell n,flash Z q r D A m b X Y) + ((taxΔ R q n p β v η C S m - ξ*A.card)-(χ+ν)*D.card)):=by
 let T:= CF.Graph.taxY n β p.threshold C S; let F(b:Cell n):=flash Z q r D A m b X Y; let Y'(b:Cell n):= Z.baseTerm q p U b; let t':=q.linear*p.threshold^2/2; let v'':=q.linear*p.threshold*v'/2; let m':ℝ:=D.card; let l':ℝ:=(misdemean v' U).card; let R':=(21:ℝ)^4
 apply Real.exp_monotone
 have hr:(∑ b:Cell n,F b)+(t'*m'+v''*l')≤ (∑ b:Cell n,Y' b)+(Fintype.card (Cell n):ℝ)*Δ₁ R q v m η C:=by
    unfold l' m' F t' Y' v''; subst D; have he:= sum_le_sum (s:=univ) (g:=fun b=> Z.baseTerm q p U b+ Δ₁ R q v m η C) fun i _=> sparse_line (b:=i) B hr f g h u uD l s t p'; simp_rw [sum_add_distrib,sum_const,nsmul_eq_mul,card_univ,counts_tax] at he; simpa only [Δ₁,mul_add] using he
 have hC:= mul_le_mul_of_nonneg_left (show (A.card:ℝ)≤ l'*R' from (by unfold R' l'; rw [d]; exact_mod_cast (broken_charge (U:=U) (r:=r) (t:=v')))) hx
 have ht:= mul_le_mul_of_nonneg_right hz (show 0 ≤ m' from Nat.cast_nonneg _); have hi:=mul_le_mul_of_nonneg_right hm (show 0≤l' from Nat.cast_nonneg _)
 obtain ⟨a,b⟩:=CF.Graph.oath B p U
 have hΔ: T ≥ β*(∑ x:Site n, -(PathData.atomSeries Z.cubic p U x + PathData.atomSeries Z.quartic p U x)) + ∑ x:Site n,-PathData.atomSeries Z.loop p U x:=by
    rw [sum_neg_distrib,sum_neg_distrib]; exact add_le_add (mul_le_mul_of_nonneg_left ((neg_le_neg (neg_le_of_abs_le a)).trans_eq (neg_neg _)) d') ((neg_le_neg (neg_le_of_abs_le b)).trans_eq (neg_neg _))
 have hmu:(misdemean p.threshold U).card=D.card:= hD ▸ rfl
 change -(Z.principal q p β U) + _ ≤ (-β*∑ b:Cell n,F b) + _
 unfold PathData.principal taxΔ; rw [hmu]; change -(β*((∑ b:Cell n,Y' b)+_)+_)+(κ*m'+fuel*l') ≤ (-β * ∑ b:Cell n,F b) + ((T+β*(Fintype.card (Cell n):ℝ)*_ - _)- (χ+ν)* m') -- regroup β*card*Δ
 rw [sum_neg_distrib,sum_neg_distrib] at hΔ; unfold t' v'' at hr; unfold R' at hC; nlinarith only [mul_le_mul_of_nonneg_left hr d', ht,hC,hΔ, hi]
abbrev trip (Z:PathData G)(q:Clip)(p:BudgetPoint) (A:Support c) (D:Finset (Cell n))(T:Forest r)(β κ fuel v':ℝ)(U:T.Slice G):ℝ:=if broken r v' (T.drape U)=A ∧ misdemean p.threshold (T.drape U)=D then goods Z q p β κ fuel v' (T.drape U) else 0
lemma env_grow : Envelope (goods Z q p β κ fuel v' (n:=n)):= ((PathData.principal_env B p β).neg.add ((conduct ..).add (conduct ..))).exp
lemma goods_invariant :GaugeInvariant (goods Z q p β κ fuel v' (n:=n)):=by
 intro i U; let v:=κ*(misdemean p.threshold U).card; let A:=richG Z q p β κ (n:=n)
 have he (W:Config G n) : goods Z q p β κ fuel v' W= A W*Real.exp (fuel*(misdemean v' W).card):=by rw [←Real.exp_add]; unfold goods; congr 1; ring
 rw [he (gauge i U),he U,malaise_home,show A (gauge i U)=A U from richG_inv B i U]
omit B in
lemma misdemeanor_test (v:ℝ):MeasurableSet {U:Config G n| misdemean v U=D}:=by
 simp only [Finset.ext_iff,Set.setOf_forall]; apply MeasurableSet.iInter; intro j; by_cases h:j∈D; · simp only [h,iff_true]; exact scan ..
 simp only [h,iff_false]; exact (scan ..).compl
lemma through_t (A:Support c)(D:Finset (Cell n)):Envelope (trip Z q p A D T β κ fuel v'):=by
 let M:= T.drape (G:=G); have hm:Measurable M:= T.continuous_drape.measurable
 have he:= env_grow (n:=n) (p:=p) (β:=β) (κ:=κ) (v':=v') (fuel:=fuel) B; let f:=goods Z q p β κ fuel v' (n:=n); obtain ⟨C,hC⟩:=he.cost
 have hf:Envelope (fun x=> f (M x)):= ⟨he.meas.comp hm,C,fun i=>hC _⟩
 exact Envelope.piece (p:=fun x=> broken r v' (M x)=A ∧misdemean p.threshold (M x)=D) (hm ((malaise_selector A r v').inter (misdemeanor_test _))) hf (Envelope.const 0)
end YM.Gleam.Luster
