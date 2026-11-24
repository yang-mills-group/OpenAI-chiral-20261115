import SatinThinIncense
import YM.SU5.Regis.Ranging
/-! # lower attempt statistic with non-connected stencil: anchor positions of MOVING spots (can be arbitrarily far apart). Keep small-defect qualifications for all of them, not a bin.
Use the full-range comparison result (6). -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option quotPrecheck false
set_option maxRecDepth 4000
set_option synthInstance.maxSize 30000
set_option maxHeartbeats 480000
noncomputable section
namespace YM.Regis.Head
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Gleam Matrix ProbabilityTheory
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius NNReal
variable {c n : Side}{r:Ratio c n}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ:ℝ}{U:Config G n}{A:Support c}{o x z:Site n}{f m:ℕ} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L_:Floor H q n δ w)
namespace Garland
open Etch
variable {I J:Type*} [Fintype I][Fintype J] {Q:ℝ} (z:PlaqAxes→ℝ) {Υ:MvPolynomial I ℝ}
-- Touring records ALL pose displacements on gauge sites (not yet requiring center nodes). Support checked later.
structure Tour (I:Type*)(n:Side) where
 loc : I → Site n
 orient : I → Signed
-- two cases via root at zero and labelled ticket. move processes both. 
variable (T:Tour I n) (C':Etch G J) (ρ:ℝ)
def Tour.moves (s:Signed)(b:Site n):Tour I n:=⟨fun i=>affine s b (T.loc i),fun i=>s*T.orient i⟩
lemma Tour.rules (s u:Signed)(b c:Site n): (T.moves s b).moves u c=T.moves (u*s) (affine u c b):=by
 cases T; unfold moves; congr 1; · ext i; simp [affine,Signed.act_mul]; try ring
 simp [mul_assoc]
/-- off fleet as above. -/
def Tour.exhibit (t:ℝ)(U:Config G n):ℝ:= ∏ i:I, garland z ρ t (T.orient i) (T.loc i) U
def Tour.reading (W:Altar G n) := ∏ i:I, C'.chalk q ρ (T.orient i) (T.loc i) W
-- orientation
lemma Tour.moves_here (t:ℝ)(u:Signed)(b:Site n): T.exhibit z ρ t (pull u b U)=(T.moves u b).exhibit z ρ t U:=by unfold exhibit garland; simp_rw [pull_pull]; rfl
-- on stamen, chalk pull law holds. Check `chalk_now` by showing appropriate investment identical by bank u b composition. bank(u3 u1) equals bank u1 ∘ bank u3. prove via represent uniqueness of linear increment? simpler diag proof via slot derivative on configuration and chalk equation x. use slot_deriv projected composition via bank_at
lemma clockwise (C':Etch G J)(s u:Signed)(b c:Site n) (w: Regis.Head.Dir G n) : C'.chalk q ρ s b (tiler B P (bank u c w))= C'.chalk q ρ (u*s) (affine u c b) (tiler B P w):=by
 rw [C'.chalk_now q ρ s b B P, C'.chalk_now ..]; unfold sketch; apply congrArg C'.f; funext i; simp_rw [river_now q B P]; apply congrArg (ρ • ·)
 let S:=C'.slot i; let g:= slot_deriv S 0 (bank s b (bank u c w)); -- arg
 apply HasDerivAt.unique _ (slot_deriv S 0 (bank (u*s) (affine u c b) w)); apply HasDerivAt.congr_of_eventuallyEq g; refine Eventually.of_forall (fun x=> ?_); dsimp only; simp_rw [bank_at,pull_pull]
lemma Tour.reads_here (s:Signed)(b: Site n)(w:Regis.Head.Dir G n) : T.reading C' ρ (q:=q) (tiler B P (bank s b w))=(T.moves s b).reading C' ρ (q:=q) (tiler B P w):=prod_congr rfl fun i _=> clockwise B P ρ C' _ s _ b w -- q inference issue clock args order inspect
-- accounting; numerical product lemma
lemma products_margin {A E:J→ℝ}{M:ℝ}(N:Finset J)(h:∀ i, |A i|≤M)(g:∀ i, |E i|≤M)(t:1≤M): |(∏ i∈N,A i)-∏ i∈N,E i|≤ M^N.card*(∑ i∈N, |A i-E i|):=by
 induction N using Finset.induction_on with
 | empty=>simp
 | insert i s v ih=>
   let X:=∏ i∈s,A i; let W:=∏ i∈s,E i; let U:=∑ i∈s,|A i-E i|; have he:0≤M:=zero_le_one.trans t; have hp:|W|≤ M^s.card:=by unfold W; rw [Finset.abs_prod]; exact (Finset.prod_le_prod (fun i _=>abs_nonneg _) (fun i _=>g i)).trans_eq (by simp) -- tune
   rw [prod_insert v,prod_insert v,sum_insert v,card_insert_of_notMem v,pow_succ']; change |A i*X-E i*W|≤ _*_ *(_ + U); rw [show A i*X-E i*W=A i*(X-W)+(A i-E i)*W from (by ring)]; refine (abs_add_le ..).trans ((add_le_add ((abs_mul ..).le.trans (mul_le_mul (h i) ih (abs_nonneg (X-W)) he)) ((abs_mul ..).le.trans (mul_le_mul_of_nonneg_left hp (abs_nonneg _)))).trans (?_)); change M*(M^s.card*U)+ |A i-E i| * M^s.card≤ M*M^s.card*(_+U); nlinarith only [mul_le_mul_of_nonneg_left t (show 0≤ |A i-E i| * M^s.card from by positivity)]
lemma Tour.exhibit_cost : |T.exhibit z ρ p.threshold U|≤ (costG z p.threshold ρ)^Fintype.card I:=by unfold exhibit; rw [Finset.abs_prod]; exact (prod_le_prod (fun _ _=>abs_nonneg _) (fun i _=>costG_le ..)).trans_eq (by rw [prod_const,card_univ]);
lemma Tour.reading_cost (W:Altar G n) : |T.reading C' ρ (q:=q) W|≤ C'.arc^Fintype.card I:=by unfold reading; rw [Finset.abs_prod]; exact (prod_le_prod (fun _ _=> abs_nonneg _) (fun i _=> C'.chalk_bound q ρ _ _)).trans_eq (by rw [prod_const,card_univ]);
lemma Tour.env_figure : Envelope (T.exhibit z ρ p.threshold (G:=G)):=by
 refine ⟨?_,(costG z p.threshold ρ)^Fintype.card I,fun i=>?_⟩; · exact (Finset.measurable_fun_prod _ fun i _=> (costG_env z (P:=p) _ _).meas)
 rw [Real.norm_eq_abs]; exact T.exhibit_cost z ρ
lemma Tour.invariant : GaugeInvariant (T.exhibit z ρ t (G:=G)):= fun _ _=> Finset.prod_congr rfl fun _ _=> garland_gauge z ..
lemma Tour.smooth_read : ContDiff ℝ 1 (T.reading C' (q:=q) ρ):= contDiff_prod fun _ _=> C'.chalk_smooth ..
-- derivative bill not by summing OO(J), need Hessian estimates from Caller projection. Orientation lookup on all i, separate root sets per occurrence.
variable {L:Type*} [Fintype L] (Φ:L→ Tour I n)
abbrev interest (Λ: L→ Tour I n) (a:I) : L→Site n:=fun i=>(Λ i).loc a
def Stationed (Λ:L→Tour I n) : Prop:=∀ i,Injective (interest Λ i)
def panorama (t:ℝ)(U:Config G n):ℝ:=∑ i, (Φ i).exhibit z ρ t U
def accountGl(W:Altar G n) := ∑ i, (Φ i).reading C' (q:=q) ρ W
lemma grandEnv : Envelope (panorama z ρ Φ p.threshold (G:=G)):=by unfold panorama; exact Envelope.sum univ (fun i=> _) (fun i=> (Φ i).env_figure z ρ) -- tune namespace
lemma grandInvariant: GaugeInvariant (panorama z ρ Φ t (G:=G)):=fun a U=>sum_congr rfl fun i _=> (Φ i).invariant z ρ a U
lemma beacon_priced (W:Altar G n): |accountGl C' ρ Φ (q:=q) W| ≤ Fintype.card L*C'.arc^Fintype.card I:=by unfold accountGl; refine (abs_sum_le_sum_abs ..).trans ((sum_le_sum (fun i _=> (Φ i).reading_cost C' ρ (q:=q) W)).trans_eq ?_); simp
lemma account_beads (s:Signed)(b:Site n)(U: Config G n): panorama z ρ Φ t (pull s b U)=panorama z ρ (fun i=>(Φ i).moves s b) t U:= sum_congr rfl fun i _=> (Φ i).moves_here (z:=z) (ρ:=ρ) .. -- check
lemma Stationed.pulled (h:Stationed Φ)(s:Signed)(b:Site n) : Stationed (fun i=>(Φ i).moves s b):=fun j=> (Push.Local.turnSites s b).injective.comp (h j)
end Garland
end YM.Regis.Head
#print axioms YM.Regis.Head.Garland.clockwise
#print axioms YM.Regis.Head.Garland.Tour.env_figure
#print axioms YM.Regis.Head.Garland.grandEnv
