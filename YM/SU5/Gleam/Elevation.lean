/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.SU5.Gleam.Lacuna
import YM.CF.Graph.Dash
import YM.Next.RANK.Determinant
/-! # Tax (in a single orientation). -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.Gleam
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03
open scoped Matrix BigOperators Classical ContDiff Topology ENNReal Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ:ℝ}{U:Config G n}{A:Support c}{o x z:Site n}{f m:ℕ} {X Y:fieldDir G n 1} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}
variable (B:Z.Bounds q η C S)
lemma scan {n : Side}(t:ℝ)(c:Cell n):MeasurableSet {U:Config G n| c∈ misdemean t U}:=by
 simp only [misdemean,mem_filter,mem_univ,true_and]; exact (isOpen_lt continuous_const (G.continuous_chord.comp (show Continuous (fun U=> faceValue (K:=G.El) U c) from continuous_travel ..))).measurableSet
lemma malaise_selector (A:Support c)(r:Ratio c n)(v:ℝ): MeasurableSet {U:Config G n| broken r v U=A}:=by
 let Q(b:Finset (Cell n)):= halo 10 (b.image (fun i => r.parent i.1)); let R: Finset (Finset (Cell n)):= univ.filter (fun b=> Q b=A)
 let K (b:Finset (Cell n)):= { U:Config G n| misdemean v U=b}; rw [show {U:Config G n| broken r v U=A}=⋃ b∈R,K b from ?_]; swap
 · ext x; simp only [Set.mem_setOf_eq,Set.mem_iUnion,K]; constructor; · intro t; exact ⟨misdemean v x,mem_filter.mpr ⟨mem_univ _,t⟩, rfl⟩
   rintro ⟨b,h,rfl'⟩; change Q (misdemean v x)=A; rw [rfl']; exact (mem_filter.mp h).2
 refine MeasurableSet.biUnion R.countable_toSet fun i _=>?_; unfold K; simp only [Finset.ext_iff,Set.setOf_forall]; apply MeasurableSet.iInter; intro j; by_cases h:j∈i; · simp only [h,iff_true]; exact scan ..
 simp only [h,iff_false]; exact (scan ..).compl
lemma counts_tax (U:Config G n)(v t:ℝ): (∑ b:Cell n, if b∈misdemean v U then t else 0) = t*(misdemean v U).card := by rw [← sum_filter,filter_mem_eq_inter,univ_inter,sum_const,nsmul_eq_mul,mul_comm]
lemma conduct (n:Side)(v t:ℝ): Envelope (fun U:Config G n=> t*(misdemean v U).card):=by simp_rw [← counts_tax]; refine Envelope.sum univ (fun b U=> if b∈misdemean v U then t else 0) (fun i=> ?_); exact Envelope.piece (p:=fun U=> i∈misdemean v U) (scan ..) (Envelope.const _) (Envelope.const _)
lemma malaise_home {g:Site n→G.El}:misdemean v (Lattice.gauge g U)=misdemean v U:= by ext x; simp [misdemean,face_gauge]
abbrev richG (Z:PathData G)(q:Clip)(p:BudgetPoint) (β κ:ℝ)(U:Config G n):= Real.exp (-(Z.principal q p β U)+κ*(misdemean p.threshold U).card)
include B
lemma income_g : Envelope (richG Z q p β κ (n:=n)):= ((PathData.principal_env B p β).neg.add (conduct ..)).exp
lemma richG_inv : GaugeInvariant (richG Z q p β κ (n:=n)):=by
 intro k U -- adaptation from RANK determinant using actual Bonds
 have hA {m:ℕ} (f:ℕ→ RG.Atom G m)(H:∀ i,(f i).Invariant)(x:Site n) : PathData.atomSeries f p (gauge k U) x=PathData.atomSeries f p U x:=by
    apply tsum_congr; intro i; have ht : (f i).unmasked (gauge k U) x=(f i).unmasked U x:=by simp only [RG.Atom.unmasked,Work.F05.slot_gauge]; exact H i _ _
    simp [Atom.placed,masked,Set.indicator,Healthy,ht]
 have he(x:Lattice.Site n) : PathData.kept q p.threshold x (gauge k U) ↔ PathData.kept q p.threshold x U:=by simp [PathData.kept]
 have hB(i:Cell n) : Z.baseTerm q p (gauge k U) i= Z.baseTerm q p U i:=by simp only [PathData.baseTerm,face_gauge,G.chord_conj,Work.F05.ell_gauge B,G.norm_adjoint,he]
 unfold richG PathData.principal; simp only [hA Z.cubic (fun i=> (B.invariant i).2.1),hA Z.quartic (fun i=>(B.invariant i).2.2),hA Z.loop (fun i=>(B.invariant i).1),malaise_home]; simp only [hB]
 -- adjust
abbrev taxΔ (R:Rules G)(q:Clip)(n:Side)(p:BudgetPoint)(β v η C S:ℝ)(m:ℕ):= CF.Graph.taxY n β p.threshold C S + β*(Fintype.card (Cell n):ℝ)* Δ₁ R q v m η C
lemma enormous_f (d:A=broken r p.threshold U)(l:EnoughMark q p m)(d':0≤β)(f:ProbeBox X (2*v))(g:ProbeBox (X+Y) (2*v))(h:TrustLogs (X+Y) U r A v)(u:abandon X r A m)(s:0 ≤ v)(t:v≤ R.c)(p':0 ≤ C)(hx:0 ≤ ξ)(hz:κ+21^4*ξ ≤ β*(q.linear*p.threshold^2)) : richG Z q p β κ U ≤ Real.exp ((-β*∑ b:Cell n,rent Z q r A m b X Y) + (taxΔ R q n p β v η C S m - ξ*A.card)):=by
 let T:= CF.Graph.taxY n β p.threshold C S; let F(b:Cell n):=rent Z q r A m b X Y; let Y'(b:Cell n):= Z.baseTerm q p U b; let t':=q.linear*p.threshold^2; let m':ℝ:=(misdemean p.threshold U).card; let R':=(21:ℝ)^4
 apply Real.exp_monotone
 have hr:(∑ b:Cell n,F b)+t'*m'≤ (∑ b:Cell n,Y' b)+(Fintype.card (Cell n):ℝ)*Δ₁ R q v m η C:=by
    unfold m' F t' Y'; subst A; have he:= sum_le_sum (s:=univ) fun i _=> Δ_line (b:=i) B f g h u l s t p'; rw [sum_add_distrib,sum_add_distrib,sum_const,nsmul_eq_mul,card_univ,counts_tax] at he; exact he
 have hC:= mul_le_mul_of_nonneg_left (show (A.card:ℝ)≤ m'*R' from (by unfold R' m'; rw [d]; exact_mod_cast (broken_charge (U:=U) (r:=r) (t:=p.threshold)))) hx
 have ht:= mul_le_mul_of_nonneg_right hz (show 0 ≤ m' from Nat.cast_nonneg _)
 obtain ⟨a,b⟩:=CF.Graph.oath B p U
 have hΔ: T ≥ β*(∑ x:Site n, -(PathData.atomSeries Z.cubic p U x + PathData.atomSeries Z.quartic p U x)) + ∑ x:Site n,-PathData.atomSeries Z.loop p U x:=by
    rw [sum_neg_distrib,sum_neg_distrib]; exact add_le_add (mul_le_mul_of_nonneg_left ((neg_le_neg (neg_le_of_abs_le a)).trans_eq (neg_neg _)) d') ((neg_le_neg (neg_le_of_abs_le b)).trans_eq (neg_neg _))
 change -(Z.principal q p β U) + κ*m' ≤ (-β*∑ b:Cell n,F b) + _ -- binder scope * consumes `+`? sums Lean notation encloses plus!
 unfold PathData.principal taxΔ; change -(β*((∑ b:Cell n,Y' b)+_)+_)+ κ*m' ≤ (-β * ∑ b:Cell n,F b) + (T+_ -_)
 rw [sum_neg_distrib,sum_neg_distrib] at hΔ; unfold t' at hr; unfold R' at hC; linarith only [mul_le_mul_of_nonneg_left hr d', ht,hC,hΔ]
end YM.Gleam
#print axioms YM.Gleam.malaise_selector
#print axioms YM.Gleam.richG_inv
#print axioms YM.Gleam.enormous_f
