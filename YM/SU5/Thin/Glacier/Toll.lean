import YM.SU5.Thin.Glacier.Crest
import YM.SU5.Gleam.Elevation
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Gleam
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03
open scoped Matrix BigOperators Classical ContDiff Topology ENNReal Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ:ℝ}{U:Config G n}{A:Support c}{o x z:Site n}{f m:ℕ} {X Y:fieldDir G n 1} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}
variable (B:Z.Bounds q η C S)
variable (ht:ℝ) {d κA ψ:ℝ} {W:Finset (Cell n)}
local notation "χ" p:max=> p.threshold
abbrev stipd (d κA:ℝ)(W:Finset (Cell n))(x:ℝ)(U:Config G n):ℝ:= d*W.card+κA*(misdemean x U).card
abbrev heatG (Z:PathData G)(q:Clip)(p:BudgetPoint)(β d κA x:ℝ)(U:Config G n):= Real.exp (-(Z.principal q p β U)+stipd d κA (meek p U) x U)
include B
lemma heat_env: Envelope (heatG Z q p β d κA v (n:=n)):= ( ((PathData.principal_env B p β).neg).add ( (conduct (G:=G) n _ _).add (conduct n _ _))).exp
lemma heat_inv : GaugeInvariant (heatG Z q p β d κA v (n:=n)):= by
 have he:=richG_inv (β:=β) (p:=p) (κ:=0) (n:=n) B
 intro k H'; obtain h:= he k H'; unfold richG at h; simp only [zero_mul,add_zero] at h; unfold heatG; rw [Real.exp_add, Real.exp_add _ (stipd _ _ _ _ H'), h]; unfold stipd meek; simp_rw [malaise_home]
lemma crevice {τ:ℝ}(ht:χ p≤τ) (h₁:A=broken r τ U)(hz:W=meek p U)(l:EnoughMark q p m)(d':0≤β)(f:ProbeBox X (2*v))(g:ProbeBox (X+Y) (2*v))(h:TrustLogs (X+Y) U r A v)(u:noiseless X r A W m)(s:0 ≤ v)(t:v≤ R.c)(p':0 ≤ C)(hx:0 ≤ ξ)(t':d+ψ ≤ β * (leaff q * (χ p)^2))(hv:κA+ξ*21^4 ≤ β*(q.linear/2*(χ p)*τ)) : heatG Z q p β d κA τ U ≤ Real.exp ((-β*∑ b:Cell n,calf Z q r A m W b X Y) + (taxΔ R q n p β v η C S m - ξ*A.card - ψ*W.card)):=by
 let F(b:Cell n):=calf Z q r A m W b X Y; let Y'(b:Cell n):= Z.baseTerm q p U b; let T:=CF.Graph.taxY n β p.threshold C S; let k:= leaff q * (χ p)^2; let w:= q.linear/2*(χ p)*τ; let m':ℝ:=W.card; let R':=(21:ℝ)^4; let W':ℝ:=(misdemean τ U).card
 apply Real.exp_monotone; have hr:(∑ b:Cell n,F b)+(k*m'+w*W')≤ (∑ b:Cell n,Y' b)+(Fintype.card (Cell n):ℝ)*Δ₁ R q v m η C:=by
    unfold F m' W' k w Y'; subst W; have he:= sum_le_sum (s:=univ) fun i _=> Δ_lane (b:=i) B f g τ ht h u l s t p'; rw [sum_add_distrib,sum_add_distrib,sum_const,nsmul_eq_mul,card_univ] at he; unfold hire meek at he; rw [sum_add_distrib,counts_tax,counts_tax] at he; exact he
 have hC:= mul_le_mul_of_nonneg_left (show (A.card:ℝ)≤ W'*R' from (by unfold R' W'; rw [h₁]; exact_mod_cast (broken_charge (U:=U) (r:=r) (t:=τ)))) hx
 have ht:= mul_le_mul_of_nonneg_right t' (show 0≤ m' from Nat.cast_nonneg _) -- shadow ht
 have hw:= mul_le_mul_of_nonneg_right hv (show 0≤W' from Nat.cast_nonneg _)
 obtain ⟨a,b⟩:=CF.Graph.oath B p U
 have hΔ: T ≥ β*(∑ x:Site n, -(PathData.atomSeries Z.cubic p U x + PathData.atomSeries Z.quartic p U x)) + ∑ x:Site n,-PathData.atomSeries Z.loop p U x:=by
    rw [sum_neg_distrib,sum_neg_distrib]; exact add_le_add (mul_le_mul_of_nonneg_left ((neg_le_neg (neg_le_of_abs_le a)).trans_eq (neg_neg _)) d') ((neg_le_neg (neg_le_of_abs_le b)).trans_eq (neg_neg _))
 change -(Z.principal q p β U)+ (d*(meek p U).card+κA*W') ≤ (-β * ∑ b:Cell n,F b) + _
 rw [←hz]; unfold PathData.principal taxΔ; change -(β*((∑ b:Cell n,Y' b)+_)+_)+(d*m'+κA*W')≤ (-β * ∑ b:Cell n,F b) + (T+_ -_ -_)
 rw [sum_neg_distrib,sum_neg_distrib] at hΔ; change _≤β*k*m' at ht; change _ ≤ β*w*W' at hw; unfold R' at hC; linarith only [mul_le_mul_of_nonneg_left hr d',ht,hw,hC,hΔ]

end YM.Gleam