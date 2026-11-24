import SatinThinAngstrom
/-!
# LP.17 renewal. This time price EVERY satellite, still on elected threshold.

Trick: omit from the Gaussian crop near any chosen positive fraction of the *actual* threshold,
without changing the latter, the Metric, layout or funds. New classification makes the cost
payable **even with far_bill's existing both flake allowances**. Analogue of `scar_line` and
`at_shelf` (compare also Thin/Luster/Cub (half-cut)). Gives a shorter route to the LP17 moment.
G and WA.12 consuming that hereafter on this trajectory need not bound a Gaussian cap-tail
separately in LP. Can also preserve the leading Mark exponential cost for WA.
-/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option quotPrecheck false
noncomputable section
namespace YM.Gleam.Wake
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03
open scoped Matrix BigOperators Classical ContDiff Topology ENNReal Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ:ℝ}{U:Config G n}{A:Support c}{o x z:Site n}{f m:ℕ} {X Y:fieldDir G n 1} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}
variable (B:Z.Bounds q η C S)

variable {α αcost ε:ℝ}
abbrev unitDueN(q:Clip)(α:ℝ):ℝ:= q.linear*α^2/4
abbrev nearRich(Z:PathData G)(q:Clip)(p:BudgetPoint)(β κ ξ ε αcost α:ℝ)(U:Config G n):ℝ:= twice_rich Z q p β κ ξ ε U * Real.exp (αcost*(misdemean α U).card)

lemma mis_of_le(h:α≤ε):misdemean ε U ⊆ misdemean α U := fun i p=> (mem_filter.mpr ⟨mem_univ _,lt_of_le_of_lt h ((mem_filter.mp p).2)⟩)
lemma core_mono {k:ℕ}{L M :Support n}(h:L⊆ M) (p:withinCore r A M k x) : withinCore r A L k x := by
 refine ⟨p.1,fun hh =>p.2 ?_⟩; obtain ⟨y,h0,h1⟩:= halo_spec.mp hh; exact halo_spec.mpr ⟨y,h h0,h1⟩
-- all tests simultaneously at each face
lemma advent (u:0≤α)(v:α≤p.threshold)(t:p.threshold≤ε): (if b∈ misdemean α U then unitDueN q α else 0) + ((if b∈ misdemean p.threshold U then unitDueS q p/2 else 0) + (if b∈ misdemean ε U then unitDueL q p ε else 0)) ≤ Z.baseTerm q p U b:=by
  let H:= misdemean p.threshold U; let E:= misdemean ε U; let N:=misdemean α U
  have hp:= p.threshold_pos; have hq:= q.tail_pos
  by_cases z:b∈H
  · have hz:b∈misdemean α U:=mis_of_le v z; apply le_trans _ (mane t); change (if _ then _ else _)+((if b∈H then _ else _)+_) ≤(if b∈H then _ else _)+_; rw [if_pos hz,if_pos z,if_pos z,← add_assoc]; apply add_le_add_left
    unfold unitDueN unitDueS; nlinarith only [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ u v 2) hq.le]
  have ht:b∉misdemean p.threshold U:=z; have hs:b∉misdemean ε U:=fun y =>z (mis_of_le t y)
  rw [if_neg ht, if_neg hs,zero_add,add_zero]
  split
  next he =>
    let d:= G.chord (faceValue U b); have h: d≤p.threshold:= le_of_not_gt (fun p=> z (mem_filter.mpr ⟨mem_univ _,p⟩)); have hh:α<d:=(mem_filter.mp he).2
    unfold PathData.baseTerm; refine (le_add_of_nonneg_right ?_).trans' ?_
    · split; positivity; exact le_rfl
    rw [PathData.clipped,if_pos h]; unfold unitDueN; have hD:q.linear ≤ 2*q.direct:=by linarith only [q.kink,q.quadratic_pos]
    change _ ≤ q.direct*d^2/2; nlinarith only [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ u hh.le 2) hq.le,mul_le_mul_of_nonneg_right hD (sq_nonneg d)]
  next he=>
    have hA:= mane (U:=U) (b:=b) (q:=q) (Z:=Z) t; simpa [ht,hs] using hA

include B
lemma near_line (u:0≤α)(w':α≤p.threshold)(hε:p.threshold≤ε)(f:ProbeBox X (2*v))(g:ProbeBox (X+Y) (2*v))(h:TrustLogs (X+Y) U r (broken r ε U) v) (w:blank X r (broken r ε U) (face_anchors (misdemean α U)) m) (l:EnoughMark q p m)(p':0 ≤ v)(t':v≤ R.c)(hv:0 ≤ C) : arrear Z q r (broken r ε U) (face_anchors (misdemean α U)) m b X Y + ((if b∈ misdemean α U then unitDueN q α else 0)+((if b∈misdemean p.threshold U then unitDueS q p/2 else 0)+(if b∈misdemean ε U then unitDueL q p ε else 0))) ≤ Z.baseTerm q p U b + Δ₁ R q v m η C:=by
 let e:= acry R v m η C; let A:=broken r ε U; let E:= misdemean p.threshold U; let Y0:= misdemean α U
 unfold arrear; split
 next hg =>
    have he: face_anchors E ⊆ face_anchors Y0 := image_subset_image (mis_of_le w')
    have h := scar_line (b:=b) B hε f g h (fun b h=> core_mono he (w b h)) l p' t' hv
    have hh:b∉ Y0:=fun y=> hg.2 (halo_spec.mpr ⟨b.1, mem_image_of_mem Prod.fst y,by simp⟩)
    unfold arrear at h; rw [if_pos (show withinMark r (broken r ε U) (face_anchors (misdemean p.threshold U)) m b from core_mono he hg)] at h
    rw [if_neg (show b∉ misdemean α U from hh),zero_add,if_neg (show b∉misdemean p.threshold U from fun y=>hh (mis_of_le w' y))]; rwa [if_neg (show b∉misdemean p.threshold U from fun y=>hh (mis_of_le w' y))] at h
 next hl=>
    rw [add_comm, research]; obtain ⟨hu,he⟩:= fallout B f w hl (by positivity)
    apply add_le_add (advent u w' hε)
    have h0 :0 ≤ faceCutError R v:=by unfold faceCutError; have hp:=R.positive; have _p:=G.colorScale_pos; positivity
    have he':0 ≤ acry R v m η C:= acry_zero hv p'
    have hu':0 ≤ q.direct:=q.quadratic_pos.le
    rw [hu,norm_zero,zero_pow (by decide : (2:ℕ)≠0),mul_zero,zero_div,zero_add,Δ₁]; apply le_trans (div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) he (2:ℕ)) (by norm_num)) (le_add_of_nonneg_left ?_)
    positivity

variable {u y:ℝ}{Λ:Finset (Cell n)}
theorem near_shelf (h0:0≤α)(ha:α≤p.threshold)(t:ε≥p.threshold)(d:A=broken r ε U)(dd:Λ=misdemean α U)(l:EnoughMark q p m)(d':0≤β)(f:ProbeBox X (2*v))(g:ProbeBox (X+Y) (2*v))(h:TrustLogs (X+Y) U r A v)(p':blank X r A (face_anchors Λ) m)(s:0 ≤ v)(t':v≤ R.c)(hv:0 ≤ C)(hx:0 ≤ y)(hz:κ ≤ β*unitDueS q p/2)(ht:αcost+u ≤ β*unitDueN q α)(hx':ξ+21^4*y ≤ β*unitDueL q p ε) : nearRich Z q p β κ ξ ε αcost α U ≤ Real.exp ((-β*∑ b:Cell n,arrear Z q r A (face_anchors Λ) m b X Y) + (taxΔ R q n p β v η C S m - u*Λ.card - y*A.card)):=by
 let T:= CF.Graph.taxY n β p.threshold C S; let F(b:Cell n):= arrear Z q r A (face_anchors Λ) m b X Y; let Y'(b:Cell n):= Z.baseTerm q p U b; let ts:=unitDueS q p; let tv:=unitDueL q p ε; let N:=unitDueN q α; let ms:ℝ:=(misdemean p.threshold U).card; let m':ℝ:=Λ.card; let mL:ℝ:=(misdemean ε U).card; let R':=(21:ℝ)^4
 unfold nearRich twice_rich; rw [←Real.exp_add]
 apply Real.exp_monotone
 have hr:(∑ b:Cell n,F b)+ (N*m'+(ts/2*ms+tv*mL))≤ (∑ b:Cell n,Y' b)+(Fintype.card (Cell n):ℝ)*Δ₁ R q v m η C:=by
    unfold m' ms mL F ts tv Y' N; subst A Λ; have he:= sum_le_sum (s:=univ) fun i _=> near_line (b:=i) B h0 ha t f g h p' l s t' hv; simp only [sum_add_distrib,sum_const,nsmul_eq_mul,card_univ,counts_tax] at he; simpa only [Δ₁,mul_add] using he
 have hC:= mul_le_mul_of_nonneg_left (show (A.card:ℝ)≤ mL*R' from (by unfold R' mL; rw [d]; exact_mod_cast (broken_charge (U:=U) (r:=r) (t:=ε)))) hx
 have hy:= mul_le_mul_of_nonneg_right hz (show 0 ≤ ms from Nat.cast_nonneg _)
 have hN:= mul_le_mul_of_nonneg_right ht (show 0 ≤ m' from Nat.cast_nonneg _)
 have ht':= mul_le_mul_of_nonneg_right hx' (show 0 ≤ mL from Nat.cast_nonneg _)
 obtain ⟨a,b⟩:=CF.Graph.oath B p U
 have hΔ: T ≥ β*(∑ x:Site n, -(PathData.atomSeries Z.cubic p U x + PathData.atomSeries Z.quartic p U x)) + ∑ x:Site n,-PathData.atomSeries Z.loop p U x:=by
    rw [sum_neg_distrib,sum_neg_distrib]; exact add_le_add (mul_le_mul_of_nonneg_left ((neg_le_neg (neg_le_of_abs_le a)).trans_eq (neg_neg _)) d') ((neg_le_neg (neg_le_of_abs_le b)).trans_eq (neg_neg _))
 rw [←dd]; change -(Z.principal q p β U) + κ*ms+ ξ*mL+αcost*m' ≤ (-β*∑ b:Cell n,F b) + _
 unfold PathData.principal taxΔ; change -(β*((∑ b:Cell n,Y' b)+_)+_)+ κ*ms+ξ*mL+αcost*m' ≤ (-β * ∑ b:Cell n,F b) + (T+_ -_ -_)
 rw [sum_neg_distrib,sum_neg_distrib] at hΔ; unfold ts tv N at hr; unfold R' at hC; linarith only [mul_le_mul_of_nonneg_left hr d', hy,hN,ht',hC,hΔ]
lemma near_burs : Envelope (nearRich Z q p β κ ξ ε αcost α (n:=n)):= (income_burs B).mul ((conduct ..).exp)
lemma near_gauge : GaugeInvariant (nearRich Z q p β κ ξ ε αcost α (n:=n)):= by intro k U; unfold nearRich; rw [twice_gauge B k,malaise_home]
end YM.Gleam.Wake
