import YM.SU5.FiniteGaugeData.Tower.Crescendo
import YM.SU5.FiniteGaugeData.Tower.Gauge
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
/-!
# Environment for cross-level pay: passing identities and inequalities
 at one observing level on this selection; discard no signs or denominators.
-/
open Fock
section supportMotion
variable (Z:Calibration)(P:ℕ)(S D:Finset Cover)
-- pre-padding clearance on coarse cover. Strict, and in gauge lattice units.
def separated (P:ℕ)(S T:Finset Cover):=∀ x∈S,∀y∈T,x-y∉Lattice.box P

lemma wrapped_far (h:separated P S D):∀ᶠ m: Side in atTop,∀ x∈ Satin.region S (Z.c m),∀ y∈ Satin.region D (Z.c m),P < separation x y:=by
 let R:= Satin.liner (S∪D) P
 filter_upwards [separates Z R] with n w x u y v
 obtain ⟨i,hx,rfl⟩:= mem_image.mp u; obtain ⟨j,hy,rfl⟩:=mem_image.mp v
 by_contra! t; rw [separation_comm] at t
 have hp:= YM.Work.E08.lift_mem_box t
 let p:= Lattice.lift (wrap (More (Z.c n)) i-wrap (More (Z.c n)) j)
 have hz(i:Cover)(v:i∈S∪D):i∈R:=liner_here (S∪D) P v
 have he:i=p+j:= w (hz _ (mem_union.mpr (Or.inl hx))) ((show p+j∈R from mem_biUnion.mpr ⟨j,mem_union.mpr (Or.inr hy),mem_image.mpr ⟨p,hp,rfl⟩⟩)) (by rw [map_add,show wrap _ p=_ from Lattice.wrap_lift _,sub_add_cancel])
 exact h i hx j hy (show i-j∈_ from (show p+j-j=i-j from congrArg (·-j) he.symm) ▸ (show p+j-j∈Lattice.box P from by rw [add_sub_cancel_right]; exact hp))

lemma reflected_coord (a:Axis)(z:ℤ)(x:Cover): (plane a z).motion x a=2*z-x a:=by
 rw [fling_move ..]; simp; ring
lemma region_sep {a:Axis}{z:ℤ}(x:region a z Z.ℓ S)(u:region a z Z.ℓ D): separated (2*(Advance.nearZero Z.D+Z.w)) (reflectedBox a z S) D:=by
 intro i h j hj k
 obtain ⟨t,ht,rfl⟩:= mem_image.mp h; have he:=x t ht; have hv:=u j hj
 have p:= (Lattice.box_test.mp k).1 a; rw [Pi.sub_apply,reflected_coord] at p
 have h:=Z.buffer; have ht:0<Z.R.L.val:=Z.R.L.property; unfold Margin r₃ r₁ at h; unfold Advance.nearZero at p
 push_cast at p; have hu:2*(16+8*Z.D+1+Z.w)<2*Z.ℓ:=by nlinarith
 omega
lemma wingspan_region (a:Axis)(z:ℤ)(h:region a z (tent Y H).ℓ S): region a (Λ.R.L.val*z) (tent Y H).ℓ (wingspan Λ l S):=by
 let p:= tent Y H
 have hu := margin_step (p.buffer) (p.R.coarse)
 intro x t; obtain ⟨i,v,b⟩:=mem_biUnion.mp t; obtain ⟨i,u,rfl⟩:=mem_image.mp v; obtain ⟨bV,v,rfl⟩:=mem_image.mp b
 have ht:= h i u; rw [Pi.add_apply,Pi.smul_apply,nsmul_eq_mul]
 have he:= (Lattice.box_test.mp v).1 a; push_cast at he; change (tent Y H).ℓ+Λ.R.L.val * Advance.gross (aliasLaw Λ) (distanceLaw l) Λ.R.J ≤ Λ.R.L.val * (tent Y H).ℓ at hu
 have hx : ((Λ.R.L.val:ℕ):ℤ)* (z+(p.ℓ:ℤ))≤ (Λ.R.L.val:ℤ) * i a:= mul_le_mul_of_nonneg_left ht (by positivity)
 have h': ((p.ℓ:ℕ):ℤ) + Λ.R.L.val * (Advance.gross (aliasLaw Λ) (distanceLaw l) Λ.R.J:ℕ) ≤ (Λ.R.L.val:ℤ) * p.ℓ:= by unfold p; exact_mod_cast hu
 change (Λ.R.L.val:ℤ)*z+(p.ℓ:ℤ) ≤ bV a + (Λ.R.L.val:ℤ)*i a
 rw [mul_add] at hx; linarith


end supportMotion
section operator
variable (n k₀ : ℕ→ℕ)(D:Cresc Y H n k₀)
variable (S:Finset Cover)
local notation "T" F:max=> destined Y H s n k₀ S D F
local notation "b" i:max F:max=> block Y H s (n i) (k₀ i) S F
local notation "W₀" => wingspan Λ l
local notation "Z₀"=>tent Y H

variable {F G:Family (tent Y H)}
include D
lemma ev_image (x:InTest K true S false F)(m: Side)(v:Fields ((K).c m)):
 Tendsto (fun i:ℕ=> (b i F) m v) atTop (𝓝 ((T F) m v)):=Metric.tendsto_nhds.mpr fun ε p=> ((integrates Y H s n k₀ S D F x _ (half_pos p)).mono fun y v0=>by rw [dist_eq_norm]; exact (v0 m v).trans_lt (by linarith))
/-- uniformly bounded operations on the entire S; may vary input with the
read. Thresholds on i. -/
lemma operator_paid: ∃ A:ℝ, 0<A ∧ ∀ᶠ i:ℕ in atTop, ∀ (F:Family (tent Y H)),InTest K true S false F →∀ y:ℝ, pay F y → pay (T F) (A*y) ∧ pay (b i F) (A*y):=by
 -- by output_deck fleet budget for a fixed stage OR on arbitrary spectrum.
 -- uniform Op cost on transfer for all i via unit input decomposition and
 -- treating ineligible corner zero.
 let J:=Σ r:ℕ,Purse S × Satin.Evens (W₀ S)
 -- just use cauchy/outfits to reduce to cost of one eligible point; there even easier finite env? prove via menu for whole Ω.
 let I₀:={j:J//admittedStage Y H s n k₀ S j.1∧∀ x:PairsC,‖j.2.1.val x‖ ≤ 1}
 have he(t:I₀): legalAt Y s (n t.val.1) (k₀ t.val.1):=t.property.1.1
 have ht(t:I₀): Tivoli (W₀ S) ((K).c (momentm Y (n t.val.1) (s+1))):=t.property.1.2
 have hs(v:Evens S):= (output_deck Y H s S _ _ he v ht (fun j=>j.val.2.1) zero_le_one (fun i=> i.property.2) (fun i=>i.val.2.2)).budget
 choose l L ll using hs
 let A₀:=∑ v:Evens S,l v * Fintype.card (Evens (W₀ S)); have ha:0≤A₀:=sum_nonneg (fun i _=> mul_nonneg (L i) (by positivity))
 let A:= A₀+1; have hA:0<A:=by unfold A; positivity
 have hr(i:ℕ)(F:Family (tent Y H))(x:InTest K true S false F)(f:pay F 1): pay (b i F) A:=by
    let J(v:Evens S):= (⟨banner S K F v,banner_paid S K F v⟩:Purse S); let H'(v:Evens S)(j:Purse S):= note K j.val (tagWord S v.val)
    have hu(v):InTest K true S false (H' v (J v)):=atoms_test Y H S v _
    have hv:F=∑ v:Evens S,H' v (J v):= banner_pays S K x
    have hw(v):pay (b i (H' v (J v))) (l v*Fintype.card (Evens (W₀ S))):=by
       rw [mul_comm]; refine banner_rate (W₀ S) K (booked ..) (fun j z=> ?_)
       have hz:∀ x, ‖(J v).val x‖≤1:=pay_banner S K x f v
       by_cases p:admittedStage Y H s n k₀ S i
       · let idx:I₀:= ⟨⟨i,J v,j⟩,p,hz⟩; exact ll v idx z
       unfold H'; rw [empty_gate Y H s n k₀ S v p (J v),banner_zero,Pi.zero_apply,norm_zero]; exact L v
    intro m v; nth_rw 1 [hv,sum_scheme Y H s (n i) (k₀ i) (S:=S) univ (fun j=>H' j (J j)) (fun i _=>hu _)] -- S implicit!
    simp_rw [Finset.sum_apply]; refine (norm_sum_le ..).trans ((sum_le_sum (fun j _=> hw j ..)).trans ?_); change A₀≤A; unfold A; linarith
 -- scale to any common y
 have hp(i:ℕ)(F:Family (tent Y H))(x:InTest K true S false F)(y:ℝ)(f:pay F y):pay (b i F) (A*y):=by
    rcases (pay_nonneg f).eq_or_lt with e | e
    · have hw:F=0:=by
         funext n x; exact norm_eq_zero.mp (le_antisymm ((f n x).trans e.ge) (norm_nonneg _))
      have he: (b i (0:Family K))=0:=by simpa only [zero_smul] using scale_scheme Y H s (n i) (k₀ i) (S:=S) InTest.one (0:ℂ)
      rw [hw,he,←e,mul_zero]; exact fun _ _=> norm_zero.le
    let c:ℂ:= (y:ℂ)⁻¹; have hc:‖c‖=y⁻¹:=by unfold c; rw [norm_inv,Complex.norm_real,Real.norm_of_nonneg e.le]
    have hC: pay (c • F) 1:= by rw [←inv_mul_cancel₀ e.ne', ←hc]; exact pay_scale f c
    intro t u; have h:=hr i _ (InTest.smul c x) hC t u
    simp only [scale_scheme Y H s (n i) (k₀ i) x c,Pi.smul_apply,norm_smul,hc,mul_comm y⁻¹,←div_eq_mul_inv] at h
    exact (div_le_iff₀ e).mp h
 exact ⟨A,hA,Eventually.of_forall (fun i F x y f=>⟨fun m u=> le_of_tendsto (ev_image Y H s n k₀ D S x m u).norm (Eventually.of_forall fun i=> hp i F x y f m u),hp i F x y f⟩)⟩

end operator
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.operator_paid
