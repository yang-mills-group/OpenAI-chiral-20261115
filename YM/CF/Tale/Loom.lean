import YM.CF.Tale.Bye
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
set_option quotPrecheck false
namespace YM.CF.Tale
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Next Next.Free PhysicalNext.JointLoad Cube SU Exterior Cascade Bloch
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open Heir AnalyticBridge.SectorAffine.Offset AnalyticBridge.VerifiedReset
open Pressure Tube Siete
variable {c f:Side} 
open SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
variable {P: BudgetPoint} {n m:ℕ}
local notation "B"=> clinicFee
-- bind Theta decrement.C reset.O. x=threshold≤1. r≤1. b=ζ/ Ythreshold maybe h.BILL.
lemma hush_L (a C ε Γ L t w0 x:ℝ)(hC:1≤C)(hε:0 ≤ ε)(he:ε ≤ 1)(hx:0≤x)(hp:x ≤1)(hL:0 ≤ L)(vL:L≤1)(ht:0≤ t)(hG:0≤Γ)(hΓ:Γ≤1)(u:Γ^2≤x)(h:0≤w0)(hw0:w0≤ ε*x)(v:Real.exp (-a*t)≤ ε) : humpV a C Γ w0 x L t ≤ (40*C^2*ε)*x^2:=by
 unfold humpV; dsimp only; let d:=perkV a C Γ w0 x L t; have hT:0 ≤ C:=zero_le_one.trans hC; have hy:ε*x ≤ x:=mul_le_of_le_one_left hx he
 have he0:t=t:=rfl; have hm:0 ≤ d:=by unfold d perkV; positivity
 have hd:d≤3*C*ε*x:=by
    unfold d perkV; apply le_trans (add_le_add (add_le_add (le_trans (mul_le_of_le_one_right (mul_nonneg hT h) hΓ) (mul_le_mul_of_nonneg_left hw0 hT)) (mul_le_mul_of_nonneg_left hw0 hT)) (mul_le_mul_of_nonneg_left v (mul_nonneg (mul_nonneg hT hx) hL))); calc
       _ ≤ _ := add_le_add (le_refl _) (mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (mul_nonneg hT hx) vL) hε)
       _ ≤_:= le_of_eq (by ring) -- tune syntax
 have h₁:C*(Γ^2+w0) ≤ C*(x+x):=mul_le_mul_of_nonneg_left (add_le_add u (hw0.trans hy)) hT
 have h₂:2*(L*x)+d ≤5*C*x:=by
    have hp':(L*x)≤ x:=mul_le_of_le_one_left hx vL
    have he:3*C*ε*x≤ 3*C*x:=mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (by positivity) he) hx
    have hz:=hd.trans he; nlinarith only [hz, hp', hx, le_mul_of_one_le_left hx hC]
 change 2*(_+d*(2*(L*x)+d)) ≤ _
 refine le_trans (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul h₁ (mul_le_mul_of_nonneg_left hw0 hT) (mul_nonneg hT h) (mul_nonneg hT (add_nonneg hx hx))) (mul_le_mul hd h₂ (by positivity) (by positivity))) (by norm_num)) ?_; calc
    _ = (34*C^2*ε)*x^2:=by ring
    _ ≤ _:=by gcongr; norm_num
-- profiles variable η in τ range.P.
abbrev termQ(x:ℝ)(s:ℕ):ℝ:= temp x*(1+(Heir.reach x:ℝ))^s
variable (C A a K:ℝ)(hC:1≤C)(ha:0<a)(hA:0<A)(hk:1 ≤ K)(Y:Side)(k n:ℕ)
local notation "Ψ" x:max=> (termQ x n)
local notation "γ"=> B k C
local notation "μ" x:max=> (fiery SU.group x Y)
local notation "σ"=> (((Y.val:ℝ)⁻¹)^2)
local notation "η" x:max=> (γ*(Ψ x)^2)
local notation "η'" x:max=> ((η x)+(C+1*C)*(Ψ x))
variable{t:ℝ}(ht:0<t)
include ht hC ha hk hA
lemma grace_k : ∃ ε:ℝ,0<ε∧∀ᶠ x in atTop, Ψ x < t ∧ Ψ x ≤ 1 ∧ temp x ≤ Ψ x ∧ ε*μ x ≤ Ψ x∧ (η x)+ε*μ x ≤1 ∧ temp x ≤1 ∧ humpV a K (η' x) ((η x)+ε*(μ x)) (temp x) σ (radiusB x) ≤ A*(temp x)^2 :=by
 let O:=γ+2*C; have he :0≤γ:= (mul_nonneg zero_le_two (zero_le_one.trans hC)).trans (Heir.clinicFee_le k (zero_le_one.trans hC)) -- inspect lower bound
 have h:0<O:=by unfold O; positivity
 have hσ:0≤σ:=by positivity
 have vσ:σ ≤1:=pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr Y.property)) -- tune
 let ε:= min (1:ℝ) (A/(40*K^2)); have hu:0<ε:= lt_min one_pos (by positivity)
 let s:= ε/4; have hs:0<s:=by unfold s; positivity
 let ρ:=SU.group.slopeConstant* Real.log Y.val
 let G'(x:ℝ):= Real.exp (-a*x); have hx:∀ᶠ x:ℝ in atTop, Real.exp (-a*(radiusB x:ℝ)) ≤ ε:=by
    have hT:= Real.tendsto_exp_atBot.comp (((tendsto_natCast_atTop_atTop.comp Work.E01.radiusB_tendsto)).const_mul_atTop_of_neg (show -a<0 by linarith)) -- tune
    exact hT.eventually (ge_mem_nhds hu)
 refine ⟨s,hs,?_⟩
 filter_upwards [reachPays (K:=γ) (a:=0) hs (2*n),reachPays (K:=O^2) (a:=0) (show (0:ℝ)<1 by norm_num) (2*n),reachPays (K:=1) (a:=0) (lt_min ht zero_lt_one) n,Rebuild.geometry ρ,hx] with x hE hp hP hj xK -- tune m param
 have he₀:0 ≤ temp x:= Work.E04.temp_nonneg x; have hm:temp x ≤ Ψ x:= le_mul_of_one_le_right he₀ (one_le_pow₀ (by linarith [Nat.cast_nonneg (α:=ℝ) (Heir.reach x)])) -- base
 have ht':Ψ x< min t 1:=by unfold termQ; rw [mul_comm]; simpa using hP
 have hp':temp x ≤ 1:=(hm.trans (ht'.le.trans (min_le_right ..))); let R':=(η' x); have hy':Ψ x ≤ 1:=ht'.le.trans (min_le_right ..)
 have hz:0≤Ψ x:= he₀.trans hm; have hy1:η x ≤ s*temp x:=by
    refine le_trans ?_ (mul_le_mul_of_nonneg_right hE.le he₀); rw [add_zero]; unfold termQ; rw [mul_comm (2:ℕ), pow_mul]; apply le_of_eq; ring
 have hy:G'=G':=rfl; have hr: 0≤R':=by unfold R'; positivity
 have hh : R' ≤ O*Ψ x:=by unfold R' O; rw [add_mul (B k C)]; apply add_le_add (mul_le_mul_of_nonneg_left (show (Ψ x)^2≤ Ψ x from by nlinarith only [hy',mul_le_mul_of_nonneg_right hy' hz]) he); exact le_of_eq (by ring)
 have hQ:R'^2≤ temp x:=by
    refine le_trans (pow_le_pow_left₀ hr hh 2) (le_trans ?_ (le_trans (mul_le_mul_of_nonneg_right hp.le he₀) (show (1:ℝ)*temp x≤ _ by rw [one_mul]))) -- tune le_trans
    rw [add_zero, mul_comm (2:ℕ),pow_mul]; unfold termQ; exact le_of_eq (by ring)
 have hB :ε ≤1:=min_le_left ..; have he': μ x ≤2*temp x:= hj.2.1 -- tune Rebuild geom
 have ha':s*(μ x)≤ s*(2*temp x):=mul_le_mul_of_nonneg_left he' hs.le
 have hu':s*(2*temp x) ≤ ε*temp x:=by unfold s; nlinarith [mul_nonneg hu.le he₀]
 have hm:s* μ x ≤ Ψ x:=(ha'.trans hu').trans ((mul_le_of_le_one_left he₀ hB).trans hm)
 have ho: η x+s*(μ x)≤ ε*temp x:=by apply (add_le_add hy1 ha').trans; unfold s; nlinarith only [mul_nonneg hu.le he₀]
 have h1:0≤μ x:=Work.E04.temp_nonneg _
 refine ⟨ht'.trans_le (min_le_left ..),hy',by assumption,hm,ho.trans ((mul_le_of_le_one_left he₀ hB).trans hp'),hp',?_⟩
 refine (hush_L a K ε R' σ (radiusB x) ((η x)+s*(μ x)) (temp x) hk hu.le hB he₀ hp' hσ vσ (Nat.cast_nonneg _) hr (by nlinarith only [hQ,hp']) hQ (by positivity) ho xK).trans ?_
 exact mul_le_mul_of_nonneg_right (by rw [mul_comm]; exact (le_div_iff₀ (by positivity)).mp (min_le_right ..)) (sq_nonneg _)
end YM.CF.Tale
