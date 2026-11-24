import YM.SU5.Selected.Cor.Statics
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option maxRecDepth 3000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.Lantern
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest.Airy
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
namespace Bulb
set_option synthInstance.maxSize 24000
namespace Mezz
open Payroll Caste Silks Mint
local notation "ⅈ" => Complex.I
variable {N:Side}{T:Type}[Fintype T][DecidableEq T] (P:Mezz)(A:Society T)
local notation "S" => park N P.Broad
local notation "W" => park N P.Core
variable (i:P.Lot)(b:Bool)(k:Bool)(X Z:Coast→ Wq P.marks) (C:ℝ)
local notation "A'" => P.dart A N X
local notation "V'" => P.dart A N Z
local notation "ηc" b:max => hand b (cutM (Tset N))
local notation "↑X" => design (Ro N) (A') (lowerP C)
local notation "↑Z" => design (Ro N) (V') (Caste.upperP C)
namespace Caste
-- Assemble at W. visible & hidden. after gauge comparison uses blank.
noncomputable def accept (V:Pane N): P.Fish A N:= rosterG (Single N) (fun (i:P.Lot) (k:Bool)=> P.pole A i b k X Z C V)
local notation "Kₚ" b:max t:max => accept P A b X Z C t
lemma accept_low : Kₚ true 1= ↑X:= by apply uncoil _ _; intro i k; rw [accept,re_yoke,blank_poleX]; rfl
lemma accept_high : Kₚ false 1= (ηc false) * ↑Z:= by
 apply uncoil _ _; intro i k; rw [accept, re_yoke,blank_poleY]; unfold yoke; rw [Matrix.mul_assoc]; rfl
variable {ε γ:ℝ}{w:ℕ}{M:Tulip.Male}(c:Caste (N:=N) P M C ε w X Z)
include c
lemma take_hold (V:Pane N): Contained (modesIn N W) (Kₚ b V):= by apply sovereign; intro i k; rw [accept,re_yoke]; exact (talent _ _ _ _ _ _ _ _ c V |>.grows (modes_monotone (image_subset_image (P.yard_core _ _ c.value)))) -- syntax
lemma take_angle (V:Pane N): (ηc b)*(Kₚ b V)=(Kₚ b V):= by apply smallest; intro i k; rw [accept,re_yoke]; exact pole_x _ _ _ _ _ _ _ _ c _
lemma salary (f:1≤C)(u:0≤γ)(V:Pane N)(p:Rightful S V 1 γ) : ‖Kₚ b V - Kₚ b 1‖ ≤ ((2*Fintype.card P.Lot:ℕ):ℝ)*(sizeW C b*2*((8*P.beams*γ)* C)):= by
 have ht:0<C:=zero_lt_one.trans_le f; apply tallies; · unfold sizeW Caste.lowerP Caste.upperP tollS; cases b <;> simp <;> positivity
 intro i k; unfold yoke; rw [Matrix.sub_mul]; change ‖yoke (Kₚ b V) i k - yoke (Kₚ b 1) i k‖≤_; rw [accept,accept, re_yoke,re_yoke]; exact whipping _ _ _ _ _ _ _ _ c _ f u _ p

noncomputable def fillV (V:Pane N): P.Fish A N:= (↑Z) + (Kₚ false V-Kₚ false 1)
-- no X in $↑Z$? include via Kₚ → Yes
local notation "℧" V:max=> fillV P A X Z C V
lemma sera (V:Pane N): Contained (modesIn N W) (℧ V):= by
 unfold fillV; rw [sub_eq_add_neg,←neg_one_smul ℂ]; exact (spans_ro P A c _ (spans_H P A c) _).add ((take_hold P A false X Z C c V).add ((take_hold P A false X Z C c 1).smul _)) -- tune args
lemma reign (V:Pane N): ηc false * ℧ V = Kₚ false V:=by
 unfold fillV; rw [Matrix.mul_add,← accept_high, Matrix.mul_sub,take_angle P A false X Z C c V,take_angle P A false X Z C c 1]; abel
lemma fill_less (V:Pane N): ℧ V - ↑Z= Kₚ false V - Kₚ false 1 := by unfold fillV; abel

-- orientation. estimate payroll on these columns, before tinting. guard at every eligible input chosen. PP : Margin. ε at lower cost. Perturbed. increase n. $R_K$. Need get $  ≤ $t/δ. choose G threshold before. 
end Caste
noncomputable def billR (C:ℝ): ℝ:=10000*C^ (4:ℕ)
-- Norm merchandising. 0≤ε≤0.01 for morph. h= height.
def Lease (T:ℝ) (b v:ℝ):= v ≤ 1 ∧ T*b ≤ v -- placeholder
namespace Numeric
variable {C}
lemma bigV (f:1≤C):100 ≤ billR C:= by unfold billR; have h:1 ≤ C^(4:ℕ):= one_le_pow₀ f; linarith
lemma rentC_L (f:1≤C):2*C/(tollS C) ≤ 1/4:=by
 have p:0<C:= zero_lt_one.trans_le f; unfold tollS; field_simp; linarith
lemma rentC_H (f:1≤C): C*tollS C ≤ billR C/4:=by
 unfold tollS billR; nlinarith [show C^ (2:ℕ)≤ C^ (4:ℕ) from pow_le_pow_right₀ f (by decide), show 0≤C^4 from (by have f:0≤C:=(by linarith); positivity)]
lemma limitPole (f:1≤C)(b:Bool): sizeW C b*2*C ≤ billR C :=by
 have h:=bigV f; have c:0<C:=zero_lt_one.trans_le f; cases b; · change Caste.upperP C * _ *_ ≤_; unfold Caste.upperP; linarith [rentC_H f]
 change lowerP C * _ * _ ≤ _; unfold lowerP; have h:=rentC_L f; rw [div_eq_mul_inv] at h; linarith
local notation "Q" => Tender.levyH P.D (billR C)
local notation "ε₀" => Tender.tightH P.D (billR C)
local notation "R" => billR C
include P
lemma rankE (f:1≤C): 0<ε₀:= Tender.mugs (show 1 ≤ billR C from (by linarith [bigV f])) _ -- syntax
lemma lowE (f:1≤C): ε₀ ≤ 1/100:= by
 have h:=bigV f; have hR :1≤ R:= (by linarith); have hQ:= (Tender.mill hR P.D).1; have ht:= rankE P f; have e:0≤ Q:=by unfold Tender.levyH; have g:0< Tender.clouds P.D:= (Tender.cloudsK ..).1; have h:0<R:=zero_lt_one.trans_le hR; positivity
 nlinarith
lemma rank_toll (f:1≤C): (100*R)*ε₀ ≤ Q:= by
 have h:=bigV f; have ht:=rankE P f; unfold Tender.tightH at ht; have g:0 <R:= (by linarith); have vb :1≤R:=(by linarith); have hz:0≤Q:=by unfold Tender.levyH; have h:0≤Tender.clouds P.D:=(Tender.cloudsK ..).1.le; positivity
 unfold Tender.tightH; rw [←mul_div_assoc]; apply (div_le_iff₀ (by positivity)).mpr; rw [mul_comm]; apply mul_le_mul_of_nonneg_left _ hz; gcongr; exact (pow_one R).symm.trans_le (pow_le_pow_right₀ vb (by decide))
lemma seat_t (f:1≤C): tollS C≤ R:=by
 have h:= bigV f; have p:= rentC_H f; refine le_trans ?_ (le_trans p ?_); · have ht:0≤ tollS C:= (by unfold tollS; linarith); nlinarith
 linarith
end Numeric
end Mezz
end Bulb
end YM.CF.Pannier.Chancel.Lantern
open YM.CF.Pannier.Chancel.Lantern.Bulb.Mezz
#print axioms Caste.take_angle
#print axioms Caste.sera
#print axioms Numeric.lowE
