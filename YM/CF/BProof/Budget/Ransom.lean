import YM.CF.BProof.Budget.Flash
/-! outside erase payouts. Need supply charge at ξ*y logs. no argument approximated. -/
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Risk
open Function RG Wilson Lattice Filter MeasureTheory SU Grid Angular Angular.Yard Finset Prox Mapping House Release hot Gauss Weights Pricing Micro Trek
open Gates Gates.Stage Gates.Stage.Setup Contour Contour.Season Contour.Battery Contour.Tower Cube Cabinet Pods Posts Skye Seam
open scoped Topology BigOperators Classical
local notation "G"=> SU.group
variable {c:Clip}{w R v:ℝ}{S:Gates.Stage c w R v}{L:Side}{a:ℕ}{y:ℝ}{d:ℕ}{N:Side}(Y:S.Setup L a (More N) d y)(P:Entice S L a d y)(T:PathData G)(θ:ℝ)(x:Pod Y)
local notation "mH"=> Y.yard
local notation "B"=> Y.Block
local notation "g₀"=> Y.g
local notation "wB"=>House.Season mH Y.c'
local notation "gE"=>Trek.tag mH
local notation "πX"=> Cabinet.roadB Y
local notation "rawK"=> rawG Y P T θ
local notation "K_"=> Y.hall
open Hero Mark
open Spin Dream Fock Dial -- fix
set_option maxHeartbeats 260000
local notation "Ζ_"=>framesL Y P T θ
local notation "CC"=>Y.yard.long
open Rhythm Tape Hearth Lat
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Hearth Tape Mark
attribute [local instance] opCStarAlgebra
variable {N₁ N₂:ℕ} {m m':Side}{j:ℕ} {a₁ b l r:ℝ}{D:Spin.Ready j a₁ b l r}{u:ℝ} (E:Essence D u)
variable {rₜ:ℕ} (Δ:Rhythm.Note E (Gates.gap L a) rₜ)(U: Orbit N → Pane N) (ν δ:ℝ)
variable {rB:ℕ}
variable {Y E T θ Δ U ν δ} (Z : School Y T θ E Δ U ν δ rB)
open Scope Moment Push.AbsoluteSums
local notation "μz"=> Z.μwage
variable (k ξ:ℕ) -- near depth, and size cutoff in F support
open Branch Tenant Air Veil Prime
variable {α C:ℝ}{I:Type}[Fintype I](K:Core j a₁ b l r N)
variable (Q:Primer N I α C)
local notation "Ψ"=> Pouch Y P T θ
local notation "ψx"=>Z.world1 P K
local notation "ψ0"=>Z.world0 P K
variable (x' : Pod Y)
open Account
open Payment Garden Palot Oasis Scree Shelter
variable (B' : GramM N)
variable (o:Y.Block) (xw x'w:Pouch Y P T θ)
local notation "φf"=> Brick.Act.fields mH g₀
variable (ε:ℂ)
abbrev winD(i:Site N)(x:Pod Y):ℂ:= ε⁻¹ * star (glow ((φf x).2 i))
def ransom (i: Site N)(x:Pod Y):ℂ:=Complex.log (winD (Y:=Y) ε i x)
abbrev eras (x:Pod Y):= School.rim_ (Y:=Y) k x
abbrev Member(o:Y.Block)(V:Pod Y):= (eras k V).filter (fun i=> addr mH g₀ (node i)=o)
lemma FeeZ(i:Site N): ‖winD ε i x‖=‖ε‖⁻¹:=by unfold winD; rw [norm_mul,norm_star,glow_p,mul_one,norm_inv]
lemma ransom_m(i:Site N):Measurable (ransom (Y:=Y) ε i):=by
 let f:=fun x:Pod Y=> glow ((φf x).2 i); have ht:Measurable f:= glow.continuous.measurable.comp ((measurable_pi_apply i).comp (measurable_snd.comp (Brick.Act.fields_m ..)))
 exact Complex.measurable_log.comp (measurable_const.mul (Complex.conjCLE.continuous.measurable.comp ht))
lemma pay_ef(i:Site N): (ransom ε i x).re= -(Real.log ‖ε‖):=by unfold ransom; rw [Complex.log_re, FeeZ, Real.log_inv] -- tune
abbrev settleF(i:Y.Block)(x:Pouch Y P T θ) := ∑ j∈ Member k i x.val, ransom ε j x.val
include Z
lemma billF_Y : Shelter.Ticket P (Near Y rB) (settleF (T:=T) (θ:=θ) P k ε) :=by
 constructor
 · intro i; exact Trek.meal ((Z.flagD_m P k).comp measurable_subtype_coe) (fun F (x:Pouch Y P T θ)=> ∑ j∈F.filter (fun j=>addr mH g₀ (node j)=i),ransom ε j x.val) (fun F=>Finset.measurable_sum _ fun j _=>(ransom_m (Y:=Y) ε j).comp measurable_subtype_coe)
 intro X x y π τ u b p; have hp:= approved Y x.val rB X Z.stageU.premium π (show b∈ Shelter.crown Y x.val rB X from p); unfold settleF; apply sum_congr; swap; · intro j t; have hx: addr mH g₀ (node j)= b:= (mem_filter.mp t).2; unfold ransom winD; rw [Brick.Act.phase_z mH g₀ j (hx.symm ▸ hp (ray_home ..)) u]
 ext i; unfold Member; rw [mem_filter,mem_filter]; refine and_congr_left (fun v=> ?_); unfold eras School.rim_; rw [erase_p,erase_p,Seam.nearhood,Seam.nearhood]; apply and_congr_right; intro t; rw [show πX (node i)=b from v]; exact Prime.close_near Y 6 _ _ u ((House.ray_in mH 32 (by decide : 6 ≤ 32)).trans hp)
lemma ticket_fee : (billF_Y P Z k ε).versionT.amt xw.val= ∑ i∈ eras k xw.val,ransom ε i xw.val := by
 rw [(billF_Y P Z k ε).issues xw.val (nearL Y xw.val) (crown_all Y xw.val rB Z.stageU.premium).symm (crown_unique Y xw.val rB Z.stageU.premium) xw.property]; exact sum_fiberwise_of_maps_to (fun i g=> Cabinet.nearer Y 6 hNear Subset.rfl (by decide) ((Seam.nearhood Y).1 ((erase_p ..).1 g).2)) _
variable (Ck:Clock Z k ξ)
omit Z in
lemma cap_F (p:2*k+1<Y.yard.long): (Member k o x).card≤ root_port Y.yard.short k Y.g.count.val:=by
 apply le_trans (b:=(Bias.CircleR g₀ mH o k).card); swap; exact Bias.circle_card g₀ mH o k p
 apply Finset.card_le_card_of_injOn node; intro i p; exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp p).2,_,((erase_p ..).1 (mem_filter.mp p).1).1⟩; exact Tenant.needle.injOn
variable (g:ε ≠ 0)
abbrev σF(D k L:ℕ) (v:ℝ) := fourBill hNear * (root_port D k L * |v|)
local notation "VΦ" => Real.log ‖ε‖
include Ck
lemma price_F : (billF_Y P Z k ε).versionT.Income (fun X x=> (Mint.grey Y rB X x).card * σF Y.yard.short k Y.g.count.val (Real.log ‖ε‖)) :=by
 let V:= (root_port Y.yard.short k Y.g.count.val:ℝ)* |VΦ|; have h(x:Pouch Y P T θ)(i:Y.Block) : (settleF P k ε i x).re≤ V:=by unfold settleF; rw [Complex.re_sum]; simp_rw [pay_ef,sum_const,nsmul_eq_mul]; apply le_trans (mul_le_mul_of_nonneg_left (neg_le_abs _) (Nat.cast_nonneg _)); exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (cap_F x.val k i (Ck.commuter Z k ξ k (by unfold TimePlus; omega)))) (abs_nonneg _)
 intro x i hx hp; apply le_trans ((billF_Y P Z k ε).version_income V (fun x _ _ i _=> h x i) x i hx hp); change (↑(Shelter.crown Y x rB i).card:ℝ)* V≤ (↑(fault Y rB x i).card:ℝ)*(fourBill hNear * V); rw [←mul_assoc _ _ V]; apply mul_le_mul_of_nonneg_right _ (by unfold V; positivity : 0 ≤ V); exact_mod_cast Cabinet.halo_size Y (A:=fault Y rB x i) hNear
omit Ck
include g
lemma cost_F : Complex.exp ((billF_Y P Z k ε).versionT.amt xw.val)= outPay ε (eras k xw.val) (φf xw.val).2:=by
 rw [ticket_fee P Z k xw ε,Complex.exp_sum]; unfold ransom; -- tune remove
 have hp(i: Site N):0 < ‖winD ε i xw.val‖:=by rw [FeeZ]; exact inv_pos.mpr (norm_pos_iff.mpr g)
 simp_rw [fun i=> Complex.exp_log (norm_pos_iff.mp (hp i))]; unfold winD; rw [Finset.prod_mul_distrib,prod_const]; unfold outPay style; rw [star_prod]
end YM.CF.BProof.Risk
