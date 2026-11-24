import YM.CF.BProof.Screen.Ball
set_option quotPrecheck false
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Scene
open Function RG Wilson Lattice Filter MeasureTheory SU Grid Angular Angular.Yard Finset Prox Mapping House Release hot Gauss Weights Pricing Micro Trek
open Gates Gates.Stage Gates.Stage.Setup Contour Contour.Season Contour.Battery Contour.Tower Cube Cabinet Pods Posts Skye Scree Jet Vault Paige Drapes Pec Seam
open scoped Topology BigOperators Classical
local notation "G"=> SU.group
variable {N:Side}{L₁ B₁ m₁:Side} {d₀:GramM (mid m₁ B₁)} {w R v:ℝ}{S:Gates.Stage d₀.funds w R v}{L:Side}{a:ℕ}{y:ℝ}{d:ℕ}(Y:S.Setup L a (More (mid m₁ B₁)) d y)(P:Entice S L a d y)(θ:ℝ)(x:Pod Y)
local notation "mH"=> Y.yard
local notation "B"=> Y.Block
local notation "g₀"=> Y.g
local notation "wB"=>House.Season mH Y.c'
local notation "gE"=>Trek.tag mH
local notation "πX"=> Cabinet.roadB Y
local notation "rawK"=> rawG Y P d₀.path θ
local notation "K_"=> Y.hall
open Hero Mark
open Spin Dream Fock Dial -- fix
set_option maxHeartbeats 260000
local notation "Ζ_"=>framesL Y P d₀.path θ
local notation "CC"=>Y.yard.long
open Rhythm Tape Hearth Lat
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Hearth Tape Mark
attribute [local instance] opCStarAlgebra
variable {N₁ N₂:ℕ} {m m':Side}{j:ℕ} {a₁ b l r:ℝ}{D:Spin.Ready j a₁ b l r}{u:ℝ} (E:Essence D u)
variable {rₜ:ℕ} (Δ:Rhythm.Note E (Gates.gap L a) rₜ)(U: Loom (mid m₁ B₁)) (ν δ:ℝ)
variable {rB:ℕ}
variable {Y E θ Δ U ν δ} (Z : School Y d₀.path θ E Δ U ν δ rB)
open Prime Scope Moment Push.AbsoluteSums
local notation "μz"=> Z.μwage
variable (k ξ:ℕ) -- near depth, and size cutoff in F support
open Branch Tenant Air Veil
open Prime Prime.Estate
open Palot Anthem Payment Oasis Stint TraceD
variable (K: Core j a₁ b l r (mid m₁ B₁)) (Ck:Clock Z k ξ){p:Odd L₁.val}{X: Pricing j L₁ p (Vault.Thread j)}(F:Grasp X B₁ δ)
variable {yv:Pay}{y₀ α A z Al Pz:ℝ}
variable (HK:Hinge F (Z.age P K) Δ.stage.c rateH Δ.stage.η yv d₀.J.I y₀ α A Al Pz)
local notation "I_"=> mid m₁ B₁
local notation "Code_"=> Hinge.Codes I_
variable (ht: Trust yv α Al z)
local notation "N_"=>mid m₁ B₁
local notation "Kℓ"=> Δ.stage.c
local notation "PR_"=> trueQ P Z K F d₀.J.I HK ht
local notation "Lθ"=>d₀.path
variable {v_:Pay}{wa βj a_g Cg h' o' ε':ℝ}(Gm:Oasis.Marks (Z.age P K) v_ Δ.stage.c rateH Δ.stage.η) {X':Cargo d₀ h' o'}(Tm:Pantry Gm X' ε')(Vb:Oasis.Tube d₀ v_ h' ε' o' a_g Cg)(ε:ℂ)(xw:Pouch Y P d₀.path θ)
-- fixed height Auth etc outsourced Lifted
local notation "οx"=> (F_' Y P d₀.path θ xw.val)
local notation "ψΘ"=> Z.pose P K
local notation "φΘ"=> Z.world1 P K
local notation "ΗΘ"=>Z.lineT.raw
variable (p₀:d₀.p.threshold=thresh y)(A₀:Spire.Pearl F)(v₀:u≤ A₀.q)
local notation "B0"=> fog_ P Z p₀ -- K and Et? 
local notation "QF"=> scoreP P Z k K F HK Gm Tm p₀
local notation "κcut"=> cutH P Z k K F HK Gm Tm p₀
open Garden Risk Account Cabinet Mint Pour
local notation "GΞ"=> Θ_ P Z k ξ K Ck F HK ht ε p₀ -- tune eta order
variable {ρ:ℝ}(G' :Mint.Mode)(W:Primer.Guard P Z k ξ K (trueQ P Z K F d₀.J.I HK ht) ρ G'.bias)
variable (vb: y≤2*d₀.beta)(ub:d₀.beta≤2*y)(te:ε≠0)
local notation "τυ"=> Τu P Z k ξ K F HK ht Gm Tm ε p₀
/-! Apply B-contour after Arts.paid at actual y/torus. -/
variable (τ':Fund₀ d₀ K A₀)(Vcost: PHfee 0 Y.yard.short k ξ Y.g.count.val (wealth yv A Pz) (Real.log ‖ε‖)≤G'.cost)(vr:0≤G'.burn)(vh:G'.burn≤ Pricing.bill_c d₀.funds Y.yard.short S.κ y d₀.beta)
variable {εg:ℝ}(k1: Good Z z εg) (u':3*εg≤a_g/4) (vε:‖ε‖≤ε') (Hw: quo (Y:=Y) k ξ (εg:=εg) (Cg:=Cg) (o':=o') (ρ:=ρ) (z:=z) (yv:=yv) (A:=A) (Pz:=Pz) ≤ 1/8)
variable {mA mC mD:ℝ} (HL:Payment.Lifted d₀ F U (scoreP P Z k K F HK Gm Tm p₀) mA mC mD w R v)
local notation "κ_"=> Capital P Z k ξ K F HK ht
local notation "output_"=> Payment.output d₀ QF (S.M y) θ S.P (Setup.soil P Y)
variable (ψ:Brick.Solid y Y.yard.short Y.g.count.val)
section
-- Pick exact fields.
local notation "Xi_"=> Xi (Y:=Y)
variable (t:Ball (θ:=θ) (rB:=rB) P (Xi (Y:=Y)) (Τu P Z k ξ K F HK ht Gm Tm ε p₀) (1/8))
abbrev θpick : Pod Y → ℂ:= (GΞ).exponential.pickM t
local notation "L_"=> θpick P Z k ξ K Ck F HK ht Gm Tm ε p₀ t
include te
lemma exercise : Complex.exp κ_ * L_ xw.val= poleF P Z k K F HK Gm Tm ε xw p₀:=by
 rw [waltz_cost P Z k ξ K Ck F HK ht Gm Tm ε xw p₀ te]; unfold θpick; rw [Shift.choose_hit _ _ _ xw.property, Shift.resp_exp]; unfold Scope.Total; rw [dif_pos xw.property]; simp only [Complex.exp_add]; ring
include W Vcost vb vr vh
abbrev sound_t := (GΞ).Income (Mint.settle Y rB G') -- remove
lemma τcash: (GΞ).exponential.Cap (Mint.settle Y rB G'):= (GΞ).includeA (allowance P Z k ξ K Ck F HK ht ε p₀ G' W vb Vcost vr vh) -- order te? allowance vCost includes
variable (waT:θ=d₀.beta*g y^2)
include τ' HL waT vε Vb v₀
lemma attains : numerator d₀ F U (QF).test = Complex.exp (output_)* Complex.exp κ_ * ∫ x, Brick.adapt mH g₀ L_ x ∂globe mH y:=by
 let W_: Shift Y P d₀.path θ rB:= (GΞ).exponential; let e:=Complex.exp κ_; let X:= L_; let f(p):=e*X p; have hv:Envelope X:= W_.pick_env t G' (τcash P Z k ξ K Ck F HK ht ε p₀ G' W vb te Vcost vr vh) -- order te
 have hut:∀ y: Payment.Sphere mH,Brick.adapt mH g₀ f y=e*(Brick.adapt mH g₀ X y):=by intro y; unfold Brick.adapt; split; rfl; rw [mul_zero]
 let SΦ:= Setup.soil P Y; let Meter:= Setup.pulse P Y
 have gS:hot.Book S.K S.P mH S.κ SΦ:=Pricing.Model.bought _ _ _ _ _ _ _ _ Meter -- tune
 have pc:= Scene.ticket P Z k K F HK Gm Tm Vb ε p₀ A₀ v₀ τ' Ck.carries te vε f ⟨measurable_const.mul hv.meas, ‖e‖*hv.cost.choose,fun i=> (norm_mul ..).trans_le (mul_le_mul_of_nonneg_left (hv.cost.choose_spec i) (norm_nonneg e))⟩ (fun i p=>show f i=0 by unfold f X θpick Shift.pickM; rw [if_neg p,mul_zero]) (fun i=> exercise P Z k ξ K Ck F HK ht Gm Tm ε i p₀ te t) -- μ
 rw [Payment.guest d₀ U QF (S.M y) HL θ S.κ S.K S.P SΦ _ (room P Y) Z.lineT.ok gS waT pc]; -- tune position
 simp_rw [hut]; rw [integral_const_mul, mul_assoc]; -- check score.y y
 rfl
-- no u' in attains? drop. 
variable (Cβ:ℝ)
lemma bodyCm:(∫ x,Brick.adapt mH g₀ L_ x ∂globe mH y)=(kilo _ (Brick.lawTotal mH g₀ y) (Brick.baseC mH g₀ y)).toReal • Battery.stock (P:=Brick.prep mH g₀ y ψ) L_:=by -- namespace kilo
 let X:=L_; have hv:Envelope X:= (GΞ).exponential.pick_env t G' (τcash P Z k ξ K Ck F HK ht ε p₀ G' W vb te Vcost vr vh)
 rw [Brick.valueF mH g₀ y ψ _ (Brick.adapt_m mH g₀ _ hv) (fun _ h=> if_neg h)]; rw [show Brick.adapt mH g₀ X ∘ Brick.flats mH g₀=X from funext (Brick.beneath mH g₀ L_)] -- tune wildcard
variable {vχ jχ:ℝ}(hQ:G'.Buy vχ jχ Y.g.count.val Y.yard.short y)(h₂:feeχ 4 rB ≤ vχ)
-- full recovery to exp.
local notation "Φ*"=> numerator d₀ F U (QF).test
local notation "B'"=>Fintype.card Y.Block
abbrev τBound(s:Side) := (s.val:ℝ)^4
local notation "qΦ"=> skyLog S.P y d₀.funds R Y.yard.short (S.M y)
include ψ hQ h₂ ub t Ck
lemma Ωdiner : Real.exp (-(Fintype.card (House.Block Y.yard Y.c'):ℝ)- ↑(Fintype.card (House.Block Y.yard Y.c'))+ output_+(Capital P Z k ξ K F HK ht).re) ≤ ‖Φ*‖:=by
 let z₁:= Payment.output d₀ QF (S.M y) θ S.P (Setup.soil P Y); let q:= Real.exp (-(Fintype.card (House.Block Y.yard Y.c'):ℝ)); let hL:= (GΞ).exponential; let L:= L_
 have Hy: q ≤ ‖Battery.stock (P:=Brick.prep mH g₀ y ψ) L‖:= hL.equity t G' (τcash P Z k ξ K Ck F HK ht ε p₀ G' W vb te Vcost vr vh) Z.lineT.raw Z.lineT.ok hQ Z.stageU.premium h₂ ψ -- tune k order
 rw [attains P Z k ξ K Ck F HK ht Gm Tm Vb ε p₀ A₀ v₀ G' W vb te τ' Vcost vr vh vε HL t waT]; rw [bodyCm P Z k ξ K Ck F HK ht Gm Tm Vb ε p₀ A₀ v₀ G' W vb te τ' Vcost vr vh vε HL ψ t waT]; -- assume order
 simp_rw [norm_mul,Complex.norm_exp,Complex.ofReal_re,norm_smul,Real.norm_of_nonneg (ENNReal.toReal_nonneg)]; let u:=Real.exp output_* Real.exp (κ_).re -- notation issue; rewrite
 simp_rw [sub_eq_add_neg,Real.exp_add]; apply le_trans (b:= u*(q*q)) (by unfold u q; apply le_of_eq; ring); exact mul_le_mul_of_nonneg_left (mul_le_mul (Brick.value_bill mH g₀ y ψ) Hy (by positivity) (ENNReal.toReal_nonneg)) (by unfold u; positivity)
end
end YM.CF.BProof.Scene
