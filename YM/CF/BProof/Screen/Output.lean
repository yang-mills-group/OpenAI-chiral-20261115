import YM.CF.BProof.Screen.Hit
import YM.CF.BProof.Gates.Mcost
/- schism. cost material level. Exponents ready for y calculation. -/
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
namespace Output
local notation "λ*"=> output_ -- fix
-- HL meant Tag; derive from Traj. Use Meas Ward on full Orbit; support estimate by Height h. offset preserved.
open Tulip
structure Warp : Prop where
 covariant :∀ x g, denZ d₀ F U (Girt.gird g x)= effectK (tradew N_ g).val (denZ d₀ F U x)
 measurable_ : Envelope (denZ d₀ F U)
abbrev mA_ := wealth yv A Pz+(Cargo.roomAge d₀.p.B (o'+o')+4*Cg)
abbrev mC_ := Charge.mCost d₀.funds R (2*y) (Weights.rent y S.M R w v) (DP L a y)
abbrev mD_ := Setup.piT (DP L a y) y
include vb P in
lemma beta_pos : 0 ≤ d₀.beta:= by have ht:=P.dull.threshY; linarith
-- ensure P included
variable (HP:Warp F (d₀:=d₀) (U:=U)) -- tune order
include HP vb ub ht Vb
local notation "Aθ"=> wealth yv A Pz+(Cargo.roomAge d₀.p.B (o'+o')+4*Cg)
local notation "Cs"=> Charge.mCost d₀.funds R (2*y) (Weights.rent y S.M R w v) (DP L a y)
local notation "Cd"=> Setup.piT (DP L a y) y
lemma outputs : Payment.Lifted d₀ F U QF Aθ Cs Cd w R v:=by
 let θt:= Z.lineT; have hv:= θt.raw; have hu:= θt.ok; have hz:0 ≤ d₀.beta:= beta_pos P vb
 refine ⟨?_,hv,hz, HP.measurable_,fun g x=> HP.covariant x g⟩
 have hf: ∃ ρ:ℝ,0≤ρ∧ Moment.Toll (QF).M.floor (QF).M.price ρ Aθ:=by
    let ψ:=4*z; have p: 0≤ψ:= by unfold ψ; have h:= ht.pos; positivity
    refine ⟨0,le_rfl, Manus.rent HK Tm Vb 0 (p.trans ht.weight) (p.trans ht.H) (p.trans ht.E) (div_nonneg Vb.norm.le (by norm_num))⟩
 refine ⟨Z.ft,Z.warmZ P, P.dull.seen,P.dull.smallXi,hf, fun i U=> ?_, fun i=> ?_,fun i=>?_,fun i g x=>?_,fun i U v=> ?_⟩
 · exact Setup.outlay_fee P Y Lθ U i d₀.beta hv d₀.p p₀ hz ub
 · exact Charge.outlay_m mH i d₀.funds d₀.p d₀.path _ d₀.beta hv B0 -- tune
 · exact Charge.outlay_read mH i d₀.funds d₀.p d₀.path _ d₀.beta hv (Setup.permits P d₀.p p₀) ((by norm_num : 1 ≤ (2:ℕ)).trans P.after) B0
 · exact Charge.outlay_g mH i d₀.funds d₀.p d₀.path _ d₀.beta _ hv B0 g -- tuning
 exact Setup.shell_fee P Y U i v
omit HP vb ub ht Vb
local notation "Lv"=> (More I_).val
local notation "Lᴮ"=> ((More I_).val:ℝ)^4
local notation "KΦ"=> Capital P Z k ξ K F HK ht
abbrev β_bound : ℝ:= skyLog S.P y d₀.funds R Y.yard.short (S.M y)
lemma block_small(Y:S.Setup L a (More (mid m₁ B₁)) d y): Fintype.card (House.Block Y.yard Y.c') ≤(More (mid m₁ B₁)).val^4:=by
 apply le_trans (Fintype.card_le_of_surjective (bT Y) (fun i=> ⟨_, Cabinet.cart_eq Y i⟩)); exact Pricing.width Y.yard
include ht in
lemma capital_bound : -(wealth yv A Pz)*(((More I_).val:ℝ)^4) ≤ (KΦ).re:=by
 let Κω:= wealth yv A Pz; let L:=((More I_).val:ℝ)^4; have h:‖Capital P Z k ξ K F HK ht‖≤ L*Κω:=by -- K shadow K core!
   apply (Primer.buy P Z k ξ K PR_ ht.pos).trans_eq; change _ * _ = L*Κω; congr 1; unfold L; have hm(s:Side): Fintype.card (Site s)=s.val^4:= (by simp [Site,Four,Axis,Per,ZMod.card]); change (Fintype.card (Site (More I_)):ℝ)=_; rw [hm]; push_cast; rfl -- tuning
 linarith only [abs_le.mp ((Complex.abs_re_le_norm _).trans h)|>.1] -- tune |-💔
include ub vb
lemma incomeT : - (β_bound (S:=S) (Y:=Y)) * Lᴮ≤ output_ :=by
 refine le_trans (b:=-(skyLog S.P y d₀.funds R Y.yard.short (S.M y)* Lᴮ))  ?_ ?_; swap; · exact (abs_le.mp (Pricing.ceiling S.P _ Lθ _ _ _ (Setup.soil P Y) (Gates.Stage.Setup.room P Y) Z.lineT.raw Z.lineT.ok _ _ ub (beta_pos P vb) d₀.p.threshold_le)).1 -- tune wide
 exact le_of_eq (by rw [neg_mul])
abbrev amount_:= -(2+skyLog S.P y d₀.funds R Y.yard.short (S.M y)+ wealth yv A Pz)
include ψ -- tune
variable (wa':θ=d₀.beta*g y^2){vχ jχ:ℝ}(hQ:G'.Buy vχ jχ Y.g.count.val Y.yard.short y)(h₂:feeχ 4 rB ≤ vχ)
include Ck W te Vcost vr vh HP ht Vb k1 u' vε Hw wa' hQ h₂ v₀ τ'
lemma original : Real.exp (-(2+skyLog S.P y d₀.funds R Y.yard.short (S.M y)+wealth yv A Pz)* Lᴮ)≤ ‖numerator d₀ F U (QF).test‖:=by
 let Q':=(outputs P Z k K F HK ht Gm Tm Vb p₀ vb ub HP)
 obtain ⟨t⟩:= investment P Z k ξ K Ck F HK ht Gm Tm Vb ε p₀ G' W vb ub k1 u' vε _ Hw -- order vb ub
 have h:= Ωdiner P Z k ξ K Ck F HK ht Gm Tm Vb ε p₀ A₀ v₀ G' W vb ub te τ' Vcost vr vh vε Q' ψ t wa' hQ h₂ -- ensure U included
 refine le_trans (Real.exp_monotone ?_) h; have hp:= incomeT P Z k K F HK Gm Tm p₀ vb ub; have hv:= capital_bound P Z k ξ K F HK ht; unfold β_bound at hp; have ht: (Fintype.card Y.Block:ℝ)≤ ((More I_).val:ℝ)^4 := by exact_mod_cast block_small Y
 linarith only [hp,hv,ht]
end Output
end YM.CF.BProof.Scene
