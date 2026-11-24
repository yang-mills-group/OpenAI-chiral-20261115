import YM.CF.BProof.Screen.Energy
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
section
variable {I V :Type}[Fintype I][MeasurableSpace V][Fintype V] -- skip
end
-- Weak budget certificate. Recipes heights and ξ. Keep gap const. Use distinct rates for gas AP tail vs tick tr vs gauge but cost≥4. tags extendible via contour.Client.
variable {εg:ℝ}
def BFA(B' l k:ℕ) (ζ ζ':ℝ) := Scope.total B' k l ζ*ζ'
abbrev qο(B' n l k:ℕ)(o Cg εg:ℝ):= (Cargo.roomAge n (o+o)+4*Cg)*Scope.total B' k l εg+(2*(4*Cg))*Scope.total B' k l εg
abbrev ζϝ(B' n k ξ l:ℕ)(ρ z o Cg Cw:ℝ) := Primer.WgR (ρ*(Primer.price_short B' k ξ l Cw)) +(Primer.expL z ξ*Cw)*Scope.total B' k l z -- n,o,Cg unused
abbrev AU₁(δ:ℝ→ℕ)(v K:ℝ→ℝ)(i:ℝ):=v i
abbrev Jζ := Scope.ac Y 1 Z.μwage
-- schedule (μ power reinforces covenant)
local notation "DΨ" => Pouch Y P d₀.path θ
structure Good (Z:School Y d₀.path θ E Δ U ν δ rB)(z εg:ℝ): Prop where
 price_w : Mapping.Factor Y.g.count.val (House.up 8) (Scope.ac Y 1 Z.μwage) z 4
 price_g : Mapping.Factor Y.g.count.val (House.up 8) (Scope.ac Y 1 Z.μwage) εg 4
variable (k1: Good Z z εg) (u':3*εg≤a_g/4) (vε:‖ε‖≤ε')
def quo : ℝ:= Pour.fŴ Y+(qο Y.yard.short d₀.p.B Y.g.count.val k o' Cg εg + ζϝ Y.yard.short d₀.p.B k ξ Y.g.count.val ρ z o' Cg (wealth yv A Pz))
-- availability P→ Teller
abbrev Ball(I:Type)[Fintype I] (v: Pouch Y P Lθ θ→ℂ)(u:ℝ):= Account.Teller (gridBase wB) (Cabinet.Ready P Y Lθ θ) (Esp Y rB) I (Scope.Total Y P Lθ θ v) 4 u
lemma bound_frame {I:Type}[Fintype I]{C D:ℝ}{F:Pod Y→ℂ}{U:Pouch Y P Lθ θ→ℂ} (v: Teller (gridBase wB) (Cabinet.Ready P Y Lθ θ) (Esp Y rB) I F 4 C)(p:∀ (x:Pouch Y P Lθ θ), F x.val=U x)(h:C≤D): Nonempty (Ball (Y:=Y) (θ:=θ)  (rB:=rB) P I U D):=by
 refine ⟨{v with pay:= v.pay.weaken _ _ le_rfl h,values:= fun x a=>?_}⟩; exact (dif_pos a).trans ((p ⟨x,a⟩).symm.trans (v.values x a))
abbrev bT₀(N:Side):= Veil.KeyP N⊕ Palot.Y (More N)
abbrev KT(N:Side)(B':Type):= B' ⊕ Veil.Hinge.Codes N
abbrev Xi := Layer mH⊕ (bT₀ I_⊕KT I_ Y.Block)
include u' k1 vε Vb Ck
local notation "LΦ"=>House.Block Y.yard Y.c'
lemma stock_a : Nonempty (Ball (θ:=θ)  (rB:=rB) P (bT₀ I_) (τfee P Z k K F HK Gm Tm ε p₀) (qο Y.yard.short d₀.p.B Y.g.count.val k o' Cg εg)) := by
 have h:= Air.thaw P Z K k Ck.pos (Ck.height Z k ξ) v_ Gm X' Vb Tm εg u'; have d:= Air.sunset P Z K k (Ck.height Z k ξ) v_ Gm X' Vb ε vε p₀.ge εg u' -- tune args f.elem
 have u:2*k+1<Y.yard.long:=Ck.commuter Z k ξ k (by unfold TimePlus; omega)
 obtain ⟨A⟩:= titan Y P Lθ θ Z.μwage rB _ εg h k1.price_g u; obtain ⟨B'⟩:= titan Y P Lθ θ Z.μwage rB _ εg d k1.price_g u; refine bound_frame P (A.add B') (fun x=>?_ ) le_rfl
 unfold τfee; change Scope.Total Y P Lθ θ _ x.val+Scope.Total Y P Lθ θ _ x.val=_; unfold Scope.Total; rw [dif_pos x.property,dif_pos x.property]; rw [cautiously]; -- tune
omit u' Vb vε
include W
lemma stock_b : Nonempty (Ball (θ:=θ) (rB:=rB) P (KT I_ LΦ) (φfee P Z k ξ K F HK ht) (ζϝ Y.yard.short d₀.p.B k ξ Y.g.count.val ρ z o' Cg (wealth yv A Pz))) :=by
 obtain ⟨A⟩:= Primer.revenue P Z k ξ K PR_ Ck W
 obtain ⟨B'⟩:= titan Y P Lθ θ Z.μwage rB _ z (Primer.chain P Z k ξ K PR_ ht.pos Ck) k1.price_w (Ck.commuter Z k ξ k (by unfold TimePlus; omega)); -- tune
 refine bound_frame P (A.add B') (fun x=> ?_) le_rfl; unfold φfee; change Scope.Total Y P Lθ θ _ x.val+Scope.Total Y P Lθ θ _ x.val=_; unfold Scope.Total; rw [dif_pos x.property,dif_pos x.property]
include u' Vb vε vb ub p₀
lemma investment(Ω:ℝ)(w: quo (Y:=Y) k ξ (εg:=εg) (Cg:=Cg) (o':=o') (ρ:=ρ) (z:=z) (yv:=yv) (A:=A) (Pz:=Pz) ≤ Ω): Nonempty (Ball (θ:=θ)  (rB:=rB) P (Xi (Y:=Y)) τυ Ω):=by
 obtain ⟨V'⟩:= Pour.weak Y P _ θ rB Z.lineT.ok Z.lineT.raw d₀.p p₀ d₀.beta vb ub
 obtain ⟨L⟩:= stock_a P Z k ξ K Ck F HK Gm Tm Vb ε p₀ k1 u' vε -- tune order
 obtain ⟨F⟩:= stock_b P Z k ξ K Ck F HK ht G' W k1 (Cg:=Cg) (o':=o') -- tune arguments HCliff
 refine bound_frame P (V'.add (L.add F)) (fun x=> ?_) w; unfold Τu; change _+(Scope.Total Y P Lθ θ _ x.val+Scope.Total Y P Lθ θ _ x.val)= _; unfold Scope.Total; rw [dif_pos x.property,dif_pos x.property]; -- tune
end YM.CF.BProof.Scene
