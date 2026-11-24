import YM.CF.BProof.Rise.Inside
import YM.CF.BProof.Prime.Levy
/- Uniform leverage on Y.Hinge realization. -/
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Prime
open Function RG Wilson Lattice Filter MeasureTheory SU Grid Angular Angular.Yard Finset Prox Mapping House Release hot Gauss Weights Pricing Micro Trek
open Gates Gates.Stage Gates.Stage.Setup Contour Contour.Season Contour.Battery Contour.Tower Cube Cabinet Pods Posts Skye Scree Jet Vault Paige Drapes Pec Seam
open scoped Topology BigOperators Classical
local notation "G"=> SU.group
variable {c:Clip}{w R v:ℝ}{S:Gates.Stage c w R v}{L:Side}{a:ℕ}{y:ℝ}{d:ℕ}{N:Side}{L₁ B₁ m₁:Side}(Y:S.Setup L a (More (mid m₁ B₁)) d y)(P:Entice S L a d y)(T:PathData G)(θ:ℝ)(x:Pod Y)
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
set_option quotPrecheck false
local notation "Ζ_"=>framesL Y P T θ
local notation "CC"=>Y.yard.long
open Rhythm Tape Hearth Lat
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Hearth Tape Mark
attribute [local instance] opCStarAlgebra
variable {N₁ N₂:ℕ} {m m':Side}{j:ℕ} {a₁ b l r:ℝ}{D:Spin.Ready j a₁ b l r}{u:ℝ} (E:Essence D u)
variable {rₜ:ℕ} (Δ:Rhythm.Note E (Gates.gap L a) rₜ)(U: Orbit (mid m₁ B₁) → Pane (mid m₁ B₁)) (ν δ:ℝ)
variable {rB:ℕ}
variable {Y E T θ Δ U ν δ} (Z : School Y T θ E Δ U ν δ rB)
open Scope Moment Push.AbsoluteSums
local notation "μz"=> Z.μwage
variable (k ξ:ℕ) -- near depth, and size cutoff in F support
open Branch Tenant Air Veil
namespace Estate
open Cliff
open Palot Anthem Payment Oasis Stint TraceD
variable (K: Core j a₁ b l r (mid m₁ B₁)) (Ck:Clock Z k ξ){p:Odd L₁.val}{X: Pricing j L₁ p (Vault.Thread j)}(F:Grasp X B₁ δ)
variable (O:Pec.Pride (mid m₁ B₁)){yv:Pay}{y₀ α A z Al Pz:ℝ}
variable (HK:Hinge F (Z.age P K) Δ.stage.c rateH Δ.stage.η yv O y₀ α A Al Pz)
local notation "I_"=> mid m₁ B₁
local notation "Code_"=> Hinge.Codes I_
variable (ht: Trust yv α Al z)
local notation "PR_"=> trueQ P Z K F O HK ht
local notation "BΘ"=> Z.hom P K
local notation "Σθ"=> Z.world0 P K
variable (w0:House.Block Y.yard Y.c')(xw:Pouch Y P T θ)
local notation "ΖQ"=> central Y xw.val w0
local notation "BΛ"=> Z.pose P K
local notation "Φx"=> Z.world1 P K xw
local notation "Φz"=> Z.world0 P K ΖQ
local notation "Φ0"=>Z.hom P K ΖQ
local notation "δθ"=> Rhythm.Lease.wearC S y
local notation "κθ"=> Tape.carried (Z.pose P K xw).val.1
variable (Pw:w0∉ nearL Y xw.val)(Γ: Cliff.Inside S E δ y₀ y)(fu:u≤F.p)
lemma πBias (z:Fin 5): World.x (Z.world0 P K z)=1:=rfl -- tune
section
variable {D:Type}{K: Jet.Draw D}{W:D→ℂ}{v ε:ℝ}
lemma plotsH(q: OrderD K 1 W v)(X:ℝ→D)(p:K.test ℝ Set.univ X)(t:ℝ)(vT:0≤t) : ‖W (X t)-W (X 0)‖ ≤ t*v:=by -- v shadow norm price
 let f:= W ∘ X; have hk(t):= q ℝ Set.univ isOpen_univ X p t (Set.mem_univ t); have he:=Convex.norm_image_sub_le_of_norm_fderiv_le (C:=v) (fun t (_:t∈(Set.univ:Set ℝ))=> (hk t).smooth.differentiableAt (by simp)) (fun t (_:t∈Set.univ)=> by rw [← norm_iteratedFDeriv_one]; exact (hk t).norm_le 1 (by omega)) convex_univ (Set.mem_univ 0) (Set.mem_univ t); rw [sub_zero,Real.norm_of_nonneg vT,mul_comm] at he; exact he
lemma zen_p(x y:ℂ) : ‖Spire.zen x-Spire.zen y‖≤ ‖x-y‖:= by unfold Spire.zen; rw [←mul_sub,norm_mul,Complex.norm_I,one_mul,← Complex.ofReal_sub,← Complex.sub_im,Complex.norm_real]; exact Complex.abs_im_le_norm _
end
local notation "Cρ"=> money_θ D S y ξ
include Pw Γ fu Ck
variable {i : Veil.Atom (More (mid m₁ B₁))}(hS:∀ j∈ atS i, Cliff.Calm Z k ξ w0 j)
include hS
local notation "XΘ"=>Z.stun P xw.val
lemma ζHum : ‖(HK.Gl i).val (κθ,XΘ)-(HK.Gl i).val (1,Z.homX ΖQ)‖≤ δθ * HK.J.fare i:=by
 let F₁:= HK.J.value i; obtain ⟨w⟩:= Cliff.spend_ P Z k ξ K Ck w0 xw Pw (atS i) hS Γ F.p fu -- tune
 let X(t):Brace.Chord m₁ B₁ δ F.p:=⟨(w.U t,w.X t),w.safe t,w.fuel t⟩
 have he:(w.U 0,w.X 0)=(1,Z.homX ΖQ):= w.start
 rw [←he, ← (HK.Gl i).include_b w.done]; change ‖(HK.Gl i).val (X δθ).val- (HK.Gl i).val (X 0).val‖≤_; rw [HK.Gl_eq,HK.Gl_eq]; refine plotsH (HK.J.plot i).plot X (fun i _=> w.plot i) δθ Γ.shape.safe.le -- tune
lemma ζPig : ‖(HK.Sp i).val κθ-(HK.Sp i).val 1‖≤ δθ * HK.A.fare i:=by
 obtain ⟨w⟩:= Cliff.spend_ P Z k ξ K Ck w0 xw Pw (atS i) hS Γ F.p fu
 let X(t): Spire.CapX m₁ B₁ δ:= ⟨w.U t,w.safe t⟩; rw [← show (HK.Sp i).val (w.U δθ)=_ from (HK.Sp i).include_b ((Veil.paired _).1 w.done).1,←show (X 0).val=1 from (Prod.mk.inj w.start).1]; change ‖(HK.Sp i).val (X δθ).val- (HK.Sp i).val (X 0).val‖≤ _; rw [HK.Sp_eq,HK.Sp_eq]; exact plotsH (HK.A.plot i).plot X (fun i _=> (w.plot i).1) δθ Γ.shape.safe.le -- tune syntax
omit hS
variable {ρ σ:ℝ}
lemma snowfall (p: (Cρ+δθ)≤ρ) (t: Code_)(u:t∈ Primer.entry Y k ξ PR_ w0)(e:Primer.tax PR_ t≠0): Primer.Varies P Z K PR_ ρ w0 xw t ΖQ:=by
 have ht:Micro.Loc (Hinge.aged t):= Primer.breadth PR_ t e; obtain ⟨⟨g,v⟩,p'⟩:= (Primer.claim_H Y k ξ PR_ w0 |>.1 u); have h:∀ j∈ Primer.rent PR_ t, Cliff.Calm Z k ξ w0 j:= fun j v'=> p' ▸ Cliff.after_clock Z k ξ Ck g ht v (Hinge.root t) (Hinge.aged_here t) v'; apply le_trans (_ : ‖Primer.func PR_ t Φx-Primer.func PR_ t Φz‖≤ ((Cρ+δθ)) * Primer.tax PR_ t) (mul_le_mul_of_nonneg_right p ((Primer.toll PR_).nonneg _)); rcases t with t|(t|t)
 · unfold Primer.func; change ‖(HK.Bl t).val (sion (BΛ xw))-(HK.Bl t).val (sion (Z.hom P K ΖQ))‖≤_; rw [HK.Bl_eq,HK.Bl_eq]; exact le_trans (Cliff.household _ _ _ _ _ w0 xw HK.T' t v h Ck Pw) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right Γ.shape.safe.le) ((Primer.toll PR_).nonneg (.inl t))) -- tune
 · change ‖-(HK.Sp t).val κθ- -(HK.Sp t).val 1‖ ≤ _ -- tune is - f - -g should specify
   rw [neg_sub_neg, norm_sub_rev]; exact le_trans (ζPig P Z k ξ K Ck F O HK w0 xw Pw Γ fu h) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (Cliff.voteV ..)) ((Primer.toll PR_).nonneg (.inr (.inl t))))
 change ‖-Spire.zen _- -Spire.zen _‖≤_; -- tune binder ℂ
 rw [neg_sub_neg,norm_sub_rev]; refine le_trans ((zen_p ..).trans (ζHum P Z k ξ K Ck F O HK w0 xw Pw Γ fu h)) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (Cliff.voteV ..)) ((Primer.toll PR_).nonneg (.inr (.inr t))))
omit Pw
lemma cost_purchase {b4:ℝ}(p:∀ z:Fin 5, Bias.ScopeP (Gates.gap L a) D δ Δ.stage.c rateH b4 k z)(uB:0≤b4)(S':k≤ (mid m₁ B₁).val)(j':1≤j)(q: (Cρ+δθ)≤ρ)(v: σ+(House.root_port Y.yard.short (k+ξ) Y.g.count.val)*(2*(Primer.expL z ξ*wealth yv A Pz))≤ b4/64*(Y.g.count.val:ℝ)^3): Primer.Guard P Z k ξ K PR_ ρ σ := ⟨ht.pos,(le_trans (add_nonneg (Cliff.voteV ..) Γ.shape.safe.le) q),fun w x Pw t u e=> snowfall P Z k ξ K Ck F O HK ht w x Pw Γ fu q t u e, fun k' t x=> suppressed P Z k ξ K Ck F O HK ht _ j' (p k') uB S' t v x⟩
end Estate
end YM.CF.BProof.Prime
