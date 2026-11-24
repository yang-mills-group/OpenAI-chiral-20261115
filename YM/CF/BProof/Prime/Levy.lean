import YM.CF.BProof.Prime.Estate
import YM.CF.BProof.Payment.Knot

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
open Palot Anthem Payment Oasis Stint TraceD
variable (K: Core j a₁ b l r (mid m₁ B₁)) (Ck:Clock Z k ξ){p:Odd L₁.val}{X: Pricing j L₁ p (Vault.Thread j)}(F:Grasp X B₁ δ)
variable (O:Pec.Pride (mid m₁ B₁)){yv:Pay}{y₀ α A z Al Pz:ℝ}
variable (HK:Hinge F (Z.age P K) Δ.stage.c rateH Δ.stage.η yv O y₀ α A Al Pz)
local notation "I_"=> mid m₁ B₁
local notation "Code_"=> Hinge.Codes I_
-- cost here chosen independent of all size thresholds.
structure Trust (yv: Pay)(α Al z:ℝ):Prop where -- Pay typo
 pos:0≤z
 weight:4*z≤ yv.rate/2
 H:4*z≤α
 E:4*z≤Al
variable (ht: Trust yv α Al z)
abbrev wealth(ψ:Pay)(a b:ℝ) := (vaultPay ψ quota + (vaultPay ψ quota+ vaultPay ψ quota))+(a+b)
abbrev trueQ : Primer I_ Code_ z (wealth yv A Pz):=⟨Hinge.aged, HK.fee, Hinge.root, Hinge.aged_here, HK.packed, HK.income _ ht.weight ht.H ht.E,fun i h=> groveloc (HK.conducive i h)⟩
local notation "PR_"=> trueQ P Z K F O HK ht
local notation "BΘ"=> Z.hom P K
local notation "Σθ"=> Z.world0 P K
local notation "ΔΘ"=> Primer.diff_ P Z K PR_
variable (v': Fin 5)
abbrev κDept (x:Veil.TraceD.Desk I_)(z:Fin 5):= HK.T'.items x (BΘ z)
lemma rent_v (i: Desk I_)(z':Fin 5): Primer.func PR_ (Sum.inl i) (Σθ z')= HK.T'.items i (BΘ z'):=HK.Bl_eq .. -- tune
lemma homRoad (v:Fin 5): (Z.hom P K v).val.1.val.1.val=(1:Pane I_) ∧ (Z.hom P K v).val.1.val.2=Pins mH g₀ ∅ :=⟨rfl,rfl⟩
local notation "Lx"=>Loft K δ Δ.stage.c rateH Δ.stage.η
lemma qR_hom (i:TokenW I_)(x y:Lx)(d:Tape.carried x.val.1=Tape.carried y.val.1)(w:x.val.1.val.2=y.val.1.val.2): (HK.T'.items (.inl i) x).re -(HK.T'.items (.inl i) y).re=0:=by
 change (HK.T'.qReal i _).re -(HK.T'.qReal i _).re= _; unfold qReal; rw [show x.val.1=y.val.1 from Subtype.ext (Prod.ext (Subtype.ext d) w),sub_self]
lemma rent_same (i:TokenW I_)(p:Fin 5): (ΔΘ p (.inl (.inl i)))=0:=by
 have h0:= homRoad P Z K p; have h:=homRoad P Z K 0; unfold Primer.diff_; rw [rent_v,rent_v]; exact qR_hom P Z K F O HK i _ _ (h0.1.trans h.1.symm) (h0.2.trans h.2.symm)
lemma rent_im (i:TokenW I_)(p:Fin 5): ΔΘ p (.inl (.inr (.inr i)))=0:=by unfold Primer.diff_; rw [rent_v,rent_v]; change (HK.T'.qIm i _).re - (HK.T'.qIm i _).re=_; unfold qIm Spire.zen; simp
lemma pigment (i: Code_) (h: Sum.isRight i) : ΔΘ v' i=0:=by -- derive right
 rcases i with i|(i|i); simp at h
 · unfold Primer.diff_; change (-(HK.Sp i).val (1:Pane I_)).re - (-(HK.Sp i).val (1:Pane I_)).re= _; rw [sub_self]
 · unfold Primer.diff_; change (-Spire.zen ((HK.Gl i).val _)).re-(-Spire.zen ((HK.Gl i).val _)).re= _; unfold Spire.zen; simp
variable (j':1≤ j)
include Ck j'
lemma ways : Primer.MoneyZ P Z k K PR_ v':=by
 constructor; swap; exact fun i p=> diff_zero P Z k ξ K PR_ Ck v' i p
 intro i
 let iz: Support (More I_)→ Code_ := fun S=> .inl (.inr (.inl (i,S))); have he: Injective iz:=fun a b H=> by simpa [iz] using H
 let D:=(Primer.Roots PR_ i); let x:= BΘ v'; let y:=BΘ 0; let δ:= ΔΘ v'
 have hx: univ.image iz⊆ D:= by intro x h; obtain ⟨v,g,rfl⟩:= mem_image.mp h; refine mem_filter.mpr ⟨mem_univ _,?_⟩; rfl
 change ∑ p∈ D,δ p= _; rw [←sum_subset (f:=δ) hx _,sum_image he.injOn]; calc
   _ = (∑ j:Support (More I_), (HK.T'.qBias (i,j) x).re)-(∑ j:Support (More I_), (HK.T'.qBias (i,j) y).re):=by
         rw [←sum_sub_distrib]; apply sum_congr rfl; intro j _; unfold δ iz Primer.diff_; rw [rent_v,rent_v]; rfl
   _ = _:=by rw [TraceD.biasPriceX,TraceD.biasPriceX,(Z.serial P K 0).blank j' (Z.age P K) i, sub_zero] -- may need change y
 · intro a t e; rcases a with (a|(a|a))|a; exact rent_same P Z K F O HK ht a v'; refine False.elim (e (mem_image.mpr ⟨a.2,mem_univ _,?_⟩)); exact show _= _ from (by have he:a.1=i:= (mem_filter.mp t).2; unfold iz; rw [← he]); exact rent_im P Z K F O HK ht a v'; exact pigment P Z K F O HK ht v' _ rfl -- tune
lemma suppressed {pw σ:ℝ} (p:Bias.ScopeP (Gates.gap L a) D δ Δ.stage.c rateH pw k v')(pwq:0≤pw)(S':k≤ (mid m₁ B₁).val) (u:v'≠0) (v: σ+(House.root_port Y.yard.short (k+ξ) Y.g.count.val)*(2*(Primer.expL z ξ*wealth yv A Pz))≤ pw/64*(Y.g.count.val:ℝ)^3)(b:House.Block Y.yard Y.c'):
    (Primer.atBook k ξ PR_ (Z.world0 P K v') b-Primer.atBook k ξ PR_ (Z.world0 P K 0) b).re ≤ -σ:=by
 apply Primer.aperture P Z k ξ K PR_ Ck b v' ht.pos (ways P Z k ξ K Ck F O HK ht v' j') (cβ:=pw) _ v; apply Bias.shack _ _ _ _ _ _ p (Z.serial P K v') u pwq (Z.age P K) S'; exact Ck.commuter Z k ξ k (by unfold TimePlus; omega); exact Y.width.le; have := Ck.count; omega
end Estate
end YM.CF.BProof.Prime
