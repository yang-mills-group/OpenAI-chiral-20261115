import YM.CF.BProof.Prime.Offer
/-! Inert homogeneous bands license all deep cancellations. -/
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Prime
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
open Branch Tenant Air Veil
variable {α C:ℝ}{I:Type}[Fintype I](K:Core j a₁ b l r N)
variable (Q:Primer N I α C)
local notation "Ψ"=> Pouch Y P T θ
local notation "ψx"=>Z.world1 P K
local notation "ψ0"=>Z.world0 P K
namespace Estate
variable (Y)
def tint (i:Y.yard.Index) (v:Fin 5):Geometry N:= fun _=> if Y.yard.D i then 1 else locus v
variable {Y}
variable {μ:Support (More N)}(h:Clock Z k ξ)(i:Y.yard.Index)
local notation "C_"=>Δ.clock
abbrev road(z:Fin 5)(x:Seat N):=(homeScript mH z).HH Δ.clock Y.g ∅ 1 Z.p x
abbrev roadH(z:Fin 5)(i:Seat N):=road Z z i
include P
lemma road_cost(z:Fin 5)(x:Seat N):Money (road Z z x):=Rhythm.rideH E P Y Δ Z.buyS ∅ (Bias.homerL E Y Δ δ Z.lineT.safe Z.lineT.height) (Bias.homerP E Y Δ z) Z.pt Z.p0 x
include h P
lemma goes (z:Fin 5){x:Seat N}(t: x∈Y.yard.band i)(p:¬Anthem.Manus.Shallow Y.yard k x): road Z z x= if Y.yard.D i then BM 1 else Dream.side z :=by
 let D':= Trek.homeScript mH z; let v:=Bias.homerP E Y Δ z
 unfold road; rw [spectra]; apply Eq.trans ((Bias.homerP E Y Δ z).noVac _ _ _ _ _ Z.stageU.podium t ?_); rfl
 intro g; exact p ⟨_,Y.yard.vic_nearer _ _ _ k (Z.stageU.podium.nearP.le.trans h.carries) g⟩
lemma bears (z:Fin 5){x:Seat N}(t:x∈ Y.yard.band i)(p:¬Anthem.Manus.Shallow Y.yard k x): road Z z x= motion (tint Y i z x) ∘ road Z 0 x:=by
 rw [goes P Z k ξ h i z t p,goes P Z k ξ h i 0 t p]; unfold tint; split; next h=> rw [motion_one]; rfl
 unfold Dream.side; apply funext; intro v; rw [show locus 0=1 from (by simp [locus]),motion_one]; rfl -- tune
-- full path + derivatives
variable (p:∀ x∈ μ,x∈ Y.yard.band i∧ ¬ Anthem.Manus.Shallow Y.yard k x)(z:Fin 5)
include p
lemma park : (world N).agree μ (ψ0 z) ((world N).act (tint Y i z) (ψ0 0)) := by
 let g:= tint Y i z; have ht:Lattice.gauge g (1:Pane N)=1:=by ext1 j; dsimp only [Lattice.gauge,g,tint,Pi.one_apply]; group -- tune `g`
 have hp:(pine N).agree μ 1 (gauge g 1):= by rw [ht]; rfl
 apply (Veil.paired μ).2; apply And.intro ((Veil.paired μ).2 ⟨hp,(Veil.equalize μ _ _).2 ?_⟩); swap -- tune
 · refine ⟨hp,rfl,(curve_rule μ).2 fun a v=>?_⟩; funext k'; apply ContinuousMap.ext; intro x; have hA:= road_cost P Z z a; have hB:= bears P Z k ξ h i z (p a v).1 (p a v).2; rcases k' with ⟨t,b|b⟩ -- tune
   · change road Z z a _=motion (tint Y i z a) _; rw [hB]; rfl
   change deriv (road Z z a) _=motion (tint Y i z a) (deriv (road Z 0 a) _); rw [hB]; exact Hero.motionDer _ (road_cost P Z 0 a).2.1 _
 apply (tent_eq ..).2; intro x v; change (homeScript mH z).XX .. = scaledV _ ((homeScript mH 0).XX ..) -- tune tails ext ellipsis
 rw [homX_band mH g₀ z C_ Z.p Z.stageU.podium Z.pt Z.p0 (p x v).1,homX_band mH g₀ 0 C_ Z.p Z.stageU.podium Z.pt Z.p0 (p x v).1]; unfold tint; split; next h=> rw [scaled_one]; rfl
 rw [show locus 0=1 from (by simp [locus]),scaled_one,id_eq]
omit p
lemma diff_zero(a:I)(p:¬atFall Y k (Q.rent a)): Q.diff_ P Z K z a=0:=by
 unfold atFall at p; push Not at p; obtain ⟨i,p,q⟩:=p; let g:=tint Y i z; unfold Primer.diff_; rw [show Q.func a (ψ0 z)=Q.func a (ψ0 0) from ((Q.Wt a).include_b (park P Z k ξ K h i (fun i hi=> ⟨p hi,q i hi⟩) z)).trans ((Q.Wt a).ward g (ψ0 0)),sub_self] -- tune binder order
end Estate
end YM.CF.BProof.Prime
