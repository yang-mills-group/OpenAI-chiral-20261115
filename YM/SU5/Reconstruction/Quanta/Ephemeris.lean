import YM.SU5.Reconstruction.Quanta.Printer
import YM.SU5.Reconstruction.Quanta.Touch
import YM.SU5.Reconstruction.FirstWindows.Unwrap
/-! # Unconditional procurement at the chosen character. Takes leads on even ROOT only, costs on both grades. -/
-- Header
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
set_option linter.unusedVariables false -- h₁, V etc
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock Tilted
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G
open WindRose
variable (C : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (j:Axis)
variable (χ : displayAlgebra Y H V G.history G.clipped j false (C j) →⋆ₐ[ℂ] ℂ)


open Garret PhaseChoice
local notation "Pₓ" => price Y H V G C j χ
variable (S:Finset Cover)(s:ℕ)
local notation "i₀" r:max=> i (G.rows r)
local notation "k₀" r:max=> k (G.columns r)
local notation "W₀" t:max=> volumeAround Λ l t S
abbrev ingress (f:Family (tent Y H))(b:Bool)(r t:ℕ): Family (tent Y H) := Garret.quarry Y H s (i (G.rows r)) (k (G.columns r)) b S f t
local notation "Qr" b:max f:max r:max t:max=> ingress Y H G S s f b r t
/- Honor all CP1 geometry. Sequence keeps approximately right χ Gram, AND REAL support budgets at every stage for each f, sign paid. No requiring odd operator caps spent at height∞. -/
structure TowerCheck (n r:ℕ):Prop where
 pay₀ : Tapestry.Pay Y (s+n) (i₀ r) (k₀ r)
 spirit {f:Family (tent Y H)}{b:Bool}(p:InTest (tent Y H) true S b f)(u:ℕ)(v:u≤n) : InTest (tent Y H) true (W₀ u) b (Qr b f r u) ∧ (CovCover (tent Y H) f → CovCover (tent Y H) (Qr b f r u))
 stepwise {f:Family (tent Y H)}{b:Bool}(p:InTest (tent Y H) true S b f)(u:ℕ)(v:u<n): distribute Y H ((s+u)+1) (i₀ r) (Qr b f r (u+1)) =aboveD Y H (s+u) (i₀ r) (k₀ r) (Qr b f r u)
 spaceOp (U:Set RSpace)(p:PhaseChoice.SupportedPhysically Λ l s S U) (u:ℕ): PhaseChoice.SupportedPhysically Λ l (s+u) (W₀ u) U
 receipt (a:Axis)(z:ℤ)(p:Tower.region a z (reserve Λ l) S)(u:ℕ): Tower.region a ((Λ.R.L.val:ℤ)^u*z) ((tent Y H).ℓ) (W₀ u)
 -- polls width certification uniform independent of t goal, even beyond.
 stake (u:ℕ) : PhaseChoice.FullDistances (W₀ u) (Journey.side Y (i₀ r) (s+u))
include V
lemma review(n:ℕ) : ∀ᶠ r in atTop,TowerCheck Y H G S s n r:=by
 let Q:= G.history; have h:Tendsto (fun r=>i₀ r) atTop atTop:= (V.pick.grow_i.comp Q.growsA).tendsto_atTop
 filter_upwards [Q.finance (s+n),Garret.certified Y H V s S Q n,h.eventually (unwrapped Y H s S),Garret.living Y H V s S Q n,Garret.voiceArc Y H V s S Q n] with r p c a x y -- notation Q shadow hv tune
 refine ⟨⟨p.depth,p.enters⟩,fun {f b} v t u=> ⟨x t u f b v,y t u f b v⟩,fun {f b} p u v=> ?_,fun _ p i=>p.persists i,fun a z g n=>Garret.parades Y H a z g n,a⟩
 exact (c u v b _ (x u v.le f b p)).2.2 -- ℭastery
variable (a:Axis)(z:ℤ)
local notation "z₀" t:max=> ((Λ.R.L.val:ℤ)^t*(Heat.gaugeShift Λ.block z))
local notation "Mₓ" t:max=> poleForm (tent Y H) a (z₀ t)
local notation "Mp" => poleForm (tent Y H) a (Heat.gaugeShift Λ.block z)
variable {b:Bool}{f g:Family (tent Y H)}(p:InTest (tent Y H) true S b f)(q:InTest (tent Y H) true S b g)
local notation "c₀"=>reflectedBox a (Heat.gaugeShift Λ.block z) S ∪ S
local notation "F₀" r:max u:max=>train Y H s u (i₀ r) (k₀ r) c₀ (Mp b f g)
local notation "Ψ" => Mp b f g
variable (n:ℕ)(h: Tower.region a (Heat.gaugeShift Λ.block z) ((tent Y H).ℓ) S)
structure SpeaksAt (n r:ℕ) (b:Bool)(f g:Family (tent Y H)):Prop where
 tone(u:ℕ)(v:u ≤ n): train Y H s u (i (G.rows r)) (k (G.columns r)) (reflectedBox a (Heat.gaugeShift Λ.block z) S ∪ S) (Mp b f g)=
    (Mₓ u) b (ingress Y H G S s f b r u) (ingress Y H G S s g b r u)
include p q h
lemma studio_link : ∀ᶠ r in atTop, SpeaksAt Y H G S s a z n r b f g:=by
 have ht : ∀ᶠ r in atTop,∀ u∈ Finset.Iic n,F₀ r u=(Mₓ u) b (Qr b f r u) (Qr b g r u):=by
    rw [Finset.eventually_all]; intro u _; exact (Garret.reaches Y H V s S a (Heat.gaugeShift Λ.block z) G.history c₀ u h).mono fun r p' => p' _ _ _ p q (NorthTapes.statement a _ p q)
 exact ht.mono fun r h=> ⟨fun t p=> h t (Finset.mem_Iic.mpr p)⟩
-- actually those very coupled Gram reached in χ and at arbitrary tance IN THIS faithful unselected tracks.E.N: still not claiming cross-height Gram of odd nor that χ evalu limits simply on sharp except through those Brace consultations.P.One.
lemma visible_with_meter : Tendsto (fun r=> Pₓ (s+n) false ((Mₓ n) b (Qr b f r n) (Qr b g r n))) atTop (𝓝 (Pₓ s false Ψ)):=by
 let u:= NorthTapes.statement a (Heat.gaugeShift Λ.block z) p q
 let H':= Garret.family_train Y H s G.history (n:=n) u
 rw [← context_lift Y H V G C j χ (q:=n) u]; apply (price_limit Y H V G C j χ (s+n) H').congr'; filter_upwards [studio_link Y H V G S s a z p q n h] with r p; rw [p.tone n le_rfl] -- left notation tune

end YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.review
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.studio_link
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.visible_with_meter
