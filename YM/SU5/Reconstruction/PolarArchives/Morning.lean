import YM.SU5.Reconstruction.PolarArchives.Lease
-- Header
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.PolarArchives
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
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
local notation "Mirror" i:max=> flipMark i (tent Y H)
open Stormwatch ConePrice Germ SelectionAnalysis CrossedFrame
open YM.ConePrice.Storm
local notation "µ" => Domain Y H G false Set.univ
local notation "Gt" => marks (timeMesh Λ)
local notation "au"=>move K
variable (P:Ramp)
local notation "H₀"=> Ark.Ht Y H G.history.circuit P.a 0 false (C P.a)
local notation "A"=>Aurora Y H V G.history P.a false (C P.a)
local notation "Pc"=>album Y H V G C P.a
local notation "pay"=> LightBudget.prepaid Y H V G P.a (C P.a)
local notation "vc"=>seat0 Y H V G.history P.a false (C P.a)
local notation "px"=> (A).orthogonalProjectionOnto
local notation "Nₐ"=> Domain Y H G false (flank P.a 0)
local notation "τ" => gust P (tent Y H)
open Chambers
local notation "μₜ" t:max=>move (tent Y H) (eject P.a t)
variable {q:Bool}{U:Set RSpace}
local notation "K₀"=>displayAlgebra Y H V G.history G.clipped P.a false (C P.a)
local notation "Hₛ"=> groundRoom Y H V G.history P.a false (C P.a)
local notation "Ωχ"=> courseValue Y H V G
local notation "Kw"=>driveAlgebra Y H V G.history G.clipped P.a false (C P.a)
local notation "Rs"=> reduceToDisplay Y H V G.history G.clipped P.a false (C P.a)
local notation "RX"=>rotateQ P K
variable (gap:ℝ≥0)
noncomputable def Acres(P:Ramp)(gap:ℝ≥0):Set RSpace := {x:RSpace|(gap:ℝ) < landN P x}
noncomputable def SkyAcres(P:Ramp)(gap:ℝ≥0):Set RSpace:= {x:RSpace|landN P x< -(gap:ℝ)}
local notation "U" => Acres P gap
local notation "U'"=> SkyAcres P gap
lemma Acres_far(P:Ramp)(d:ℝ≥0): Acres P d⊆ northD P:=fun _ t=> lt_of_le_of_lt d.property (show (d:ℝ)< _ from t)
lemma Ivory_near(P:Ramp)(d:ℝ≥0): SkyAcres P d⊆ southD P:=fun _ h=> lt_of_lt_of_le (show _ < -(d:ℝ) from h) (neg_nonpos.mpr d.property)
lemma acre_N_S: P.s.act '' U⊆ U':=by rintro _ ⟨x,h,rfl⟩; show landN P _<_; rw [land_turn]; exact neg_lt_neg h
lemma acre_S_N:P.s.act '' U'⊆ U:=by rintro _ ⟨x,h,rfl⟩; show _ < landN P _; rw [land_turn]; linarith [show landN P x< -(gap:ℝ) from h]
lemma unpaired: Disjoint (P.s.act '' U) U:= Disjoint.mono ( (acre_N_S ..).trans (Ivory_near ..)) (Acres_far ..) (N_disjoint P)
local notation "Fₛ" q:max => Domain Y H G q (Acres P gap)
include V in
lemma pay_your {f g:Sky (tent Y H)}(t:f∈Fₛ q)(h:g∈Fₛ q): τ f*g∈ Domain Y H G q univ:=
 domain_mult_to Y H G (shelters Y H V G P t) h (unpaired P gap) (subset_univ _) (subset_univ _)
/-- RAW continuum requirement.Applies all the history.No χ cost presumed. -/
noncomputable def Rectitude(P:Ramp)(gap:ℝ≥0): Prop:= ∀ x:Domain Y H G true (Acres P gap),∀ h:gust P K x.val*x.val∈µ,0≤ courseValue Y H V G ⟨gust P K x.val*x.val,h⟩
-- use the estimator on these ACTUAL sharp probes no need control star there or all along trajectory for any ε.
local notation "S" =>sharp Y H
noncomputable def Volt(P:Ramp)(gap:ℝ≥0):Prop:= ∀ (s:ℕ)(f:Dome (tent Y H)), f∈insideAt Λ l K true (Acres P gap) s → ∀ ε:ℝ, 0<ε → ∃ᶠ t:ℕ in atTop,-ε≤ (sharp Y H s (i (G.rows t)) (k (G.columns t)) ((P.cuspF K f.val)*f.val)).re
lemma reflection_root (x:Sky (tent Y H))(h:τ x*x∈ Domain Y H G false Set.univ):
   0≤ Ωχ ⟨τ x*x,h⟩ ↔ 0≤ (Ωχ ⟨τ x*x,h⟩).re:= by
 let z:= τ x*x; have ht: gust P K z=z:= by unfold z; rw [gust_mul,gust_square,mul_comm];
 have h':Ωχ ⟨z,h⟩=star (Ωχ ⟨z,h⟩):= (congrArg Ωχ (Subtype.ext ht.symm)).trans (staff Y H V G P h (ht.symm ▸ h))
 rw [Complex.le_def]; apply and_iff_left_of_imp; intro _; have q0:= congrArg Complex.im h'; change 0=(Ωχ ⟨z,h⟩).im; change (Ωχ ⟨z,h⟩).im= -(Ωχ ⟨z,h⟩).im at q0; linarith
lemma born (p:Volt Y H G P gap): Rectitude Y H V G P gap:= by
 rintro ⟨x,s,f,h,rfl⟩ v -- pattern subtype nested? test
 change 0≤Ωχ ⟨τ (ticket Y H G s f)* ticket Y H G s f,v⟩; rw [reflection_root]
 let W:= windTilt P K f*f
 have e: ticket Y H G s W= τ (ticket Y H G s f)* ticket Y H G s f:=by rw [gust_ticket Y H V]; exact ticket_separated Y H G (protects P s true (Acres P gap) _ h) h (unpaired P gap) -- ticket_separated requires... maybe q implicit
 rw [show (⟨_,v⟩: Domain Y H G false Set.univ) = ⟨ticket Y H G s W,ticket_loose ..⟩ from Subtype.ext e.symm,course_ticket_val]
 have hl:= PhaseChoice.final_limit Y H G s W.val ((marque ..).1 W.property)
 specialize p s f h; by_contra r; rw [not_le] at r; obtain ⟨δ,v₁,v₂⟩:= exists_between r
 have hz:0< -δ:= neg_pos.mpr v₂; obtain ⟨t,z,y⟩:= ((p _ hz).and_eventually ((Complex.continuous_re.continuousAt.tendsto.comp hl).eventually (gt_mem_nhds v₁))).exists; rw [neg_neg] at z; exact not_lt.mpr z y
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.PolarArchives
