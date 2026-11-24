import YM.SU5.Reconstruction.AllGrades.Crown
import YM.SU5.Reconstruction.AllGrades.ThermalPace
import YM.SU5.Reconstruction.AllGrades.Boarding
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

attribute [local instance] opCStarAlgebra
open SlabMark MeshClock Tilted
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
open Garret NorthTapes
open _root_.YM.Hilbert.Freight
variable (D:Invitation Y H G)
local notation "l₀" b:max s:max t:max F:max => launch Y H G D b s t F
variable (a:Axis)(b:Bool)(s:ℕ)
local notation "Fm"=>studio (tent Y H) a 0 b
variable (P: Inspector Y H G)
local notation "Ω"=> P.pulse
local notation "Bp" s:max => badge Y H V G D a b s P
local notation "hP" p:max f:max=> homePlane Y H V G D a b _ _ p f
local notation "W"=> poleForm (tent Y H) a 0 b
local notation "C₀"=> chime (tent Y H)
local notation "Θ"=> mirror (tent Y H)
local notation "L"=> Λ.R.L.val
open Heat
open WindRose PolarArchives ConePrice SelectionAnalysis Chambers Brazier
variable (C:∀ j, Arena Y H G.history.circuit j 0 false)(j:Axis)
variable (χ: displayAlgebra Y H V G.history G.clipped j false (C j) →⋆ₐ[ℂ] ℂ)
local notation "mK"=> marks (timeMesh Λ)
local notation "K₀"=>displayAlgebra Y H V G.history G.clipped a false (C a)
local notation "Ω₀"=> courseValue Y H V G
local notation "Kw"=>driveAlgebra Y H V G.history G.clipped a false (C a)
local notation "F₊"=> Domain Y H G false (flank a 0)
local notation "Sm" m:max=> strip a (-(m:ℝ)) (m:ℝ)
local notation "Qt" m:max=> flank a (m:ℝ)
local notation "bM" d:max=> strip a (-d) d
local notation "A₀"=> atlasAt Y H V G
local notation "Pt" m:max=> Pub Y H a m
local notation "Bk" d:max f:max => (((badge Y H V G D a b d (atlasAt Y H V G)) f))
local notation "Px" u:max f:max=> ticket Y H G u f
local notation "rF"=> studio (tent Y H) a 0 b
local notation "rW"=> studio (tent Y H) a 0 false
local notation "Δ"=> timeMesh Λ
local notation "Wq" n:max=> walkC Y H a b n
local notation "Tr"=> cruise Y H a b

/-! # Unconditional even Spacebody voter equivalence & movement. -/
open Nymph
local notation "SJ"=> displacement Y H V G.history G.clipped j false (C j) χ a (C a)
local notation "KJ"=> indoor Y H V G.history G.clipped a false (C a) SJ
local notation "Τ"=> voterAt Y H V G C j χ
local notation "Q" t:max => badge Y H V G D a false t Τ
local notation "B⚬" t:max x:max=> bud Y H V t G.history G.clipped a false (C a) SJ x
local notation "FA"=>studio (tent Y H) a 0 false
local notation "FW" t:max=> Tower.Field Y H t a 0 false
local notation "ρ" t:max u:max p:max x:max=> homePlane Y H V G D a false t u p x
local notation "Sx"=> Works Y H V G D a false Τ

open Roy ConePrice.Session LightBudget
variable (B:BoostBacking Y H V G C j χ)
local notation "Σv"=> peninsula Y H V G.history G.clipped a false (C a) SJ
local notation "ᾼ"=> fort Y H V G.history G.clipped a false (C a) SJ
local notation "Fc"=> saunters Y H V G.history G.clipped a false (C a) SJ
local notation "Mu"=> voter_credit Y H V G D a false C j χ
local notation "R"=> wheelTimes Y H V G D a false Τ Mu
local notation "cr"=> regime Y H V G D a false Τ
local notation "λy"=> spokesman Y H V G D a C j χ
local notation "u₀"=> echoV Y H V G D a C j χ
local notation "kR"=> ride Y H V G.history G.clipped a false (C a) SJ
local notation "da"=> dainty Λ
open Germ
variable (T:Frostland Y H V G C j χ)(x y:studio (tent Y H) a 0 b)(l':Trans a)
local notation "ℋ" d:max s:max=> homePlane Y H V G D a d s
local notation "V₀"=> Impetus Y H V G D a b Τ
local notation "η"=>voter_credit Y H V G D a b C j χ
local notation "λx" b:max s:max x:max=> badge Y H V G D a b s (voterAt Y H V G C j χ) x
local notation "λo" b:max=>regime Y H V G D a b (voterAt Y H V G C j χ)
local notation "So"=> wheelTimes Y H V G D a b Τ η
local notation "Zμ"=> Lore (So) (λo b)
local notation "We" => turnLane Y H a b l'
local notation "Ml" n:max=> multiplyG Y H a b x (We n x)
local notation "ρL" s:max n:max=> notch (dainty Λ) s (n:ℤ)
open ConePrice Session
open InnerProductSpace
local notation "Kσ"=> (Works Y H V G D a b Τ)
local notation "σ"=> travelingAll Y H V G D a b C j χ B T
local notation "Hψ"=> (λo b).crew l'
local notation "Ζ"=> (Hψ).play
local notation "pm" t:max x:max=> ((badge Y H V G D a b t Τ) x)
local notation "CK" c:max=> wheelTimes Y H V G D c b Τ (voter_credit Y H V G D c b C j χ)
local notation "Ho" c:max s:max x:max=> badge Y H V G D (c:Axis) b s Τ x
local notation "Sk" c:max=> studio (tent Y H) c 0 b
local notation "vR" t:max=> (travelingAll Y H V G D a b C j χ B T).E t

local notation "tz" c:max n:max f:max=> chime (tent Y H) c (2*n) f
local notation "N"=> studio (tent Y H) a 0 b
local notation "p₀"=> (Τ).pulse
local notation "Cu"=> cue (σ)
local notation "ρx" n:max=> notch (dainty Λ) s n
local notation "Aσ"=> badge Y H V G D a b s (voterAt Y H V G C j χ)
variable {S S':Finset Cover}{f g:Family (tent Y H)} (p:InTest (tent Y H) true S true f) (q:InTest (tent Y H) true S' true g)
 -- Fermi character method
local notation "Δ"=> dainty Λ
local notation "πz" t:max x:max=> badge Y H V G D a true t Τ x
private lemma oddExchange{J: Calibration}{f g:Family J} (p:InTest J true S true f)(q:InTest J true S' true g):f*g= -(g*f):=by
  funext m k; have he:= ((p.support m).mono (Finset.subset_univ _)).allV k; have hv:= ((q.support m).mono (Finset.subset_univ _)).allV k; change f m k*g m k= -(g m k*f m k); simpa [Fock.Sector.grainB] using he.sign_com hv
private lemma cancel_step {S:Finset Cover}{b:Bool}{A:Calibration}{f:Family A}(p:InTest A true S b f)(n:ℤ): chime A a (2*n) (chime A a (2*(-n)) f)= f:=by rw [march_sums a b p,mul_neg,add_neg_cancel,march_zero a b p]
private lemma cancel_step'{S:Finset Cover}{b:Bool}{A:Calibration}{f:Family A}(p:InTest A true S b f)(n:ℤ): chime A a (2*(-n)) (chime A a (2*n) f)= f:=by nth_rw 2 [← neg_neg n]; exact cancel_step a p (-n) -- occurrences? check
private lemma backward_price {S:Finset Cover}{p:Family (tent Y H)}(h:InTest K true S false p): p₀ s (-p)= -p₀ s p:=by rw [← neg_one_smul ℂ p,(Τ).scale s (aux_test h),neg_one_smul]
local notation "Ψ" f:max=> Reflect.chord true • (p₀ s f)
include p q
private lemma splice_odd (u:ℤ) : (Ψ (f*(tz a u (tz l'.val (-u) g))))= -(Ψ (g*(tz l'.val u (tz a (-u) f)))):=by
    let Y':=tz a u (tz l'.val (-u) g); let F:= tz l'.val u (tz a (-u) f); let p':=flow_port K l'.val (2*u) (flow_port K a (2*(-u)) p); let q':= flow_port K a (2*u) (flow_port K l'.val (2*(-u)) q); have ht:= tariff_leg Y H true p q'
    have hy: tz a (-u) (tz l'.val u (f*Y')) = F*g:=by
       unfold Y' F; rw [chime_product,chime_product,march_comm l'.val true p,←march_comm l'.val true (flow_port (tent Y H) l'.val (2* -u) q)]; rw [cancel_step l'.val q,cancel_step' a q]; -- orientation `march_comm` : chime j(... a= l') → chime a(... j), want `c_u (a_u)(c_-u) g`; first uses j=a; rw `←` yes
    change Reflect.chord true • (p₀ s (f*Y')) = - _
    rw [← (Τ).parity s l'.val u ht, ← (Τ).parity s a (-u) (aux_test (flow_port (tent Y H) l'.val _ ht.paid.choose_spec)), hy, oddExchange p' q, backward_price Y H V G s C j χ (tariff_leg Y H true q p').paid.choose_spec, smul_neg]
lemma asymmetric {d d':ℂ}(u:Crown Y H V G a true s C j χ f g d)(v:Crown Y H V G l'.val true s C j χ g f d') : d= -d':=by
 apply tendsto_nhds_unique_of_eventuallyEq (u.horizon l' (fun i=> -(i:ℤ))) ((v.horizon (⟨a,l'.property.symm⟩:Trans l'.val) (fun i=> -(i:ℤ))).neg)
 exact Eventually.of_forall fun r=> splice_odd Y H V G a s C j χ l' p q r
omit q
include D B T
lemma story_zero : Crown Y H V G a true s C j χ f f 0:=by
 obtain ⟨c,v⟩:= story_lives Y H V G D a true s C j χ B T p p
 obtain ⟨k,h⟩:= exists_ne a; let b':Trans a:=⟨k,h⟩; obtain ⟨d,u⟩:=story_lives Y H V G D b'.val true s C j χ B T p p
 have ht:c=d:= asym_equal Y H V G a true s C j χ b' p v u; let t':= asymmetric Y H V G a s C j χ b' p p v u; have he:c=-c:= t'.trans (congrArg Neg.neg ht.symm)
 have he':c=0:=by
    apply Complex.ext; · have h1:= congrArg Complex.re he; simp only [Complex.neg_re] at h1; rw [Complex.zero_re]; linarith
    have h1:= congrArg Complex.im he; simp only [Complex.neg_im] at h1; rw [Complex.zero_im]; linarith
 exact he' ▸ v
-- every odd-support mark Y. Taking limit for shifts of Θ-real at same height.K.Meta.
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.asymmetric
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.story_zero
