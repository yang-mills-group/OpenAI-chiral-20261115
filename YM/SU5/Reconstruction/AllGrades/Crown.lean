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
variable {S S':Finset Cover}{f g:Family (tent Y H)} (p:InTest (tent Y H) true S b f) (q:InTest (tent Y H) true S' b g)
 -- not actual fields colors necessarily
include p q
lemma tariff_leg : TestFamily (tent Y H) true (f*g):=by have ht:=InTest.mul (p.mono (Finset.subset_union_left (s₂:=S'))) (q.mono Finset.subset_union_right); rw [Bool.xor_self] at ht; exact aux_test ht -- p q not included? add
include B T D
lemma story_beacon {m n:ℕ}(u: mirror K a 0 (chime K a (2*(-(m:ℤ))) f)∈ N)(v:C₀ a (2*(n:ℤ)) g∈ N)(w:ℕ→ℤ):
    let y: studio (tent Y H) a 0 b:= ⟨_,u⟩; let x: studio (tent Y H) a 0 b:= ⟨_,v⟩
    Tendsto (fun i:ℕ=> Reflect.chord b • (p₀ s (f* chime (tent Y H) a (2*(i:ℤ)) (chime (tent Y H) l'.val (2*w i) g)))) atTop
       (𝓝 (inner ℂ (pm s y) (Cu (pm s x)))):=by
    intro y x
    let i(k:ℕ):= k-(m+n); let z(i:ℕ):= Picket.cross a l'.val l'.property; let t(i:ℕ): OS.Cross a:= (ρx (w i):ℝ) • z i; let V'(k:ℕ):ℝ≥0:= whenly da s (i k)
    have he:Tendsto i atTop atTop:=tendsto_atTop_atTop.mpr fun t=>⟨t+(m+n),fun r w=>by unfold i; omega⟩
    let x':=pm s x; let y':=pm s y
    have ht:Tendsto V' atTop atTop:=by unfold V' whenly; exact (tendsto_natCast_atTop_atTop.comp he).atTop_mul_const (mill_pos (dainty Λ) s)
    apply (tendsto_const_nhds (x:=y')|>.inner (𝕜:=ℂ) (clock_frost _ (all_light Y H V G D a b C j χ B T) V' t x' ht)).congr'
    filter_upwards [eventually_ge_atTop (m+n)] with k h; let s':= chime K l'.val (2*w k) g; let y₁:= turnLane Y H a b l' (w k) x
    change inner ℂ y' ((σ).E _ ((σ).U _ _))= _
    rw [show (σ).U (t k) x'= Aσ y₁ from ?_]
    swap;· change (σ).U ((ρx (w k):ℝ) • Picket.cross a _ _) x'= _; rw [←coast_real Y H V G D a b C j χ B T l' (ρx (w k)),regime_value]; exact atLane ..
    have H₁: y₁.val= chime K a (2*n) s':=march_comm a b q _ _ l'.val
    let p':chime K a (2*n) s'∈ N:= H₁ ▸ (show y₁.val∈ N from y₁.property)
    rw [show (σ).E (V' k) (Aσ y₁)= Aσ (walkC Y H a b (i k) y₁) from ages_pose .., show y₁=(⟨_,p'⟩:N) from Subtype.ext H₁]; exact reach_eq Y H V G D a b s Τ p (flow_port K l'.val _ q) u p' k h
omit p q
-- inner limit orientation characteristic
structure Crown (x y:Family (tent Y H)) (d:ℂ):Prop where
 horizon(l':Trans a)(w:ℕ→ℤ): Tendsto (fun i:ℕ=> Reflect.chord b • (p₀ s (x*(tz a (i:ℤ) (tz l'.val (w i) y))))) atTop (𝓝 d)
include p q
lemma story_lives : ∃ c,Crown Y H V G a b s C j χ f g c:=by
 obtain ⟨m,u⟩:=left_fit Y H a b p; obtain ⟨n,v⟩:=right_fit Y H a b q; exact ⟨_,⟨fun r w=> story_beacon Y H V G D a b s C j χ B T r p q u v w⟩⟩
-- along any c
omit B T D p
lemma singles {d:ℂ}(u:Crown Y H V G a b s C j χ f g d): Tendsto (fun i:ℕ=> Reflect.chord b • (p₀ s (f*(tz a (i:ℤ) g)))) atTop (𝓝 d):=by
 obtain ⟨c,h⟩:= exists_ne a; let r:Trans a:=⟨c,h⟩; apply Tendsto.congr _ (u.horizon r (fun _=>0)); intro i; rw [mul_zero,march_zero c b q] -- order ζ projection
lemma asym_equal{d e:ℂ}(v:Crown Y H V G a b s C j χ f g d)(u:Crown Y H V G l'.val b s C j χ f g e):d=e:=by
 let h':Trans l'.val:=⟨a,l'.property.symm⟩; apply tendsto_nhds_unique_of_eventuallyEq (v.horizon l' (fun x=>x)) (u.horizon h' (fun x=>x)); filter_upwards with i; rw [march_comm l'.val b q]
omit q
local notation "Θg"=> cue (σ)
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.story_lives
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.singles
