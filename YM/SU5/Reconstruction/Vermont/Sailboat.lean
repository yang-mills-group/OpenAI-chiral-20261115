import YM.SU5.Reconstruction.Vermont.Chronicle
import YM.SU5.Reconstruction.Vermont.Hear
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock ConePrice SelectionAnalysis Germ Chambers
open Anvil
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G false
local notation "Ds" => Domain Y H G true
local notation "Gt" => marks (timeMesh Λ)
variable (C : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (a:Axis)
variable (χ : displayAlgebra Y H V G.history G.clipped a false (C a) →⋆ₐ[ℂ] ℂ)
local notation "w" i:max=> displacement Y H V G.history G.clipped a false (C a) χ i (C i)
local notation "J₀" i:max=> indoor Y H V G.history G.clipped i false (C i) (w i)
local notation "C₀" i:max=> saunters Y H V G.history G.clipped i false (C i) (w i)
local notation "G₀" i:max=> fort Y H V G.history G.clipped i false (C i) (w i)
local notation "Ω₀" i:max=> vocation Y H V G.history G.clipped i false (C i) (w i)
local notation "S₀" i:max=> peninsula Y H V G.history G.clipped i false (C i) (w i)
local notation "ℜ" p:max=> Real.toNNReal (p:ℝ)
local notation "Pr" i:max=> bridgeEstate Y H V G i (C i) (w i)
local notation "Vo" i:max=> coreOs Y H V G i (C i) (w i)
local notation "Os" i:max=> compassKet Y H V G i (C i) (w i)
local notation "D'" i:max=> Domain Y H G false (flank i 0)
local notation "Tx" => timeMesh Λ
local notation "Q" i:max=>Follows Y H V G i (C i) (w i)
local notation "θ" i:max=> flipMark i (tent Y H)
local notation "m₁" => FirstWindows.move (tent Y H)
local notation "ℓ_"=>osValue Y H V G a (C a) χ
open BridgeClub Reflector
namespace Crease
variable (F: BoostBacking Y H V G C a χ)
variable (j z:Axis) (b:j≠z)
open Lens Sail
local notation "Π₀" i:max=> opCarries Y H V G i (C i) (w i)
local notation "L0" => Sight Y H V G C a χ j
local notation "Fz" => (Vo z)
local notation "ζ"=> floor Y H V G C a χ j
local notation "S"=> (S₀ j)
local notation "Ω"=> (Ω₀ j)
variable {U W:Set RSpace} (B:SpaceFor Λ U W)
namespace Shutters
local notation "Φ" i:max=>B.registerQ.low i j
local notation "μ" i:max=> B.registerQ.width i j
local notation "τ" i:max=> (Real.toNNReal (μ i:ℝ))
local notation "Δ"=> (Φ true - (Φ false+μ false))
local notation "δ"=> Real.toNNReal (Δ:ℝ)
local notation "L▬"=>Program Y H V G C a χ j
local notation "〽"=> fast Y H V G C a χ j B
local notation "Ψ"=> pairing Y H V G C a χ j B
local notation "κ" s:max x:max=> ticket Y H G s x
local notation "▽"=>Consigned Y H V G C a χ j B
include F
lemma casts (x:Sky (tent Y H))(i:Bool)(M:Program Y H V G C a χ j)(u: ▽ x i M) (t:ℝ)(n:ℕ): fast Y H V G C a χ j B M i t n ∈ ζ (turf j B t i):= from_price Y H V G C a χ F j _ a (μ i) _ M u.pays.choose_spec.2 t _ n -- arg L
omit F
-- receipt at Domain.Even Vers.B. no WOT asserted without Θ. Use turn cost after booking projection at *same* spatial region.
lemma ordered_prog (r: Registered Y H V G C a χ j) (c:IsCompact U)(d:IsCompact W)(i:Bool) (x:Sky K)(e:x∈ D (duet U W i)): ∃ M, Consigned Y H V G C a χ j B x i M := by
 let k:= slide_pin Y H V G j (duet U W i) (Φ i) x e (μ i) (B.printed j i); let l0:= k.1; let v:= k.2.2; let p:= B.registerQ.positive i j; obtain ⟨A,h⟩:= fits Y H V G j (C j) (w j) _ p _ (domain_mono Y H G v k.1)
 have hj : IsCompact (duet U W i):=by cases i; exact c; exact d
 obtain ⟨M,p⟩:= shout Y H V G C a χ j r _ hj A x _ (Φ i) p e (B.printed j i) h
 exact ⟨M,e,A,h,p⟩
variable (x y : Dome (tent Y H))(s: ℕ)
variable (M P:Program Y H V G C a χ j)
-- accounting product X/Y. packet retains support and comparators; you spend SCRIPT of bounds controlled interior,
-- any payer clock continu gets real pay. M may be any allowed.
structure Pairs : Prop where
 stampL : x∈ insideAt Λ l (tent Y H) false U s
 stampR : y∈ insideAt Λ l (tent Y H) false W s
 runL : ▽ (κ s x) false M
 runR : ▽ (κ s y) true P
local notation "🤍"=>Pairs Y H V G C a χ j B
local notation "ℓ"=>sameRead Y H V G j (C j) (w j) s
local notation "Γ" x:max y:max=> ℓ (x*y)
include F b
lemma judgement (k: Creased Y H V G C a χ F j z b) (p:IsCompact U)(v:IsCompact W) (q:Disjoint U W) (A:Pairs Y H V G C a χ j B x y s M P) :
   ∃ φ:ℕ→ℕ,Tendsto φ atTop atTop∧ Tendsto (fun i=> Ψ M P φ i 1) atTop (𝓝 (Γ x y)):=by
 obtain ⟨A1,h0,HP⟩:= A.runL.pays; obtain ⟨B0,g,t⟩:= A.runR.pays
 let h1:= reads Y H V G C a χ F j z b k U p A1 M (m₁ (eject j (-Φ false)) (κ s x)) (μ false) (shutter_c B false j).le h0 HP
 let h2:= reads Y H V G C a χ F j z b k W v B0 P _ _ (shutter_c B true j).le g t
 obtain ⟨e,w2⟩:= sees_sun Y H V G C a χ F j (κ s x) (κ s y) _ _ _ _ _ _ h0 g (gap j B).le
 have hv : (Γ x y) = inner ℂ Ω ((Π₀ j) A1 ((S).E δ ((Π₀ j) B0 Ω))) := by
   simp only [AddSubgroup.coe_sub,AddSubgroup.coe_add] at w2; unfold sameRead; rw [← w2,os_across Y H V G]; apply congrArg ℓ_; exact Subtype.ext (ticket_separated Y H G A.stampL A.stampR q)
 rw [hv]; exact Lens.can_center S Ω δ _ _ M P h1 h2
omit F
-- η distance in W_L to all W_R, real receipts at ANY λ.
lemma exposure (e:ℝ)(t:∀ x∈ U,∀ y∈ W,x z+e≤ y z) (r:ℝ)(x:E4)(h:x∈ turf j B r false)(y:E4)(p:y∈ turf j B r true): x z +e ≤ y z:= by
 obtain ⟨u,h,x',k0⟩:=on_field j z b B r false x h; obtain ⟨u',v1,y',_⟩:= on_field j z b B r true y p
 rw [x',y']; exact t u h u' v1
end Shutters
end Crease
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
