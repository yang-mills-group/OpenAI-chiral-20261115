import YM.SU5.Reconstruction.UVPrice.Void
import YM.SU5.Reconstruction.UVPrice.Root
/-!
# Optional soft stamp prices in the actual physical law. Build helpers.
-/
set_option autoImplicit false
set_option maxHeartbeats 300000
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
open Roy
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
local notation "θ" i:max=> flipMark i (tent Y H)
local notation "F₀"=> osValue Y H V G a (C a) χ
variable (j j' : Axis) (hv:j'≠j)
local notation "N" i:max => flank i 0
local notation "L" i:max=> lowland i 0
local notation "Φ"=> move (tent Y H)
variable (p : ∀ j, saunters Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))=⊤)
variable {Pan:Panel Y H V G.history G.clipped a false (C a)}
-- include C binding
variable (Hp:Issued Y H V G.history G.clipped a false (C a) Pan) (Room:Arena Y H G.history.circuit j 0 false)
local notation "Z₀"=> Pan.character
local notation "A'"=> displayAlgebra Y H V G.history G.clipped a false (C a)
local notation "Qg"=> D Set.univ
local notation "Zu" f:max i:max=> osValue Y H V G i (C i) (displacement Y H V G.history G.clipped a false (C a) f i (C i))
include Hp
lemma aContinu (x:Qg): Integrable (fun i=> osValue Y H V G a (C a) (Z₀ i) x) Pan.μ:= by
 haveI:= Hp.normalized
 obtain ⟨s,f,rfl⟩:= (eventually_enclosed Y H G x).exists
 simp_rw [os_enclose]
 have t :=Hp.weak (located Y H V s G.history G.clipped a false (C a) (asLoose K f.val))
 exact t.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) -- notation ψ?
lemma reIssu (x:Qg) :
    (∫ i, (osValue Y H V G a (C a) (Z₀ i) x).re ∂Pan.μ)= (courseValue Y H V G x).re:=by rw [←mixture Y H V G a (C a) Pan Hp]; exact integral_re (aContinu Y H V G C a Hp x)
variable {r e:ℝ}(u : 0≤r)
include u Hp
lemma roster (ht:∀ᵐ i∂Pan.μ, Purchases Y H V G C a (Z₀ i) r) (u': 0≤e)(δ : ℝ) : FirstShot Y H V G j e δ:=by
 intro z hz f k x y
 let Ht(g:Qg)(i:Pan.X):=osValue Y H V G a (C a) (Z₀ i) g
 let X:=(⟨_,x⟩:Qg); let U:=(⟨_,y⟩:Qg)
 -- lots inference. t
 rw [←reIssu Y H V G C a Hp, ←reIssu Y H V G C a Hp]
 apply integral_mono_ae (aContinu Y H V G C a Hp _|>.re) (aContinu Y H V G C a Hp _|>.re)
 filter_upwards [ht,full_house Y H V G.history G.clipped a false (C a) Pan Hp C] with i h b -- tune order
 let v: FullWins Y H V G C a (Z₀ i):=b.2; let A'0:=(genuine_little Y H V G C a (Z₀ i) v u).2 h
 have he:= (true_spectrum Y H V G j (C j) _ u' (hz.1.trans hz.2.2)).2 (show _ from And.intro (A'0.present j) (A'0.forward j)) z hz f k x y -- tune
 rw [os_across] at he; exact he
lemma initial_cut (d:∀ j e,FirstShot Y H V G j r e): RootSmall Y H V G r:=by
 intro j e t; haveI:=Hp.normalized; haveI:= nonempty_of_isProbabilityMeasure Pan.μ; refine ⟨1,zero_lt_one,fun i g z h v f p r₁ r₂ r₃=>?_⟩; let hu:= Picket.starch (mainsea Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) (Z₀ (Classical.arbitrary _)) j (C j))) ⟨i,g⟩ z h v -- Pan.X inhabited? replace choose χ param
 have hz:= d j 1 (Picket.byStamp j i z) hu f p r₁ r₂
 rw [preshot Y H V G j (C j) f (domain_loose Y H G _ (domain_mono Y H G (TimeMesh.flank_mono j u) p)) r₃]; exact hz.trans (le_add_of_nonneg_right (show 0≤ e * _ from by positivity))
-- can combine all. Opt
lemma oversight : RootSmall Y H V G r ↔ ∀ f : A' →⋆ₐ[ℂ] ℂ, BoostBacking Y H V G C a f := by
 constructor
 · intro h f; have hp : ∀ᵐ i∂ Pan.μ, Purchases Y H V G C a (Pan.character i) r:= Eventually.of_forall fun i j δ z=> (h j δ z).imp fun e ⟨b,p⟩=> ⟨b,root_softens Y H V G j (C j) (displacement Y H V G.history G.clipped a false (C a) (Z₀ i) j (C j)) u p u⟩
   refine (real_boost_purchase Y H V G C a f u zero_lt_one).1 ⟨fun j=>twoShotPays Y H V G j (C j) (displacement Y H V G.history G.clipped a false (C a) f j (C j)) (first_suffices Y H V G j (C j) _ u (roster Y H V G C a j Hp u hp u 1) u)⟩
 intro h; apply initial_cut Y H V G C a Hp u; intro j; exact roster Y H V G C a j Hp u (Eventually.of_forall fun i=>fewer Y H V G C a (Z₀ i) u (h _)) u -- tune
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
