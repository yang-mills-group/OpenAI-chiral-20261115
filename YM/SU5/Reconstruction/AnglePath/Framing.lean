import YM.SU5.Reconstruction.Oblique.Announcer
import YM.SU5.Reconstruction.AnglePath.Bridge
/-! # angular prices on this law CP. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.WindRose.Emissions
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
variable (C : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (a:Axis)
variable (χ : displayAlgebra Y H V G.history G.clipped a false (C a) →⋆ₐ[ℂ] ℂ)
local notation "wk" i:max=> displacement Y H V G.history G.clipped a false (C a) χ i (C i)
local notation "J₀" i:max=> indoor Y H V G.history G.clipped i false (C i) (wk i)
local notation "C₀" i:max=> saunters Y H V G.history G.clipped i false (C i) (wk i)
local notation "U₀" i:max=> mainsea Y H V G.history G.clipped i false (C i) (wk i)
local notation "A₀" i:max=> ride Y H V G.history G.clipped i false (C i) (wk i)
local notation "S₀" i:max=> peninsula Y H V G.history G.clipped i false (C i) (wk i)
local notation "Os" i:max=> OSvector Y H V G i (C i) (wk i)
local notation "θ" i:max=> flipMark i (tent Y H)
local notation "ℜ" t:max=> Real.toNNReal (t:ℝ)
open Stormwatch ConePrice Germ SelectionAnalysis CrossedFrame
open YM.ConePrice.Storm
local notation "µ" => Domain Y H G false Set.univ
local notation "Gt" => marks (timeMesh Λ)
local notation "Ω" =>whiff Y H V G C a χ
local notation "au"=>move K
open LightBudget Chambers -- provide BootBacking later
local notation "Fs" i:max=> fort Y H V G.history G.clipped i false (C i) (wk i)
local notation "N" i:max=>Domain Y H G false (flank i 0)
local notation "V₀" i:max=>coreOs Y H V G i (C i) (wk i)
local notation "X₀" i:max=> vocation Y H V G.history G.clipped i false (C i) (wk i)
local notation "Pr" i:max=> bridgeEstate Y H V G i (C i) (wk i)
local notation "℘" i:max=>Picket.trans (S₀ i)
local notation "Qv" i:max=> Follows Y H V G i (C i) (wk i)
local notation "π" i:max=> opCarries Y H V G i (C i) (wk i)
variable (P:Ramp)(e:RPos Y H V G P C a χ)(B:BoostBacking Y H V G C a χ)(W:Chat Y H V G P C a χ)
open CrossedFrame.Cardio _root_.YM.ConePrice.Storm.StepVoucher
local notation "S"=> SpinOn Y H V G C a χ P e
noncomputable def aperture (P:Ramp): Set RSpace:= (flank P.a 0∩flank P.b 0) ∩ northD P
local notation "G₁" => Domain Y H G false (aperture P)
local notation "H₀" =>Domain Y H G false (northD P)
lemma stocks_a: (aperture P)⊆flank P.a 0:= Set.Subset.trans Set.inter_subset_left Set.inter_subset_left
lemma stocks_b: aperture P⊆flank P.b 0:= Set.Subset.trans Set.inter_subset_left Set.inter_subset_right
noncomputable def forwardG: (G₁)→ₗ[ℂ] (H₀):= Submodule.inclusion (domain_mono Y H G inter_subset_right)
noncomputable def audition (x:Axis)(e: aperture P⊆flank x 0): (G₁)→ₗ[ℂ] (Fs x):= (V₀ x).comp (Submodule.inclusion (domain_mono Y H G e))
local notation "U"=> audition Y H V G C a χ P P.a (stocks_a P)
local notation "Z"=> audition Y H V G C a χ P P.b (stocks_b P)
local notation "M"=> motor Y H V G C a χ B S (Oriented.rotateAB P)
noncomputable def retina: G₁→ₗ[ℂ] Fs P.a:= ((M).symm.toLinearEquiv.toLinearMap).comp Z
local notation "R"=> retina Y H V G C a χ P e B
noncomputable def profile: G₁→ₗ[ℂ] W.H:= (footpath (fanoForm Y H V G P C a χ) W).comp (Submodule.inclusion (domain_mono Y H G inter_subset_right))
local notation "K₁"=> profile Y H V G C a χ P W
---------- polarized metrics in this very voter -----------
lemma view_pair (x y:G₁): inner ℂ (R x) (U y)=inner ℂ (K₁ x) (K₁ y):=by
 let Xa:= (⟨y.val,domain_mono Y H G (stocks_a P) y.property⟩:N P.a); let Xb:= (⟨x.val,domain_mono Y H G (stocks_b P) x.property⟩:N P.b)
 let A:=ferryN Y H V G C a χ S (Oriented.rotateAB P)
 obtain ⟨z,hz⟩:=A.surjective Xb
 have hX:x.val=(S).shift z.val:= congrArg Subtype.val hz.symm
 have hx: flipMark P.a K z.val=gust P K x.val:=by rw [hX]; change _= gust P K (gust P K _); rw [gust_square]; rfl
 have ha:R x=(V₀ P.a) z:= by
    apply (M).injective; change M ((M).symm ((V₀ P.b) _))= _; rw [LinearIsometryEquiv.apply_symm_apply]; exact (motoring Y H V G C a χ B S (Oriented.rotateAB P) z Xb hX).symm
 rw [ha]; let X₁:= forwardG Y H G P x; let X₂:=forwardG Y H G P y
 have hp: inner ℂ (W.plant X₁) (W.plant X₂)= whiff Y H V G C a χ (gust P K x.val*y.val):=guide Y H V G P C a χ W X₁ X₂
 change inner ℂ ((V₀ P.a) z) ((V₀ P.a) Xa)=inner ℂ (W.plant X₁) (W.plant X₂)
 have g:= leg_comp Y H V G C a χ B P.a z Xa
 exact g.trans ((congrArg (fun x₁=> whiff Y H V G C a χ (x₁*y.val)) hx).trans hp.symm)
-- ensure no restricted V misuse.W.Card.
local notation "Wk"=> bridgeEstate Y H V G
include B in
lemma pace (x y:Axis)(v:y≠x): Picket.Paces y (S₀ x):= (LightBudget.grants Y H V G x (C x) (wk x) (le_refl 0) (zero_lt_one) (((real_boost_purchase Y H V G C a χ (le_refl 0) zero_lt_one).2 B).purchases x)).2 y v
include B
lemma steady_a : DenseRange U:= by
 apply (picked_far Y H V G P.a (C P.a) (wk P.a) P.b P.cross (B.present P.a) (pace Y H V G C a χ B P.a P.b P.cross) 1 true).mono; rintro _ ⟨x,rfl⟩
 have he : flank P.a 0∩flank P.b 1 ⊆ aperture P:=by rintro t ⟨m,v⟩; change 0≤t P.a at m; change 1≤t P.b at v; exact ⟨⟨m,(show 0≤t P.b from zero_le_one.trans v)⟩,(show 0<t P.a+t P.b from (by linarith))⟩
 exact ⟨Submodule.inclusion (le_trans (domain_loose Y H G _) (domain_mono Y H G he)) x,rfl⟩ -- tune types
lemma steady_b : DenseRange Z:= by
 apply (picked_far Y H V G P.b (C P.b) (wk P.b) P.a P.cross.symm (B.present P.b) (pace Y H V G C a χ B P.b P.a P.cross.symm) 1 true).mono; rintro _ ⟨x,rfl⟩
 have he : flank P.b 0∩flank P.a 1 ⊆ aperture P:=by rintro t ⟨m,v⟩; change 0≤t P.b at m; change 1≤t P.a at v; exact ⟨⟨(show 0≤t P.a from zero_le_one.trans v),m⟩,(show 0<t P.a+t P.b from (by linarith))⟩
 exact ⟨Submodule.inclusion (le_trans (domain_loose Y H G _) (domain_mono Y H G he)) x,rfl⟩
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.WindRose.Emissions
