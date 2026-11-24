import YM.SU5.Reconstruction.AnglePath.Dawn
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
local notation "G₁" => Domain Y H G false (aperture P)
local notation "H₀" => Domain Y H G false (northD P)
local notation "U"=> audition Y H V G C a χ P P.a (stocks_a P)
local notation "Z"=> audition Y H V G C a χ P P.b (stocks_b P)
local notation "M"=> motor Y H V G C a χ B S (Oriented.rotateAB P)
local notation "R"=> retina Y H V G C a χ P e B
local notation "K₁"=> profile Y H V G C a χ P W
private lemma mirrorSymmetry {H₁ H₂:Hilbert}{x y:H₁}{z t:H₂}(p:inner ℂ y x=inner ℂ t z):inner ℂ x y=inner ℂ z t:=by rw[←inner_conj_symm,p,inner_conj_symm]
noncomputable def organ: Organ (G₁) (Fs P.a) W.H where
 L:=U
 «R»:=R
 d:=K₁
 pair x y:= mirrorSymmetry (H₁:=Fs P.a) (H₂:=W.H) (view_pair Y H V G C a χ P e B W y x)
 live:= steady_a Y H V G C a χ P B
 vive:= (M).symm.surjective.denseRange.comp (steady_b Y H V G C a χ P B) (M).symm.continuous
 strive:= steady_d Y H V G C a χ P W -- binder order?
local notation "O"=> organ Y H V G C a χ P e B W
variable {L:Hilbert}(Q:Clasp L (fort Y H V G.history G.clipped P.a false (C P.a) (displacement Y H V G.history G.clipped a false (C a) χ P.a (C P.a))) (fort Y H V G.history G.clipped P.a false (C P.a) (displacement Y H V G.history G.clipped a false (C a) χ P.a (C P.a))))(p:(organ Y H V G C a χ P e B W).Pre Q)
lemma lefter (i:Axis) (d:aperture P⊆flank i 0)(x:placement Λ)(f g:G₁)(u:0≤coordinates Λ x i)(v:g.val=move K x f.val)(T:C₀ i=⊤) : (Pr i) x (audition Y H V G C a χ P i d f) = audition Y H V G C a χ P i d g:=by
 let z:= (Submodule.inclusion (domain_mono Y H G d)) f; let v': move K x z.val∈ N i:= v ▸ domain_mono Y H G d g.property -- direction? ⋅▸
 exact ((voice_move Y H V G i _ _ T x z u v').symm.trans (congrArg (V₀ i) (show (⟨move K x z.val,v'⟩:N i)= Submodule.inclusion (domain_mono Y H G d) g from Subtype.ext v.symm)))
local notation "L₀"=> Shank Q (M)
include W p
lemma achieve (x:placement Λ)(u:0≤ coordinates Λ x P.a)(v:0 ≤ coordinates Λ x P.b): (L₀).Pass ((Pr P.a) x) ((Pr P.b) x):=by
 refine (sustainX Q (M) _ _).2 ?_; apply (show Faces U R R U L Q from p).pass
 intro i; let g:G₁:=⟨_,aperture_move Y H V G P i.property x u v⟩
 rw [show (Pr P.a) x (U i) = U g from lefter Y H V G C a χ P P.a (stocks_a P) x i g u rfl (B.present _),LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]; change Q.Latch (U g) ((M).symm ((Pr P.b) x (M ((M).symm (Z i)))))
 rw [LinearIsometryEquiv.apply_symm_apply,show (Pr P.b) x (Z i)=Z g from lefter Y H V G C a χ P P.b (stocks_b P) x i g v rfl (B.present _)]; exact (show Faces U R R U L Q from p).sees g
lemma filament : Picket.Beam P.cross (S₀ P.a) (S₀ P.b) (L₀):= by
 apply Picket.timeBeam P.cross (S₀ P.a) (S₀ P.b) (L₀) (timeMesh Λ); -- explicit
 -- tune
 intro x y u v; let m:= eject P.a x+ eject P.b y; have hf:=(achieve Y H V G C a χ P e B W Q p m (by simpa [m,P.cross.symm] using u) (by simpa [m,P.cross] using v)); unfold m at hf; rw [across_time Y H V G P.a _ _ P.b x y P.cross,add_comm (eject P.a x), across_time Y H V G P.b _ _ P.a y x P.cross.symm] at hf; unfold Picket.argSpace; rw [Real.coe_toNNReal _ v,Real.coe_toNNReal _ u]; exact hf
lemma rights : Picket.Behind (S₀ P.a) (S₀ P.b) (L₀):=by
 apply Picket.priceL (S₀ P.a) (S₀ P.b) (L₀) (timeMesh Λ); intro i f q t
 rw [← castSpace Y H V G C a χ P.a f t,←castSpace Y H V G C a χ P.b q t]; apply achieve Y H V G C a χ P e B W Q p <;> simp [Ne.symm f,Ne.symm q]
lemma exposure {J:Hilbert} (F:Clasp J (Fs P.a) W.H) (q:(O).Core F): (O).Tanning F (S₀ P.a) P.b Q:= by
 have h(x:E4): (M).conjStarAlgEquiv ((℘ P.a) x)=(℘ P.b) (Picket.quarter P.a P.b x):= (allotted Y H V G C a χ B S (Oriented.rotateAB P) x).trans (congrArg (℘ P.b) (tilt_quarter ..))
 have he:=pace Y H V G C a χ B P.a P.b P.cross
 exact ⟨p,q,he, photons Q (M) P.cross _ _ he (pace Y H V G C a χ B P.b P.a P.cross.symm) h (filament Y H V G C a χ P e B W Q p), backGrants Q (M) P.cross (S₀ P.a) (S₀ P.b) h (rights Y H V G C a χ P e B W Q p)⟩
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.WindRose.Emissions
