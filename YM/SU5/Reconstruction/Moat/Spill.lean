import YM.SU5.Reconstruction.Moat.Aspect
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
local notation "X" i:max=> OSvector Y H V G i (C i) (w i)
local notation "θ" i:max=> flipMark i (tent Y H)
local notation "m₁" => FirstWindows.move (tent Y H)
local notation "ℓ_"=>osValue Y H V G a (C a) χ
namespace Reflector
local notation "€" => Fund Y H V G C a χ
variable (j b:Axis)(d:b≠j) -- ≠
-- Spotlight density. positive layout BOTH coords; g in Prop.require r.
variable (r : marks (timeMesh Λ))
def staging (j b:Axis)(u:ℝ):= flank j u ∩ flank b u
include d in
lemma quad (f g : Domain Y H G false (staging j b (r:ℝ)))(p:0<(r:ℝ)) : (θ j) f.val * g.val ∈ Domain Y H G false (flank b (r:ℝ)) := by
 let Qu:= mirrorE j 0 '' staging j b (r:ℝ)
 apply domain_mult_to Y H G (mirror_support Y H G j _ f.property) g.property _ _ inter_subset_right
 · rw [Set.disjoint_left]; rintro x ⟨y,h,rfl⟩ v
   have t:= (show (r:ℝ)≤ y j from h.1); have he:= (show (r:ℝ) ≤ mirrorE j 0 y j from v.1); simp [mirrorE] at he; linarith
 rintro _ ⟨x,h,rfl⟩; change (r:ℝ) ≤ mirrorE j 0 x b; simpa [mirrorE,d] using (show (r:ℝ)≤ x b from h.2)
variable (P: BoostBacking Y H V G C a χ)
-- lemma far with a GAP in a (r positive) also.Don't enlarge Shore
local notation "vW"=>staging j b (r:ℝ)
local notation "Ω" i:max=>doorstep Y H V G.history G.clipped i false (C i) (w i)
abbrev clique (r:marks (timeMesh Λ))(e:0≤(r:ℝ))(x:Domain Y H G false (staging j b (r:ℝ))):= Submodule.inclusion (domain_mono Y H G ((show staging j b _ ⊆ flank j (r:ℝ) from inter_subset_left).trans (TimeMesh.flank_mono j e))) x -- F proof? remove
include P d in
lemma quad_dense (v:0≤(r:ℝ)) : DenseRange (fun x:Domain Y H G false (staging j b (r:ℝ))=> (OSvector Y H V G j (C j) (w j)) (clique Y H G j b r v x)):= by
 let U:=(C₀ j).subtypeL; let E:=(S₀ j).E (ℜ r)
 have hF:=P.present j
 have h:DenseRange U:= Function.Surjective.denseRange (fun x: J₀ j=> ⟨(⟨x,hF.symm ▸ Submodule.mem_top⟩: C₀ j),rfl⟩)
 apply Dense.mono (s₁:= U '' (E '' (far Y H V G j (C j) (w j) b (r:ℝ) true : Set (G₀ j)))) _ (h.dense_image U.continuous (((S₀ j).whole (ℜ r)).dense_image E.continuous (far_dense Y H V G j _ _ b d hF (P.forward j) r true))) -- tune argument order
 rintro _ ⟨_,⟨v₀,H0,rfl⟩,rfl⟩ -- shadow H, V. rename
 obtain ⟨x,h⟩:=LinearMap.mem_range.mp H0; subst v₀
 let D₀:D' j := ⟨x.val,domain_loose Y H G _ (domain_mono Y H G inter_subset_left x.property)⟩
 have he: E ((Vo j) D₀)= E (((compassKet Y H V G j (C j) (w j)).comp (Submodule.inclusion (domain_mono Y H G (show (flank j 0∩ sideLand b r true) ⊆ flank j 0 from inter_subset_left)))) x):=rfl
 obtain ⟨y,e,t⟩:=buoy Y H V G C a χ j hF r v D₀
 have hs:y.val ∈ Domain Y H G false (staging j b r):=by
    rw [e]; apply domain_loose Y H G; apply domain_mono Y H G _ (FirstWindows.moving Y H V G _ _ x.property)
    rintro _ ⟨u,p,rfl⟩; constructor
    · change (r:ℝ) ≤ u j+coordinates Λ (eject j r) j; rw [coordinates_eject,eject_at]; linarith [show 0≤u j from p.1]
    change (r:ℝ)≤ u b+coordinates Λ (eject j r) b; rw [coordinates_eject,eject_away j _ _ d,add_zero]; exact p.2
 refine ⟨⟨_,hs⟩,?_⟩; change (X j) y = U (E _); rw [←he]; change _= U ((S₀ j).E _ ((Vo j) D₀)); rw [← t]; exact (voice_full Y H V G j (C j) (w j) hF y).symm

variable (T: ℕ →(indoor Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))).Op) (W:ℕ→(indoor Y H V G.history G.clipped b false (C b) (displacement Y H V G.history G.clipped a false (C a) χ b (C b))).Op)
 {L:(indoor Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))).Op} {Y₁:(indoor Y H V G.history G.clipped b false (C b) (displacement Y H V G.history G.clipped a false (C a) χ b (C b))).Op}
 (x:ℕ→ Sky (tent Y H))(t:ℕ→ marks (timeMesh Λ))(s: Tendsto (fun i=>(t i:ℝ)) atTop (𝓝 0)) (t₁: ∀ i,Follows Y H V G j (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j)) (x i) (t i) (T i)) (t₂:∀ i, Follows Y H V G b (C b) (displacement Y H V G.history G.clipped a false (C a) χ b (C b)) (x i) (t i) (W i)) (z:Limited atTop T L)(p:Limited atTop W Y₁) {ρ:ℂ}(q:(star Y₁) (doorstep Y H V G.history G.clipped b false (C b) (displacement Y H V G.history G.clipped a false (C a) χ b (C b)))=ρ • doorstep Y H V G.history G.clipped b false (C b) (displacement Y H V G.history G.clipped a false (C a) χ b (C b)))

include z p q d P t₁ t₂ s
lemma coercive (h:0<(r:ℝ)): L = (star ρ) • (1 : (indoor Y H V G.history G.clipped j false (C j) (w j)).Op):= by
 have hv:= quad_dense Y H V G C a χ j b d r P h.le
 ext1 g; apply congrFun (a:=g) (hv.equalizer L.continuous (ContinuousLinearMap.continuous _) _)
 funext y; apply Dense.eq_of_inner_right ℂ hv; rintro _ ⟨iU,rfl⟩
 let f:= clique Y H G j b r h.le iU; let g:= clique Y H G j b r h.le y; let Hf:= P.present j; let Hb:= P.present b
 let A:=(θ j) f.val*g.val; let y':= quad Y H G j b d r iU y h
 let Ag:D' b:= ⟨A,domain_mono Y H G (TimeMesh.flank_mono b h.le) y'⟩; let o:D' b:= ⟨1,domain_one ..⟩
 obtain ⟨F,h0,e⟩:= surroundings Y H V G C a χ j Hf T t s x t₁ z f g r h (domain_mono Y H G inter_subset_left y.property); obtain ⟨F',h1,e'⟩:=surroundings Y H V G C a χ b Hb W t s x t₂ p o Ag r h y'
 have hh:(θ b) o.val=1:= flipMark_unit b
 have he: F=ᶠ[atTop] F':= by
    filter_upwards [h0,h1] with i v u; apply Fund.unique Y H V G C a χ v
    rw [hh,one_mul,show x i*Ag.val=(θ j) f.val*x i*g.val from (by change x i*((θ j) f.val*g.val)=_; ring)] at u; exact u
 have hv:=tendsto_nhds_unique (e.congr' he) e'
 change inner ℂ ((X j) f) (L ((X j) g))= inner ℂ ((X j) f) ((star ρ • (1:(J₀ j).Op)) ((X j) g))
 rw [hv,show (X b) o=(Ω b) from vacuum_ticket ..,← ContinuousLinearMap.adjoint_inner_left Y₁, (show ContinuousLinearMap.adjoint Y₁ (Ω b)=_ from q), inner_smul_left]; change _*_=inner ℂ _ (star ρ • (X j) g); rw [inner_smul_right, expectation Y H V G b,registered_pair,os_across Y H V G a (C a) χ b (C b),os_across Y H V G a (C a) χ j (C j)]; rfl -- os_across orientation sign head
end Reflector
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
