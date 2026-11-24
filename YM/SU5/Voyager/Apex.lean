import YM.SU5.Voyager.Locker
import YM.SU5.Aria.SatinRails
set_option maxHeartbeats 250000
set_option maxHeartbeats 250000
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Set
open Cheer (Narrow)
variable (P:Spine)(x:P.Spectrum0 3)(Z:Lead.Clan)(s n:ℕ)(c r:ℕ→ℕ)
open Spectral Caino MeasureTheory.Measure
open Spectral.Orbit.Prairie
abbrev tracks3 : Fin 3 ↪ Axis := Fin.castSuccEmb
lemma axleS (i:Fin 3): tracks3 i ≠ (3:Axis):= by fin_cases i <;> decide
lemma gazed (v : E4): terrain tracks3 v= YM.spatial v:=rfl
local notation "χ"=> P.advocate 3 x 3
local notation "Σ₀"=> (notice 3 x tracks3)
local notation "H₁"=>P.ManyF 3 (P.advocate 3 x 3)
local notation "ϕ" s:max n:max=> P.pathGlow x Z s n
local notation "℘"=> (P.seasons 3 χ).ℚmeasure
local notation "Σ₁"=> (Σ₀).region
local notation "Σ₂"=> (Σ₀).diagonal
local notation "ω"=> P.heaven 3 χ
local notation "D"=> terrain tracks3
variable (b:Fin 3→Bool) (J:P.Ellis 3 x)
def carnivalF(sp s:ℕ): P.Flicker := (P.crownT Z sp s, ⟨P.markX sp,P.book_height sp⟩)
lemma center_pulse : specY x (3:Axis) (P.carnivalF Z s n)= P.pulse0 x Z s n:= (P.entersAt 3 χ (P.crownT Z s n) (P.markX s)).symm
lemma ionV : Σ₂ ω= Measure.dirac (0:Terrain (Fin 3)):=by
 apply ext_of_charFun; funext i
 rw [sealOut 3 x tracks3]; simp only [charFun_dirac,inner_zero_left,Complex.ofReal_zero,zero_mul,Complex.exp_zero]; rw [←rtoc 3 x tracks3 axleS, P.cart_empty,inner_self_eq_norm_sq_to_K, P.stone_norm]; simp -- tune
local notation "U"=>alley b
local notation "μ"=> D ⁻¹' U
private lemma positive_crown : (Mink.inside∩(μ)).Nonempty:=by
 let v:Terrain (Fin 3):= WithLp.toLp 2 (fun i:Fin 3=> if b i then (1:ℝ) else (-1:ℝ)); let w:= YM.position v (‖v‖+1); refine ⟨w,?_,?_⟩
 · change ‖YM.spatial w‖ < YM.time w; unfold w; simp
 change D (YM.position v _ )∈ U; rw [gazed,YM.spatial_position]; intro i; cases hi:b i<;>simp [hi,v]
lemma clears (x:Space3)(h:x∈U): x≠0:=by have ht:=h 0; intro v; cases hi:b 0<;>simp [hi,v] at ht -- tune
lemma blaze_keep (p:ℝ)(q:0<p): Cheer.press p μ ⊆ μ:=by intro v h; change terrain tracks3 (p • v)∈U at h; change terrain tracks3 v∈ U; intro i; have he:=h i; change (if b i then 0< p*v (tracks3 i) else p*v (tracks3 i)<0) at he; change (if b i then 0< v (tracks3 i) else v (tracks3 i)<0); cases hi:b i<;>simp only [hi,Bool.false_eq_true,↓reduceIte, mul_pos_iff_of_pos_left q] at he ⊢<;> first| exact he | nlinarith
lemma nocharge {V:Set Space3}(p:MeasurableSet V)(h:V ⊆ U) : Σ₁ V ω=0:=by apply ((Σ₀).null_pair p _).1; rw [P.ionV x]; rw [Measure.dirac_apply' _ p]; exact indicator_of_notMem (fun g=> (clears b 0 (h g)) rfl) _ -- order
lemma budget_first {T:Set Space3}(p:MeasurableSet T)(h:T ⊆ U): Σ₁ T (P.pulse0 x Z s n)=Σ₁ T (ϕ s n):=by unfold pathGlow; rw [map_sub,map_smul,P.nocharge x b p h, smul_zero, sub_zero]
-- full occupancy equival in octant
lemma territory : Measure.restrict (Σ₂ (ϕ s n)) U= (Σ₂ (P.pulse0 x Z s n)).restrict U:= by
 ext A h
 simp only [Measure.restrict_apply h]; let V:=A∩U; let f:=P.pulse0 x Z s n; let x':=ϕ s n
 have he: MeasurableSet V:=h.inter (alley_open b|>.measurableSet)
 have ht:(Σ₂ x').real V=(Σ₂ f).real V:= ((Σ₀).same he _).trans ((congrArg (fun z:H₁=> ‖z‖^2) (P.budget_first x Z s n b he Set.inter_subset_right).symm).trans (((Σ₀).same he _).symm))
 exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top (Σ₂ x') V) (measure_ne_top (Σ₂ f) V)).1 ht -- match resolution
-- spectra from open Mink-inside. $$ scaling choose. protect all at same index.
local notation "K"=> (P.dew s n)
lemma gaugeGlow (g: ∀ n,0<r n)(T: P.Portrait x Z c r) : ∀ᶠ i:ℕ in atTop, 0<Σ₂ (ϕ (c i) (r i)) U:=by
 have hb:IsOpen μ:=(alley_open b).preimage (terrain_cont tracks3)
 obtain ⟨d,y,p⟩:= T.shines μ hb (positive_crown b)
 refine p.mono fun i w=> ?_; let y':=ϕ (c i) (r i); let ζ:=P.dew (c i) (r i); let Y:= Cheer.press ζ μ; have hp:=P.dew_pos (c i) (g i)
 have hf:(℘).region Y y'≠0:=by intro h; change d<‖(℘).region Y y'‖^2 at w; rw [h] at w; simp at w; linarith -- simp might use y
 have hu : (Σ₂ y') U= (℘).diagonal y' μ:= Measure.map_apply (f:= (terrain tracks3)) (terrain_cont tracks3|>.measurable) (alley_open b|>.measurableSet)
 change 0<(Σ₂ y') U; rw [hu]; exact (show 0<(℘).diagonal y' Y from pos_iff_ne_zero.mpr (mt (((℘).null_pair (Cheer.pressured _ hb.measurableSet) _).1) hf)).trans_le (measure_mono (blaze_keep b ζ hp))
def SailV (s n:ℕ) : Prop:= ∀ b:Fin 3→Bool, let V:= Spectral.Orbit.Prairie.alley b; volume.restrict V ≪ (Σ₂ (ϕ s n)).restrict V ∧ (Σ₂ (ϕ s n)).restrict V ≪ volume.restrict V -- ν binder notation μ puzzle
include J
lemma market_mink(g: ∀ n,0<r n)(T: P.Portrait x Z c r) : ∀ᶠ i in atTop,P.SailV x Z (c i) (r i):=by
 refine eventually_all.mpr ?_ -- tune: output forall
 intro b; let V:=alley b; filter_upwards [P.gaugeGlow x Z c r b g T] with i h; set X':= (ϕ (c i) (r i)); let u:= P.carnivalF Z (c i) (r i); let v:=P.pulse0 x Z (c i) (r i)
 have hx : (Σ₂ X').restrict V=(Σ₂ (specY x (3:Axis) u)).restrict V:= (P.territory x Z (c i) (r i) b).trans (congrArg (fun z:H₁=>(Σ₂ z).restrict V) (P.center_pulse x Z (c i) (r i)).symm)
 change volume.restrict V ≪ (Σ₂ X').restrict V ∧ (Σ₂ X').restrict V ≪ volume.restrict V; rw [hx]
 have hp:(Σ₂ (specY x (3:Axis) u)) V≠0:=fun ht=> h.ne' (Measure.restrict_eq_zero.mp (hx.trans (Measure.restrict_eq_zero.mpr ht)))
 exact ⟨live_bands 3 x J tracks3 axleS u b hp,shine_route 3 x J tracks3 axleS u b⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.market_mink
