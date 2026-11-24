import ZecaKestrel
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition
variable (P:Spine)(R : P.Register)(j:Axis)
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "W"=> P.calibration
local notation "ℓ"=> P.calibration.ℓ
open Papal Regis.Head Gleam
/-! # Price of ensemble-of-trips. Exactly composed on printed test level before estimation. -/
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
variable {s t f r v i k:ℕ}
local notation "Λ"=> P.par
/-! # Buy height and travel together. Keep both actual calibration and rank resolution schedule. -/
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
open Worth Pays CF.BProof
open Real (log)
open Aria Casting MacroGrid
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)

local notation "z'"=> Yoke.witnessZ
local notation "κ"=>P.sidesPerTick
local notation "κz"=> (P.sidesPerTick:ℤ)

variable (x : P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "M"=> P.ColorHil 3 (ξ)
local notation "G"=> P.ManyF 3 (ξ)
local notation "Ω"=> P.colorZero 3 ξ
local notation "Γ"=>P.cartage 3 ξ
local notation "Η"=>P.seasons 3 ξ
local notation "π"=>P.wealth 3 ξ
local notation "Πγ"=>P.enter 3 ξ
local notation "ω"=> P.heaven 3 ξ
open Regis.Circuit -- Aster




-- asymptotic comparison lemma reusable
section
variable {U:Hilbert}
  {y z:ℕ→U}
abbrev Neighbor (y z:ℕ→U):Prop:=
 Tendsto (fun i=>‖y i-z i‖) atTop (𝓝 0)
local infixl:50 "≈z"=>Neighbor
lemma Neighbor.trans {w:ℕ→U} (p:y ≈z z)(q:z ≈z w):y ≈z w:=by
 have h:=p.add q
 rw [zero_add] at h
 exact squeeze_zero (fun _=>norm_nonneg _) (fun _=> norm_sub_le_norm_sub_add_norm_sub ..) h
lemma Neighbor.bounded{B:ℝ}(p:y ≈z z)(q:∀ᶠ i in atTop,‖z i‖≤B):
 ∀ᶠ i in atTop, ‖y i‖≤ 1+B:=by
 filter_upwards [p.eventually (ge_mem_nhds zero_lt_one),q] with i v u
 exact (norm_le_norm_sub_add _ _).trans (add_le_add v u)

lemma Neighbor.pairs {a:ℂ} {y₁ z₁:ℕ→U}
 (p:y ≈z z)(p₁:y₁ ≈z z₁)
 {B C:ℝ}(q:∀ᶠ i in atTop,‖z i‖≤B)(q₁:∀ᶠ i in atTop,‖z₁ i‖≤C)
 (h:Tendsto (fun i=>inner ℂ (z i) (z₁ i)) atTop (𝓝 a)):
 Tendsto (fun i=>inner ℂ (y i) (y₁ i)) atTop (𝓝 a):= by
 let d i:=y i-z i
 let e i:=y₁ i-z₁ i
 have g:= (p.mul_const (1+C))
 have j:=p₁.const_mul B
 rw [zero_mul] at g
 rw [mul_zero] at j
 have m:Tendsto (fun i=>inner ℂ (d i) (y₁ i)) atTop (𝓝 0):=by
   refine tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall (fun _=>norm_nonneg _)) ?_ g)
   filter_upwards [p₁.bounded q₁] with i t
   exact (norm_inner_le_norm ..).trans (mul_le_mul_of_nonneg_left t (norm_nonneg _))
 have n:Tendsto (fun i=>inner ℂ (z i) (e i)) atTop (𝓝 0):=by
   refine tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall (fun _=>norm_nonneg _)) ?_ j)
   filter_upwards [q] with i t
   exact (norm_inner_le_norm ..).trans (mul_le_mul_of_nonneg_right t (norm_nonneg _))
 have ht:=m.add (n.add h)
 rw [zero_add,zero_add] at ht
 refine ht.congr fun i=>?_
 unfold d e
 rw [inner_sub_left,inner_sub_right]; abel
end

-- physical quote system
-- T cutoff; later choose pose normalization absorbing T
abbrev roof : ℕ := 8+P.roseFlat

variable (f)(F:P.Nib 3 (P.advocate 3 x 3))(c:ℕ→ℂ)

def Loft(seq:ℕ→ℕ) : Prop:=
 P.Bottle 3 (P.advocate 3 x 3) F ∧
 ∀ (p:Plume_LocalFieldBounds),P.roof≤p.tar→
 Neighbor (P.kestrelTilt x F c p f ∘ seq) (fun i=>P.plover x f (seq i) p)
def aboveRoof(p:Plume_LocalFieldBounds):Prop:= (P.roof:ℝ)+2≤p.tar
def Mach (seq:ℕ→ℕ):Prop:=
 ∀ p q:Plume_LocalFieldBounds,P.aboveRoof p → P.aboveRoof q →
  Tendsto (fun i=>inner ℂ (P.kestrel x F c p (seq i)) (P.kestrel x F c q (seq i)))
     atTop (𝓝 (lyric p q))

variable {P f x F c}
 (W₀:5∣P.par.R.L.val)(J:P.Ellis 3 x)
 {seq:ℕ→ℕ}(T:P.Nepenthe seq x)
 (h:P.Loft f x F c seq)
include W₀ J T h
lemma tern_comparison(p:Plume_LocalFieldBounds)(hp:P.aboveRoof p):
 Neighbor
   (P.kestrel x F c p ∘ seq) (fun i=> P.plover x f (seq i) p):=by
 let a:Plume_LocalFieldBounds:=⟨0,fun _ => (P.roof:ℤ), by
   exact Int.natCast_pos.mpr (show 0<P.roof by unfold roof; omega)⟩
 have ha:a.tar=P.roof:=by
    change (↑(↑(P.roof):ℤ):ℝ)/5^(0:ℕ)=(P.roof:ℝ)
    rw [pow_zero,div_one,Int.cast_natCast]
 have d:a.tar+2≤p.tar:=ha.symm ▸ hp -- hp aboveRoof
 obtain ⟨B,e⟩:=fam_gramBound (P.plover_gram (f:=f) x a a W₀ T J)
 refine Neighbor.trans (z:=P.kestrelTilt x F c p f ∘ seq) ?_
    (h.2 p (by unfold aboveRoof at hp; linarith only [hp]))
 exact P.detilted x F c h.1 p a d T.sky
    ((h.2 a ha.ge).bounded e)
lemma mach : P.Mach x F c seq:= by
 intro p q u v
 obtain ⟨B,e⟩:=fam_gramBound (P.plover_gram (f:=f) x p p W₀ T J)
 obtain ⟨C,y⟩:=fam_gramBound (P.plover_gram (f:=f) x q q W₀ T J)
 exact Neighbor.pairs (tern_comparison W₀ J T h p u)
    (tern_comparison W₀ J T h q v) e y (P.plover_gram x p q W₀ T J)
#print Loft
#print axioms Spine.mach
