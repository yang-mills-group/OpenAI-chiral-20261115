import Velour.Sequins.Foil
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option maxHeartbeats 1250000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set

namespace Spine
open _root_.YM.CF.Buffered.Afterglow.Hierarchy
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.LyraBill.Chiffon.Sesame.FlakeNight
open FirstWindows FirstWindows.Chambers FirstWindows.LightBudget

open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set

open _root_.YM.SatinEdge.RealSheet Boundary Probe

open YM.Velour


variable (P:Spine)(x:P.Spectrum0 3)
local notation "ℒ"=> Lead.Clan
local notation "ξ"=> P.advocate 3 x 3
local notation "ℌ"=> P.ManyF 3 ξ
local notation "S"=> P.seasons 3 ξ
local notation "U"=> (S).unit.translation
variable (V:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))
variable (w:ℒ→ Prism)
local notation "Λ"=> P.profilesZ x V w

/-- Mink real assay in these tests -/
def paycheck {Hy:Hilbert}(Y:ℒ → Test4 →L[ℂ] Hy)(F T:SampleDose):CrossRead:=
 matchRoles Hy (fun i=> Y i (sachet_LocalFieldBounds F)) (fun i=>Y i (sachet_LocalFieldBounds T))

variable (p:∀ i:ℒ,TemperedAtEdge (P.ManyF 3 (P.advocate 3 x 3)) (P.profilesZ x V w i))
variable (q:∀ i:ℒ,Positive (P.seasons 3 (P.advocate 3 x 3)) (P.profilesZ x V w i))
local notation "Y[" i "]"=> _root_.YM.SatinEdge.RealSheet.awake (S) (Λ i) (p i)

def tips(a b:Vantage)(n:ℕ)(z:ℂ):CrossRead:=
 shebang (S) (fun i=> Y[i] (sachet_LocalFieldBounds (velourSampleBead a n))) (fun i=> Y[i] (sachet_LocalFieldBounds (velourSampleBead b n))) z

include q in
lemma tips_at(a b:Vantage)(n:ℕ)(r:ℝ):
 P.tips x V w p a b n r=
 paycheck (fun i=>Y[i]) (velourSampleBead a n) (velourSampleBead (b+foldSpace (r • basis 3)) n):=by
 unfold tips paycheck; rw [shebang_real]; simp_rw [transportation (S) (Λ _) (p _) (q _),bead_ahead]


abbrev coin_LocalFieldBounds(a b:Vantage) : ℂ:= -((b-a) 3:ℂ)+((b-a) 3:ℂ)*Complex.I

include q in
lemma tips_tendsto (a b:Vantage)(h:0<(b-a) 3):
 Tendsto (fun n=> P.tips x V w p a b n (coin_LocalFieldBounds a b)) atTop (𝓝 (P.pointPrism x V w (b-a))):=by
 let c:=(b-a) 3
 let z:=coin_LocalFieldBounds a b
 have v:z.im=c:=by simp [c,z,coin_LocalFieldBounds]
 have r:z.re= -c:=by simp [c,z,coin_LocalFieldBounds]
 let d:ℝ≥0:=(z.im/2).toNNReal
 have u:(d:ℝ)=c/2:=by dsimp only [d]; rw [v,Real.coe_toNNReal _ (half_pos h).le]
 have m:0<d:=NNReal.coe_pos.mp (u.symm ▸ half_pos h)
 have A(g:Vantage)(i:ℒ) :
      Tendsto (fun n=> (S).E d (Y[i] (sachet_LocalFieldBounds (velourSampleBead g n))))
           atTop (𝓝 (U (foldSpace.symm g) (Λ i (c/2)))):=by
   simp_rw [awake_on_axis (S) (Λ i) (p i) (q i) d m,u]
   exact reap_collect (S) _ _
 let e:= z.re • basis 3
 have e': -(foldSpace.symm a) + (e+foldSpace.symm b)=polarBase (b-a):=by
    dsimp only [e]; rw [r,neg_smul,←skew_axis, map_sub]; abel
 refine tendsto_pi_nhds.mpr (fun i=> tendsto_pi_nhds.mpr fun j=> ?_)
 let f(i):=Λ i (c/2)

 have l: inner ℂ (U (foldSpace.symm a) (f i)) (U e (U (foldSpace.symm b) (f j)))=
      P.pointPrism x V w (b-a) i j:=by
   rw [←ContinuousLinearMap.adjoint_inner_right]
   change inner ℂ _ (star (U _) (U e (U _ _)))= inner ℂ (f i) (P.cartage 3 ξ (b-a) (f j))
   rw [(S).unit_star, ←mul_apply_eq_comp (U e), (S).unit_step, ←mul_apply_eq_comp,(S).unit_step,e']
   rw [←P.cart_plank x]
 rw [←l]; exact (A a i).inner (((U e).continuous.tendsto _).comp (A b j))




include q in
lemma spot_net (a b:Vantage)(h:0<(b-a) 3)(d:ReadsSix (P.pointPrism x V w (b-a))):
  ∃ f:ℕ→ Vantage, Tendsto f atTop (𝓝 b) ∧
      ∀ᶠ i:ℕ in atTop, ReadsSix (paycheck (fun i=>Y[i]) (velourSampleBead a i) (velourSampleBead (f i) i)):=by
 let r(i:ℕ):ℝ:=(1/2)^i
 have e(i:ℕ):0<r i:=by dsimp only [r]; positivity
 let O(y):= ReadsSix (P.tips x V w p a b y (coin_LocalFieldBounds a b))
 have g(i:ℕ):∃ t:ℝ, |t|≤r i ∧ (O i→ReadsSix (P.tips x V w p a b i t)):=by
    by_cases m:O i
    · obtain ⟨t,v,j⟩:=shebang_edge (S) _ _ (e i) (show 0<(coin_LocalFieldBounds a b).im from by simpa [coin_LocalFieldBounds] using h) (show ReadsSix (shebang (S) _ _ (coin_LocalFieldBounds a b)) from m)
      exact ⟨t,v,fun _=>j⟩
    exact ⟨0,(abs_zero.trans_le (e i).le), fun h=>(m h).elim⟩
 choose t y k using g
 have r':Tendsto r atTop (𝓝 (0:ℝ)):=tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
 have s:Tendsto t atTop (𝓝 0):=tendsto_zero_iff_norm_tendsto_zero.mpr
   (squeeze_zero (fun i=>norm_nonneg (t i)) (fun i=> (Real.norm_eq_abs _).trans_le (y i)) r')

 refine ⟨fun i=> b+foldSpace (t i • basis 3), ?_, ?_⟩
 · convert ((tendsto_const_nhds (x:=b)).add
     ((foldSpace.continuous.tendsto _).comp
     (s.smul (tendsto_const_nhds (x:=basis 3))))) using 1 <;> simp
 apply ((P.tips_tendsto x V w p q a b h).eventually (readsSix_open.mem_nhds d)).mono
 intro i h'
 rw [←P.tips_at x V w p q a b i (t i)]
 exact k i h'
#print axioms spot_net

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
