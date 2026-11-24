import ZecaGlaze
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
variable (P: Spine) (j:Axis) (x:P.Spectrum0 j)
open Aria Set TopologicalSpace Metric
local notation "Λ"=> P.par
local notation "κ"=> P.calibration
local notation "ℓ"=> (κ).ℓ
local notation "R"=> ruler P.par.block
local notation "Μ"=> timeMesh P.par
local notation "N"=> notch (timeMesh P.par)
local notation "Γ"=> marks (timeMesh P.par)
local notation "H"=> P.large
local notation "Y₀"=> P.run
local notation "Φ" => P.colorSpace j x
local notation "X"=> P.ColorHil j x

local notation "E"=> (P.physicalEnergy j x).E

variable (D:P.Apron)
local notation "ET" => (P.seasons j x).E
local notation "G" => P.ManyF j x

local notation "K"=>P.wealth j x
local notation "η"=>P.enter j x
local notation "C"=>P.cartage j x


/-- Price family in the physical G-space for both strictly positive pads.
Other arguments meaningless, not boundary values. -/
abbrev Nib := ℝ→ℝ→(P.ManyF j x).Op
variable (F:P.Nib j x)
/-- power heat bound. -/
def NibPay : Prop :=
 ∃ (B:ℝ)(d:ℕ),0<B ∧ ∀ t:ℝ,0<t→t≤1→‖F t t‖≤ B/t^d
/-- coherent price. -/
structure Bottle : Prop where
 pay : P.NibPay j x F
 prop {a b c d:ℝ} : 0<a→0<b→a ≤ c → b ≤ d → F c d=P.buff j x (c-a) (d-b) (F a b)

/-- Obtained as thin prices with normalization σ. -/
structure NibLine (P:Spine)(j:Axis)(x:P.Spectrum0 j)(F:P.Nib j x)
      (Y:ℕ→P.Apron)(σ:ℕ→ℂ):Prop where
 pay : P.NibPay j x F
 thin : Tendsto (fun i=>(Y i).realWidth P j) atTop (𝓝 0)
 dye : ∀ (a b : ℝ), 0<a→0<b→
       Glaze_LocalFieldBounds (P.ManyF j x) atTop
        (fun i=> σ i • P.ruby j x (Y i) 0 a b)
        (F a b)

variable {P j x F} {Y:ℕ→P.Apron}{σ:ℕ→ℂ}

namespace NibLine

lemma fit (h:NibLine P j x F Y σ){a b:ℝ}(p:0<a)(q:0<b):
 ∀ᶠ i in atTop,(Y i).realWidth P j ≤ a ∧ (Y i).realWidth P j ≤ b:=
   h.thin.eventually (ge_mem_nhds p) |>.and (h.thin.eventually (ge_mem_nhds q))

lemma bottle (h:NibLine P j x F Y σ):P.Bottle j x F:=by
 refine ⟨h.pay,?_⟩
 intro a b c d p q e f
 have m := (h.dye a b p q).buff (tendsto_const_nhds (x:=c-a)) (tendsto_const_nhds (x:=d-b))
 refine (h.dye c d (p.trans_le e) (q.trans_le f)).unique (m.congr' ?_)
 filter_upwards [h.fit p q] with i ⟨v,w⟩
 exact (map_smul ..).trans (congrArg (σ i • ·)
       (P.ruby_large _ _ _ (c-a) (d-b) (sub_add_cancel ..) (add_sub_cancel ..) -- a+(b-a)? add_sub_cancel
              (sub_nonneg.mpr e) (sub_nonneg.mpr f) v w _))

/-- all positive pad limits even with varying pads and poses -/
lemma read (h:NibLine P j x F Y σ) {a b:ℝ} {m n:ℕ→ℝ}
     {c:ℕ→Vantage} {d:Vantage}(p:0<a)(q:0<b)
     (ma:Tendsto m atTop (𝓝 a))(nb:Tendsto n atTop (𝓝 b))
     (cd:Tendsto c atTop (𝓝 d)):
   Glaze_LocalFieldBounds (P.ManyF j x) atTop
      (fun i=> σ i • P.ruby j x (Y i) (c i) (m i) (n i)) (P.dazzle j x d (F a b)):=by
 let i:= a/2
 let o:=b/2
 have e:0 < i:=half_pos p
 have f:0<o:=half_pos q
 have y:i<a:=half_lt_self p
 have g:o<b:=half_lt_self q
 rw [h.bottle.prop e f y.le g.le]
 refine (((h.dye _ _ e f).buff (ma.sub_const i) (nb.sub_const o)).dazzle cd).congr' ?_
 filter_upwards [h.fit e f, ma.eventually (le_mem_nhds y),nb.eventually (le_mem_nhds g)] with r ⟨e',f'⟩ s t
 change i≤ m r at s
 change o≤ n r at t
 rw [map_smul,map_smul,P.ruby_large _ _ _ _ _ (sub_add_cancel (m r) i) (by linarith only: o+(n r-o)=n r)
                 (sub_nonneg.mpr s) (sub_nonneg.mpr t) e' f',P.ruby_turn,add_zero]

lemma dyeOne (h:NibLine P j x F Y 1) {a b:ℝ}(p:0<a)(q:0<b):
   Glaze_LocalFieldBounds (P.ManyF j x) atTop (fun i=> P.ruby j x (Y i) 0 a b) (F a b):=
 (h.dye a b p q).congr' (Eventually.of_forall fun _=>one_smul ..)
end NibLine

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
