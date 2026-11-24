import ZecaGem
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
local notation "r"=> D.realWidth P j

local notation "K"=>P.wealth j x
local notation "η"=>P.enter j x
local notation "C"=>P.cartage j x

section film
variable {U:Hilbert}{I I₀: Type*} {l:Filter I} {k:Filter I₀}
variable {f g:I→U.Op} {T A:U.Op}

/-- Strong operator limit with eventually bounded costs. -/
structure Glaze_LocalFieldBounds (U:Hilbert) {I:Type*} (l:Filter I)(f:I→ U.Op)(T:U.Op) : Prop where
 fee:∃ b, 0≤b∧∀ᶠ i in l, ‖f i‖≤b
 seeks:∀ y:U,Tendsto (fun i=>f i y) l (𝓝 (T y))

namespace Glaze_LocalFieldBounds

lemma app (h:Glaze_LocalFieldBounds U l f T){y:I→U}{v:U}(p:Tendsto y l (𝓝 v)):
     Tendsto (fun i=>f i (y i)) l (𝓝 (T v)):=by
 obtain ⟨_,u,t⟩:=h.1
 exact firmly f u t (h.2 v) p
lemma mul (h:Glaze_LocalFieldBounds U l f T)(a:Glaze_LocalFieldBounds U l g A):
      Glaze_LocalFieldBounds U l (fun i=>f i*g i) (T*A):=by
 obtain ⟨c,y,p⟩:=h.fee
 obtain ⟨d,u,q⟩:=a.fee
 exact ⟨⟨_,mul_nonneg y u,(p.and q).mono fun i ⟨s,t⟩=>
         (norm_mul_le ..).trans (mul_le_mul s t (norm_nonneg _) y)⟩, fun v=>h.app (a.seeks v)⟩

lemma congr' (h:Glaze_LocalFieldBounds U l f T)(a:f=ᶠ[l] g):
 Glaze_LocalFieldBounds U l g T:=by
 obtain ⟨c,y,p⟩:=h.fee
 refine ⟨⟨c,y,?_⟩, fun v => (h.seeks v).congr' (a.mono (fun i b=>congrArg (fun S:U.Op=> S v) b))⟩
 filter_upwards [a,p] with i ht ho
 rwa [← ht]
lemma comp (h:Glaze_LocalFieldBounds U l f T){p:I₀→I}(u:Tendsto p k l):
 Glaze_LocalFieldBounds U k (fun i=>f (p i)) T:=by
 obtain ⟨c,y,q⟩:=h.fee
 exact ⟨⟨c,y,u.eventually q⟩,fun v=>(h.seeks v).comp u⟩

lemma pops (pl:Tendsto f l (𝓝 T)):Glaze_LocalFieldBounds U l f T:= by
 refine ⟨⟨‖T‖+1,by positivity,?_⟩, fun y=>?_⟩
 · exact (pl.norm.eventually (ge_mem_nhds (lt_add_one _)))
 exact (((ContinuousLinearMap.apply ℂ U.space y:
                      U.Op →L[ℂ] U.space).continuous.tendsto T).comp pl)
lemma const (a:U.Op):Glaze_LocalFieldBounds U l (fun _=>a) a:=pops tendsto_const_nhds
lemma pays [l.NeBot] {c:ℝ} (h:Glaze_LocalFieldBounds U l f T)(y:0≤c)
    (p:∀ᶠ i in l, ‖f i‖ ≤ c):‖T‖≤c:=
      T.opNorm_le_bound y (fun v=>le_of_tendsto (h.seeks v).norm
              (p.mono fun i a=>(f i).le_of_opNorm_le a v))

lemma unique [l.NeBot] (h:Glaze_LocalFieldBounds U l f T)(p:Glaze_LocalFieldBounds U l f A):T=A:=
 ContinuousLinearMap.ext (fun y=>tendsto_nhds_unique (h.seeks y) (p.seeks y))

lemma heat {a:I→ℝ}{b:ℝ}(ha:Tendsto a l (𝓝 b)):
 Glaze_LocalFieldBounds (P.ManyF j x) l (fun i => ET (a i).toNNReal) (ET b.toNNReal):=
 ⟨⟨1,zero_le_one,Eventually.of_forall fun i=>(P.seasons j x).shrinks _⟩,
  fun y => (((P.seasons j x).continuousE y).comp continuous_real_toNNReal).continuousAt.tendsto.comp ha⟩
lemma cart {a:I→Vantage}{b:Vantage}(ha:Tendsto a l (𝓝 b)):
 Glaze_LocalFieldBounds (P.ManyF j x) l (fun i=> P.cartage j x (a i)) (C b):=
 ⟨⟨1,zero_le_one,Eventually.of_forall fun i=>P.cart_pay j x _⟩,
   fun y => ((P.cart_cont j x y).tendsto b).comp ha⟩

variable {h:I→ (P.ManyF j x).Op}{z:(P.ManyF j x).Op}

variable {P j x}
lemma buff {a b:I→ℝ}{c d:ℝ}
 (t:Glaze_LocalFieldBounds (P.ManyF j x) l h z)(p:Tendsto a l (𝓝 c))(q:Tendsto b l (𝓝 d)):
 Glaze_LocalFieldBounds (P.ManyF j x) l (fun i=> P.buff j x (a i) (b i) (h i))
     (P.buff j x c d z):=(mul (heat P j x p) t).mul (heat P j x q)

lemma dazzle {a:I→Vantage}{b:Vantage}
 (t:Glaze_LocalFieldBounds (P.ManyF j x) l h z)(p:Tendsto a l (𝓝 b)):
 Glaze_LocalFieldBounds (P.ManyF j x) l (fun i=> P.dazzle j x (a i) (h i))
    (P.dazzle j x b z):= (mul (cart P j x p) t).mul (cart P j x p.neg)
end Glaze_LocalFieldBounds

end film
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
