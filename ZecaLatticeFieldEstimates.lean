import ZecaMilk
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

section film
variable {U:Hilbert}{I I₀: Type*} {l:Filter I} {k:Filter I₀}
variable {f g:I→U.Op} {T A:U.Op}


-- GlazeRay holds also for adjoints.
structure LatticeFieldEstimates (U:Hilbert){I:Type*}(l:Filter I)(f:I→U.Op)(T:U.Op):Prop where
 val: Glaze_LocalFieldBounds U l f T
 mir: Glaze_LocalFieldBounds U l (fun i=>star (f i)) (star T)
namespace LatticeFieldEstimates
lemma mul (h:LatticeFieldEstimates U l f T)(a:LatticeFieldEstimates U l g A):
 LatticeFieldEstimates U l (fun i=>f i*g i) (T*A):=by
 refine ⟨h.val.mul a.val,?_⟩
 simp only [star_mul]; exact a.mir.mul h.mir
lemma sub (h:LatticeFieldEstimates U l f T)(a:LatticeFieldEstimates U l g A):LatticeFieldEstimates U l (fun i=>f i-g i) (T-A):=by
 refine ⟨h.val.sub a.val,?_⟩
 simp only [star_sub]; exact h.mir.sub a.mir
lemma smul (h:LatticeFieldEstimates U l f T)(v:ℂ): LatticeFieldEstimates U l (fun i=> v • f i) (v • T):=by
 refine ⟨h.val.smul _,?_⟩
 simp only [star_smul]; exact h.mir.smul _
lemma congr' (h:LatticeFieldEstimates U l f T)(p:f=ᶠ[l] g): LatticeFieldEstimates U l g T:=⟨h.val.congr' p,h.mir.congr' (p.mono fun _ v=>congrArg star v)⟩
lemma mend {e:I→ℝ}(h:LatticeFieldEstimates U l f T)(p:Tendsto e l (𝓝 0))(u:∀ᶠ i in l, ‖g i-f i‖≤e i):LatticeFieldEstimates U l g T:=by
 refine ⟨h.val.mend p u,h.mir.mend p ?_⟩
 filter_upwards [u] with i v
 rwa [←star_sub,norm_star]
lemma pops (p:Tendsto f l (𝓝 T)):LatticeFieldEstimates U l f T:=
   ⟨.pops p,.pops (p.star)⟩
lemma const (T:U.Op): LatticeFieldEstimates U l (fun _=>T) T:=pops tendsto_const_nhds
lemma sum {J:Type*}(s:Finset J)(f:J→I→U.Op)(g:J→U.Op)
 (h:∀ j∈s,LatticeFieldEstimates U l (f j) (g j)): LatticeFieldEstimates U l (fun i=>∑ j∈s,f j i) (∑ j∈s,g j):=by
 refine ⟨Glaze_LocalFieldBounds.sum s _ _ (fun j v=>(h j v).val),?_⟩
 simp only [star_sum]
 exact Glaze_LocalFieldBounds.sum s _ _ (fun j v=>(h j v).mir)
lemma heat {a:I→ℝ}{b:ℝ}(ha:Tendsto a l (𝓝 b)):
 LatticeFieldEstimates (P.ManyF j x) l (fun i=> ET (a i).toNNReal) (ET b.toNNReal):=by
 have s: ∀ n, star (ET n)=ET n:=(P.seasons j x).sym
 refine ⟨Glaze_LocalFieldBounds.heat P j x ha,?_⟩
 simp only [s]
 exact Glaze_LocalFieldBounds.heat P j x ha

variable {h:I→ (P.ManyF j x).Op}{z:(P.ManyF j x).Op}

variable {P j x}
lemma buff {a b:I→ℝ}{c d:ℝ}
 (t:LatticeFieldEstimates (P.ManyF j x) l h z)(p:Tendsto a l (𝓝 c))(q:Tendsto b l (𝓝 d)):
 LatticeFieldEstimates (P.ManyF j x) l (fun i=> P.buff j x (a i) (b i) (h i))
     (P.buff j x c d z):=(mul (heat P j x p) t).mul (heat P j x q)

end LatticeFieldEstimates
end film

/-- LatticeFieldEstimates version of NibLine, assuming all σ=1. -/
structure Iguana (P:Spine)(j:Axis)(x:P.Spectrum0 j)(F:P.Nib j x)(Y:ℕ→P.Apron): Prop where
 pay : P.NibPay j x F
 thin : Tendsto (fun i=>(Y i).realWidth P j) atTop (𝓝 0)
 dye : ∀ (a b : ℝ), 0<a→0<b→
       LatticeFieldEstimates (P.ManyF j x) atTop
        (fun i=> P.ruby j x (Y i) 0 a b)
        (F a b)
namespace Iguana
variable {P j x} {F:P.Nib j x} {Y:ℕ→P.Apron}
lemma nib (h:P.Iguana j x F Y):P.NibLine j x F Y 1:=
 ⟨h.pay,h.thin,fun a b p q=>((h.dye a b p q).val.congr' (Eventually.of_forall fun _=> (one_smul ..).symm))⟩
lemma read (h:Iguana P j x F Y) {a b:ℝ} {m n:ℕ→ℝ}
 (p:0<a)(q:0<b)
     (ma:Tendsto m atTop (𝓝 a))(nb:Tendsto n atTop (𝓝 b)):
   LatticeFieldEstimates (P.ManyF j x) atTop
      (fun i=> P.ruby j x (Y i) 0 (m i) (n i)) (F a b):=by
 let i:= a/2
 let o:=b/2
 have e:0 < i:=half_pos p
 have f:0<o:=half_pos q
 have y:i<a:=half_lt_self p
 have g:o<b:=half_lt_self q
 rw [h.nib.bottle.prop e f y.le g.le]
 refine (((h.dye _ _ e f).buff (ma.sub_const i) (nb.sub_const o))).congr' ?_
 filter_upwards [h.nib.fit e f, ma.eventually (le_mem_nhds y),nb.eventually (le_mem_nhds g)] with r ⟨e',f'⟩ s t
 change i≤ m r at s
 change o≤ n r at t
 rw [P.ruby_large _ _ _ _ _ (sub_add_cancel (m r) i) (by linarith only: o+(n r-o)=n r)
                 (sub_nonneg.mpr s) (sub_nonneg.mpr t) e' f']

end Iguana