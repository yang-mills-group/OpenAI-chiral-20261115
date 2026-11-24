import ZecaGem
import SatinThinCanvas
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



variable {a b:ℝ}{n m:ℕ}
local notation "t" => bell Μ n m
lemma fired_ball(p:D.s≤n)(h:D.realWidth P j ≤ bell Μ n m):
 P.Fired j x n (m+m) (P.shifts j m (D.full P n))
  (P.innerCut j x D t t (D.engine P j x)):=by
 rw [←D.zoom_bell P j n p,bell_le] at h -- rw bell_le exact?
 have e:= D.fired_spot P j x (w:=m+m) p m h
       (show (m:ℤ)+D.zoom P n j≤ ↑(m+m) from by omega)
 rwa [Nat.cast_add, bell_add,add_sub_cancel_right] at e

open BigOperators
variable {I:Type}
lemma ruby_exact (A:I→P.Apron)(Z:Finset I) (c:I→ℂ)
  (p:D.s=n)(h:D.F=∑ i∈Z, c i • (A i).full P n)
  (v:∀ i∈Z,(A i).s ≤ n)
  (d:∀ i∈Z,(A i).realWidth P j ≤ D.realWidth P j)
  (e:D.realWidth P j≤a)(f:D.realWidth P j ≤ b):
 P.ruby j x D 0 a b = ∑ i∈Z,c i • P.ruby j x (A i) 0 a b:=by
 let k:= D.u j
 let w:=D.realWidth P j
 have T₀:w=bell Μ n k:=by unfold w Apron.realWidth;rw [p]

 let B(y:P.Apron):=P.innerCut j x y w w (y.engine P j x)
 have link(y:P.Apron)(h₁:y.s≤n)(g:y.realWidth P j≤w):
    P.Fired j x n (k+k) (P.shifts j k (y.full P n)) (B y):=by
    unfold B; rw [T₀];exact P.fired_ball _ _ _ h₁ (g.trans_eq T₀)

 let Hq:=fun i=>P.shifts j k ((A i).full P n)
 have hs:P.Fired j x n (k+k)
     (∑ i∈ Z,c i • Hq i)
     (∑ i∈ Z,c i • B (A i)):=
   Fired.sum (add_pos (D.pos j) (D.pos j)) _ _ _ (fun i he=> (link _ (v i he) (d i he)).smul _)
 have hx: D.full P n=D.F:=by rw [←p,Apron.full,Nat.sub_self];rfl
 have e₁:P.shifts j k (D.full P n)=∑ i∈ Z,c i • Hq i:=by
   rw [hx,h,map_sum];exact sum_congr rfl fun i _=>map_smul ..
 have hb:B D=∑ i∈ Z,c i • B (A i):=by rw [←e₁] at hs;exact (link D p.le le_rfl).unique hs

 let U:= (P.buff j x (a-w) (b-w)).comp (P.coffer j x)
 have p1(y:P.Apron)(g:y.realWidth P j≤w): U (B y)=P.ruby j x y 0 a b:=by
   unfold U B; rw [LinearMap.comp_apply,P.coffer_innerCut]
   exact P.ruby_large _ _ _ _ _ (sub_add_cancel ..) (add_sub_cancel ..) (sub_nonneg.mpr e)
       (sub_nonneg.mpr f) g g _

 rw [←p1 D le_rfl,hb,map_sum]
 exact sum_congr rfl fun i r=>(map_smul ..).trans (congrArg _ (p1 _ (d i r)))

variable {ι : Type} (A:ι→ P.Apron) (Z:Finset ι)(h:Axis→ℕ)(s:ℕ)
variable (u:∀ j,0< h j) (t':∀ i∈Z,(A i).s ≤ s) (f:∀ i∈ Z,∀ j,(A i).zoom P s j ≤ h j)
lemma pivot_ruby_exact (R:ι→ℝ)(l:List Axis)(r r':ℝ)(d:bell Μ s (h j) ≤ r)(q:bell Μ s (h j) ≤ r'):
    P.ruby j x ((P.canvas A Z h s u t' f (fun i=>(R i:ℂ))).pivot P l) 0 r r'=∑ i∈ Z,(R i:ℂ) • P.ruby j x ((A i).pivot P l) 0 r r':=by
 let B:=P.canvas A Z h s u t' f (fun i=>(R i:ℂ)); let i'(i:ι):=(A i).pivot P l; have he: (B.pivot P l).realWidth P j=bell Μ s (h j):= B.pivot_w j P l -- order
 refine P.ruby_exact j x (B.pivot P l) i' Z _ (B.pivot_s P l)
        (P.reflectorSum A Z h s u t' f ..)
        (fun i v=> by rw [show (i' i).s=(A i).s from (A i).pivot_s P l]; exact t' i v)
        (fun i v=>?_) (he.le.trans d) (he.le.trans q)
 unfold i'; change _≤(B.pivot P l).realWidth P j; rw [Apron.pivot_w, he]; exact (P.zoom_check j s (h j) (A i) (t' i v)).mp (f i v j)


end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
