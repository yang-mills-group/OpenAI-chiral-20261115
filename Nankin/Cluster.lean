import Nankin.Ship
import Taffeta.Stigma
import Rods.Fold
import YM.SU5.FiniteGaugeData.Tower.Baggage
import YM.SU5.FiniteGaugeData.Pannier.FeastDay
set_option autoImplicit false
set_option maxHeartbeats 550000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark
namespace Calico
open Py.Dyad Work.E08 AnalyticBridge.VerifiedReset StressFlux PlaqAxes
open SlabMark
variable {K:Calibration}{f g:Family K}{x y:ℕ→Family K}{S S':Finset Cover}(F:BQueue S x f)(G:BQueue S' y g)
lemma pay_addK{a b:ℝ}(p:pay f a)(h:pay g b):pay (f+g) (a+b):=fun i j=> (norm_add_le ..).trans (add_le_add (p i j) (h i j))
lemma pay_scale(c:ℂ){a b:ℝ}(p:pay f a)(h:‖c‖≤b):pay (c•f) (b*a):= by intro i j; rw [Pi.smul_apply,Pi.smul_apply,norm_smul]; exact mul_le_mul h (p ..) (norm_nonneg _) ((norm_nonneg _).trans h)
include F G
lemma polyplus:BQueue (S∪ S') (fun i=>x i+y i) (f+g):=by
 obtain ⟨t,h,⟨A,B,E,z⟩,u⟩:=F; obtain ⟨t',h',⟨C,D,Q,w⟩,v⟩:=G
 refine ⟨fun i=>((t i).mono subset_union_left).add ((t' i).mono subset_union_right),(h.mono subset_union_left).add (h'.mono subset_union_right),⟨A+C,add_pos B D,pay_addK E Q,(z.and w).mono fun _ ⟨a,b⟩=>pay_addK a b⟩ , fun c p=>?_⟩
 filter_upwards [u _ (half_pos p),v _ (half_pos p)] with i l r
 rw [show x i + y i - (f+g)= x i-f+(y i-g) from by abel, ← add_halves c]; exact pay_addK l r
omit G
lemma polyscale{c:ℕ→ℂ}{b:ℂ}(p:Tendsto c atTop (𝓝 b)) : BQueue S (fun i=>c i • x i) (b•f):=by
 obtain ⟨t,h,⟨A,B,E,z⟩,u⟩:=F; let k:= ‖b‖+1
 have e:= (p.norm).eventually (ge_mem_nhds (show ‖b‖<k from lt_add_of_pos_right _ zero_lt_one)); have v:0<k:=by unfold k; positivity
 refine ⟨fun i=>.smul _ (t _),.smul _ h,⟨k*A,mul_pos v B,pay_scale _ E (le_add_of_nonneg_right zero_le_one),(z.and e).mono fun _ w=>pay_scale _ w.1 w.2⟩,fun a l=>?_⟩
 let d:=a/(2*A); let y:=a/(2*k); have h₁:0<d:=by unfold d; positivity
 have h₂:0<y:=by unfold y; positivity
 filter_upwards [u y h₂,Metric.tendsto_nhds.mp p d h₁,e] with i q p e
 rw [dist_eq_norm] at p
 rw [show c i• x i-b • f=c i • (x i-f)+(c i-b) • f by rw [smul_sub,sub_smul]; abel,←show k*y + d*A=a from ?_]; swap
 · unfold y d; field_simp; ring
 exact pay_addK (pay_scale _ q e) (pay_scale _ E p.le)
-- issue semicolon h₁ positivity no goals
#print axioms polyscale
end Calico
end YM.CF.Buffered.Afterglow.Tower
