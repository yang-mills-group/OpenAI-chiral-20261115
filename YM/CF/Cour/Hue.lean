import YM.CF.Cour.Bill
import YM.CF.Esti.Flare
import YM.CF.Cour.Lake
import YM.CF.Pec.Frond
import YM.CF.Skye.Hark
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Cour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Planned.JetPort Push.Uniform
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{n: Side}{C D A a:ℝ}{k:ℕ}
open AnalyticBridge.SectorAffine
section
open scoped Matrix.Norms.Frobenius
private def brow : (SU.F → SU.F→ℂ)→L[ℝ] group.Mat:= LinearMap.toContinuousLinearMap {toFun:=fun x=>x,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl}
def jade :=normL (A:=SU.F→SU.F→ℂ) brow
theorem flat :0 ≤ jade:=normZ (A:=SU.F→SU.F→ℂ) brow
lemma browser(f:E→SU.E)(x:E)(h: Jet.Allows k (fun y i j=> fund (f y) i j) x C): Esti.grantB k f x (jade*C):=h.linear brow le_rfl
lemma payCurve (n:ℕ)(ht:0≤C)(p:0<a):∃ K:ℝ,1≤K∧∀ (b:ℕ) (G:Side)(E:Type)[NormedAddCommGroup E][NormedSpace ℝ E](x:E)(U:E→ Config group G), (∀ i, Esti.grantB n (fun y=>U y i) x C)→∀ (w:Walk), w.length≤8*(b+1) →∀ v, Jet.Allows n (fun y=> group.curvature (travel (U y) v w)) x (K*Real.exp (a*b)):=by
 obtain ⟨K,h,H⟩:=Laic.ventAllow C ht n a p
 let X:= curvatureCost SU.group; refine ⟨max 1 (X*K),le_max_left ..,fun b G E _ _ x U Ht w k v=>?_⟩; apply Jet.Allows.mono
 refine Esti.arc_b (G:=group) (U:=fun y=>group.mat (travel (U y) v w)) ((Esti.trekP G U Ht w v (8*(b+1)) k).mono (H b)); change X*(K*Real.exp _) ≤ _; rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_right ..) (Real.exp_pos ..|>.le)
lemma siltC(x:Site n)(k:Wind n): Continuous (fun u:Config SU.group n=>silt x k u):=group.continuous_curvature.comp (travel_cont x (boot x k))
end
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
lemma jasmine (K:ℝ)(v:0 ≤ K)(p:0<a)(n:ℕ):∃ F:ℝ,1 ≤ F ∧∀ {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{M:Side}(x:E)(U:E→ Bkg M), Jet.TransK n U x K →∀ (v:Site M)(w:Walk)(b:ℕ), w.length ≤ 8*(b+1) → Jet.Allows n (fun y=> group.curvature (travel (U y) v w)) x (F*Real.exp (a*b)):=by
 let D:=coordL (k:=SU.F); obtain ⟨S,h,H⟩:=payCurve n (mul_nonneg flat (mul_nonneg (norm_nonneg D.toContinuousLinearMap) v)) p; refine ⟨S,h,@fun E _ _ M x U p v w b hb=>?_⟩; exact H b M E x U (fun i=> browser (fun y=>U y i) _ ((p i).linear D.toContinuousLinearMap le_rfl)) w hb v
lemma yolk (K:ℝ)(v:0 ≤ K)(p:0<a)(n:ℕ):∃ F:ℝ,1 ≤ F ∧∀ {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{M:Side}(x:E)(U:E→ Bkg (More M)), Jet.TransK n U x K →∀ (s:Shape)(v:Site (More M))(w:Wind _), Jet.Allows n (fun y=> silt v w (Yg s (U y))) x (F*Real.exp (a*dial v w)):=by
 obtain ⟨A,h,H⟩:= jasmine K v p n; refine ⟨A,h,@fun E _ _ M x U p s v w=>?_⟩; unfold silt; simp_rw [← Moire.ray_t s _ _ _]; exact H _ _ p _ _ _ ((Moire.ray_L ..).trans_le (leanB ..))
end YM.CF.Cour
