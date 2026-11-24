import YM.CF.Cloak.Cap
import YM.CF.Rill.Oboe
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Cloak
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree Esti
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD
open Ac
variable {c f:Side}(S:StepData c f){r v:ℕ}
open CF.Jet
local notation "G"=> SU.group
variable {S}{n:ℕ}{θ a b m x t w K C d:ℝ}
variable {K': Teller G}{A B:Stores S}{T:Tube G S}{V:Config G c}{U:Config G f}{k:S.Choices}{q:Chi}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Nonempty E]{x':E}
open AnalyticBridge.Annulus1AD Push.SectorMeasure.Oriented Pressure.Tube
variable {O:Stores S}{F: Forest S.ratio}{Y:LinkArray G (Frozen A x F)}{z:LogArray G (Active A x F)}{β Q γ D L M s:ℝ}{J:ChartRatio G}{P:Patch}
open Forge Reine Rill
open Rill
local notation "m₀"=> SU.group.colorScale
lemma crown_h (D σ:ℝ)(hd:1≤D)(n k:ℕ)(hp:0<σ)(hv:m₀ ≤ D)(q:Chi): ∃ C:ℝ,0 ≤ C ∧∀ {f:Side}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](U:E→ Config G f)(x:E)(t:ℝ)(X:Finset (Cell f)),0<t → t≤1 → Trow U x (D*t) n →(∀ i:Cell f,Tender (fun y=>faceValue (U y) i) x (D*t) n)→ HeldT U X x→∀ (A:RG.Atom G k)(i:Site f),
 Allows n (lush_k q A X t i∘ U) x (C*t^k*A.budget σ)∧ ((∀ l∉X,Pressure.toll (U x) l≤ t) → Allows n (peer_k A X t i∘ U) x (C*t^k*A.budget σ)) ∧ ∀ p: Clip,Allows n (sleeve A X p i t ∘ U) x (C*A.budget σ):=by
 obtain ⟨f,v,hF,hV,H⟩:=pill k n D hv q (σ/2) (half_pos hp); obtain ⟨A,g,h⟩:=priceInk n f _ (half_pos hp)
 obtain ⟨L',hL,H'⟩:=plain n k D σ hp (zero_le_one.trans hd); let C:=max L' (max v (zest n*A*v)); refine ⟨C,hL.trans (le_max_left ..),@fun f' E _ _ U x t X ht hx u l k X' i=>?_⟩ -- binder shadows k
 obtain ⟨ha,hb⟩:= H X' U x i t X ht hx u l k
 have hz:= Real.exp_pos (σ/2*X'.length); have hG: 0 ≤ X'.budget (σ/2):=by unfold RG.Atom.budget RG.Atom.magnitude; positivity
 have hX:X'.budget σ= Real.exp (σ/2*X'.length) * X'.budget (σ/2):=by unfold RG.Atom.budget; rw [mul_left_comm,←Real.exp_add]; congr 2; ring
 have hv:0 ≤ X'.budget σ:=by rw [hX]; positivity
 constructor
 · apply ha.mono; apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (h _) (zero_le_one.trans (zpos n))) (by positivity)); rw [hX]; unfold C; apply le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ((le_max_right v (zest n*A*v)).trans (le_max_right ..)) (pow_nonneg ht.le _)) (by positivity)); ring
 refine ⟨fun j=> (hb fun i hx=> j i (mem_sdiff.mp hx).2).mono ?_, fun p=> ?_⟩
 · unfold C; rw [hX]; gcongr; · exact (le_max_left ..).trans (le_max_right ..)
   exact le_mul_of_one_le_left hG (Real.one_le_exp (by positivity))
 refine (sellsS p i t X X' k (H' U x (fun j=>?_) X' i)).mono (mul_le_mul_of_nonneg_right (le_max_left ..) hv); exact ((u j).paid (d:=m₀) (le_of_eq (Gauge.unitary_frob (SU.group.mat_mul_star _)))).mono (max_le (mul_le_of_le_one_right (zero_le_one.trans hd) hx) ‹m₀ ≤ D›)
lemma shake_p (n:ℕ)(p:Clip)(a σ D:ℝ)(h:1≤ D)(p':m₀ ≤ D)(ht:0<σ):∃ C:ℝ,0≤C ∧∀ {f: Side}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{v:ℝ}(U:E→ Config G f)(x:E)(t:ℝ)(q:PathData G)(F:Finset (Cell f))(r b:ℕ),0<t→t≤1 → Trow U x (D*t) n→ q.Bounds p σ a v → HeldT U F x → 0<b →∀ (i:Cell f),Allows n (fun y=>king F q p r b t (U y) i) x C:=by
 obtain ⟨u,A⟩:=Push.Uniform.paint_supply G n; obtain ⟨C,d,hC,hd,H⟩:= Esti.shortened p a ht A (zero_le_one.trans h)
 let M:=max (4*(p.linear+p.direct)) (p.direct*(Push.Uniform.priceCost G (Push.Uniform.travelCost G n 4 D))); let V:=M+2^n*C*C
 refine ⟨max 0 V,le_max_left ..,@fun f E _ _ v U x t q F r b hT hp hu hs hv hQ i=>?_⟩; have he:FuelG _ U x n D:=fun i=> ((hu i).paid (d:=m₀) (le_of_eq (Gauge.unitary_frob (SU.group.mat_mul_star _)))).mono (max_le (mul_le_of_le_one_right (zero_le_one.trans h) hp) p'); exact ((creek i p t hT.le hp he F hv).add (cow (pruned hv _ hC.le _ hT.le _ _ r b (i,true) (H U x he q hs r b hQ (i,true))))).mono (le_max_right ..) -- tune
end YM.CF.Cloak
