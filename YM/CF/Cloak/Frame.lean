import YM.CF.Cloak.Gear
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
section bound
variable {E X:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{x₀:E}{U:E→ Config G f}{u v C D:ℝ}{T:E→X}[NormedAddCommGroup X][NormedSpace ℝ X]
local notation "m"=> SU.group.colorScale
open scoped Classical
variable {X₂:Support f}{U₀:Config G f}{A:Finset (Cell f)}{F:Forest S.ratio}{s:ℝ}
open Atala
section
-- unmasked terms easier potency when t large / min order unit.
open Work.F03 Vol
lemma plain (n a:ℕ)(C σ:ℝ)(hp:0<σ)(hv:0 ≤ C):∃ A:ℝ,0 ≤ A ∧ ∀ {f:Side}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](U:E→ Config G f)(x:E), (∀ i,grantB n (fun y=>U y i) x C) →∀ (V:RG.Atom G a)(i:Site f), Allows n (fun y=> V.unmasked (U y) i) x (A * V.budget σ):=by
 obtain ⟨N,hN,H⟩:=travel_coupon G n C hv (half_pos hp); let M:= Push.Uniform.travelCost G n 4 C; let X:=curvatureCost G*M; let P:= m⁻¹*(2^n*(2^n*N*(m*X))*N); let B:=(zest n*P)^a; refine ⟨max 0 B,le_max_left ..,@fun f E _ _ U x p V i=>?_⟩; refine (cupXT (n:=n) (U:=U) (C:=σ) (D:=P) V i (fun j=>?_)).mono (mul_le_mul_of_nonneg_right (le_max_right ..) (by unfold RG.Atom.budget RG.Atom.magnitude; positivity))
 let s:=V.leg j; let w:=slotFace s i; let v(x):=travel (U x) i s.walk; let r(x):=faceValue (U x) w; simp_rw [atSite_path]; change Allows n (fun y=>SU.group.adjoint (v y) (SU.group.curvature (r y))) _ _; apply (adjointQ ((trekP f U p _ i (Slot.length s) (Nat.le_add_right s.walk.length 4)).mono (H _)) (arc_b (trekP f U p (square w.2.val.1 w.2.val.2) w.1 4 le_rfl))).mono; rw [show Real.exp (σ*(V.leg j).length) = Real.exp (σ/2*s.length) * Real.exp (σ/2*s.length) from ?_]; swap; · rw [←Real.exp_add]; unfold s; congr 1; ring
 unfold P X M s; exact Eq.le (by ring)
variable {k₁: ℕ} {σ σQ A':ℝ} {P:Clip}{T':PathData G}{B:BudgetPoint}
def sleeve (F:RG.Atom G k₁)(X: Finset (Cell f))(A:Clip)(i:Site f) (u:ℝ)(V: Config G f):ℝ:= if pers X A u V i then F.unmasked V i else 0
lemma sleeve_p (s:Site f)(p:T'.Bounds P σ A' σQ)(d v:ℕ)(h:0<d)(V:Config G f)(t:ℝ)(he:B.threshold=t)(X: Finset (Cell f))(hy:pers X P t V s↔ PathData.kept P t s V): (∑' i,sleeve (rod T' (v/d) i) X P s t V)= ∑ j,cuff T' P B d v V (s,j):=by
 have he'(i): shorten T' v d V i=(grainA T' (v/d)).ell V i:=by refine tsum_congr fun j=> ?_; unfold shortenTerm PathData.ellTerms grainA; dsimp only; simp only [Nat.le_div_iff_mul_le h]; split <;> simp [*]
 by_cases z:PathData.kept P t s V
 · unfold sleeve; simp_rw [if_pos (hy.mpr z), uncut_pair p (v/d)]; simp only [cuff,PathData.baseTerm,crown,Pressure.trunk,he, z,↓reduceIte,he',sum_sub_distrib,sum_add_distrib]; ring -- possible sorry ambiguity
 simp only [cuff,PathData.baseTerm,crown, Pressure.trunk,he,z,↓reduceIte,sleeve,if_neg (mt hy.mp z), zero_add,add_zero,sum_const_zero,sub_self,tsum_zero]
lemma sellsS (P:Clip)(i:Site f)(t:ℝ)(X:Finset (Cell f))(Q:RG.Atom G k₁)(h: HeldT U X x₀)(hp: Allows n (fun v=> Q.unmasked (U v) i) x₀ C): Allows n (sleeve Q X P i t∘ U) x₀ C:=by
 have hh:=held_p h P i t; by_cases z:pers X P t (U x₀) i; exact hp.germ (hh.mono fun i p=> (if_pos (p.mpr z)).symm); exact (allows_const x₀ (v:=(0:ℝ)) (by simpa using hp.nonneg)).germ (hh.mono fun i p=>(if_neg (mt p.mp z)).symm)
end
end bound
end YM.CF.Cloak
