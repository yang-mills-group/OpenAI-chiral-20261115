import YM.CF.Cloak.Arc
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
section smooth
variable {Y Z:Type}[NormedAddCommGroup Y][NormedSpace ℝ Y][FiniteDimensional ℝ Y][NormedAddCommGroup Z][NormedSpace ℝ Z][FiniteDimensional ℝ Z](F:Y×ℝ→Z) (C u:ℝ)
open Cay AnalyticBridge.RelativeLogdet.Ink
lemma rushL(n:ℕ)(p:∀ t∈interval, Allows (n+1) F (0,t*u) C)(h:|u| ≤1): Allows n (fun y=> F (y,u)-F (y,0)) 0 ((2^n*|u|)* Jet.composeCost n C 1):=by simpa [sum_range_succ,Cay.grade,Cay.tear] using coup_b F C u n 0 p h
lemma rushQ(n:ℕ)(p:∀ t∈interval, Allows (n+2) F (0,t*u) C)(h:|u| ≤1): Allows n (fun y=> F (y,u)-(F (y,0)+fderiv ℝ F (y,0) (0,u))) 0 ((2^n*|u|)^2* Jet.composeCost n C 1):=by simpa [sum_range_succ,Cay.grade,Cay.tear] using coup_b F C u n 1 p h
lemma rushP(n:ℕ)(p:∀ t,|t|≤|u|→ Allows (n+2) F (0,t) C)(h:|u|≤1) : Allows n (fun y=> F (y,u)-F (y,0)) 0 ((2^n*|u|)* Jet.composeCost n C 1) ∧ Allows n (fun y=> F (y,u)-F (y,0)+(F (y,-u)-F (y,0))) 0 (2*((2^n*|u|)^2* Jet.composeCost n C 1)):=by
 have hu(t)(g:t∈interval): |t| ≤ 1:=(abs_of_nonneg g.1).trans_le g.2; have hQ(t)(g:t∈interval):=p (t*u) (by rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) (hu _ g))
 refine ⟨rushL F C u n (fun i t=> (hQ i t).order (by omega)) h,?_ ⟩
 have hv:= rushQ F C (-u) n (fun i g=> p _ (by rw [abs_mul,abs_neg]; exact mul_le_of_le_one_left (abs_nonneg _) (hu _ g))) (by rwa [abs_neg]); rw [abs_neg u] at hv; rw [two_mul]; apply ((rushQ F C u n hQ h).add hv).germ; filter_upwards with i; rw [show ((0,-u):Y×ℝ)=-((0,u):Y×ℝ) from Prod.ext (neg_zero.symm) rfl,map_neg]; abel
end smooth
open Cay
open Matrix
variable {F:Forest S.ratio}{T:Tube G S}
local notation "GZ"=> Directions G c
-- polished λ map for TRUE fluctuation. scale σ, near identity# z; coords λ lifts
variable (T:Tube G S)(x:ℝ)(M:Monk G S)(d:ℝ)(l:ℕ)(p:Chi)(a L:ℝ)
def bent(z:GZ ×ℝ): Prices G (Active M.key x M.park):= let V:=(M.atop z.1 x).V; liftN T x V M.k M.key M.park p d (M.bush x) l + z.2 • (a • (L⁻¹ • pushP T M.key M.park V M.k p d x (M.bush x) l (M.bell x)))
def repine(z:GZ × ℝ):= landed x M.key M.park (M.atop z.1 x).V (M.bush x) (bent T x M d l p a L z)
lemma belt (β:ℝ)(t:ℝ)(z:GZ)(ha:a ≠0)(h:L≠0): repine T x M d l p a L (z,t*coupling β*L/a)= ((rough M (t•M.z)).atop z x).sent x T p d l β:=by
 let N:= (rough M (t • M.z)).atop z x; let Q:= (M.atop z x).V; let P:= liftN T x Q M.k M.key M.park p d (M.bush x) l; let K:= pushP T M.key M.park Q M.k p d x (M.bush x) l; have he:K (N.bell x)= t • K (M.bell x):=by
    rw [show N.bell x = t • (M.bell x) from rfl]; unfold K pushP; rw [show tape.symm (t • (M.bell x))= t • tape.symm (M.bell x) from Next.SectorChange.colors.symm.map_smul _ _,mulVec_smul]
 change landed x N.key N.park Q _ (P+(t*coupling β*L/a) • (a • (L⁻¹ • K (M.bell x)))) = landed x _ _ _ _ (P+coupling β • K (N.bell x))
 rw [he]; simp_rw [smul_smul]; rw [show t*coupling β*L/a * (a * L⁻¹)= coupling β * t from ?_]; swap; · field_simp
 rfl
end YM.CF.Cloak
