import SatinThinNovella
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.QuadClock
open Neon
open Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew
variable {N n B:Side}
set_option autoImplicit false
open Mew Waxy

variable {P:Side}{l:Patch}{K:Teller SU.group}{L:ChartRatio SU.group}
  (V:Grace K l L) {e:ℝ}(P_:Grasp V.U B e)
  (G:Ratio (mid N B) (mid P B))(S:StepData (Domain N B) (Domain P B))(G₀:Scree.Loom (mid N B))(G₁:Scree.Loom (mid P B))(X:GramM (mid N B))(Y:GramM (mid P B))(Xp:Op SU.Slot)(q:Chi)(d h Vp Vf T W C BQ Rt Zt b g κp:ℝ) -- b,g∶ b call budgets all same, g Sized
variable {J: Type}[LinearOrder J][Fintype J]
local notation "TF"=> mid P B
local notation "Tc"=>mid N B
variable (U:Solid G X.p)(F:Topic (mid P B))(o:Site (mid N B))
variable (σ:ℝ → Cusp (mid N B))
local notation "ST"=> Sweep Tc
-- Ask about current. Single-key only (not returning Ψ yet); u,A not properties of entry here, can select repr and empty-case.
variable (Ca:ℝ→ℝ→ℝ)(μ α:ℝ)
local notation "Tic"=>Tidecard G X Y U F
local notation "nun" x:max=> nun_ω Y.F (Hove.heel G x)
local notation "ρ" x:max => κprobe mintR l.L h α T (nun x) (PointSk μ)
local notation "incq" Z:max x:max => αPrice l.L h α T BQ Rt Zt (PointSk μ) Z X.p Y.p (nun x)
-- gate on existence of at least one purchase.
def Gift (l:Patch)(u:Pax (mid N B)): Prop:= Tidecard G X Y U F o σ∧ adorns X.p σ u∧ let R:=κprobe mintR l.L h α T (nun_ω Y.F (Hove.heel G o)) (PointSk μ); ∃ E K z Y', Ice l.L.val o X.p h (W*R) (Ca μ α) (C*R) (coldE X.p u) E K z Y'∧ αPrice l.L h α T BQ Rt Zt (PointSk μ) Y' X.p Y.p (nun_ω Y.F (Hove.heel G o))
#print axioms Gift
#check Gift
variable (q1:Odd G.count.val)(a1:∀ s∈cycleSweep (mid P B), passingR (mid P B) s Y.F Y.F)(b1:∀ s∈cycleSweep (mid P B), passingF (mid P B) s Y.K Y.K)(κ:ℝ)(vκ:∀ x: Site (mid P B), nun_ω Y.F x=κ)(hs:0≤h)(v:HavenL (mid N B) X.p l.L.val)
include q1 a1 b1 hs vκ v
omit q1 a1 b1 hs vκ v in
lemma wreath (x y:Site (mid N B))(F H: Copy (mid N B))(p:∀ s∈ fromHere x y, Fρ s (bandSign s • H)= F) : hailQ Fρ y H x= F:=by
 unfold hailQ avenue; simp_rw [←map_smul]
 rw [sum_congr rfl (fun i (u:i∈fromHere x y)=> p i u),sum_const,← Nat.cast_smul_eq_nsmul ℝ]; exact inv_smul_smul₀ (by exact_mod_cast (card_pos.mpr (anyFrom x y)).ne') _
#check cleared
#check dormant
lemma sell_all : ∃ (a:ℝ)(E: Site (mid N B)→ RegBudget (mid N B))(K':Site (mid N B)→ Cusp (mid N B)), Bent Eρ E∧ Bent Kρ K'∧∀ x σ A, Gift G X Y h T W C BQ Rt Zt U F x σ Ca μ α l A→ Ice l.L.val x X.p h (duty_Q X.p.order X.p.power*(W*(ρ x))) (strive_E X.p.order*Ca μ α) (C*(ρ x)) (coldE X.p A) (E x) (K' x) 0 (PointSk a) ∧ incq (PointSk a) x:=by
 by_cases p:∃ (x:Site Tc)(σ:ℝ → Cusp Tc)(A:Pax Tc),Gift G X Y h T W C BQ Rt Zt U F x σ Ca μ α l A; swap
 · exact ⟨0,0,0,fun s _ x y _=>by simp [map_zero],fun s _ x y _=>by simp [map_zero],fun x t u v=>False.elim (p ⟨x,t,u,v⟩)⟩
 obtain ⟨x,σ₀,A,R,h,u,K',z,D,he,hl⟩:=p; let a:=coldE X.p A; let ξ:= hailQ Fρ x a
 have hero (y:Site Tc)(σ:ℝ → Cusp Tc)(A':Pax Tc)(t:Tic y σ)(p:adorns X.p σ A'): ξ y=coldE X.p A':=wreath y x _ _ (fun T (_u:T∈fromHere y x)=> dormant G X Y U F y σ ((fromHere_iff ..).1 _u).1 t x σ₀ R q1 a1 b1 ((fromHere_iff ..).1 _u).2 A' p A h) -- adjust ordering
 have hh : ξ x=a:= hero x σ₀ A R h; rw [vκ] at hl
 obtain ⟨r,s,w⟩:= cleared (L:=l.L) Y.p α T BQ Rt Zt μ v x hs ξ (hail_F x a) u K' z D (by rw [hh]; exact he) hl -- tune `p` nonneg? hd maybe vκ
 refine ⟨r,hailQ Eρ x u,hailQ Kρ x K',hail_E x u,Waxy.hail_K x K',fun y τ Ux Hy=>?_ ⟩
 have he:= w y; rw [hero y τ Ux Hy.1 Hy.2.1] at he; constructor
 · -- normalize nun x/y
   specialize he; simp_rw [vκ] at he ⊢; exact he
 rw [vκ]; exact s
end YM.CF.QuadClock
