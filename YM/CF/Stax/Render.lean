import YM.CF.Stax.Flow
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Stax
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
local notation "CΞ"=> Cipher n
variable (P: BudgetPoint)(h:ℝ)(δ:ℕ)
variable {P h δ}
variable (F:Aura n→Support (More n)→ Copy n)(r: Aura n→ Support (More n)→ℝ)(hF:∀ X:Aura n,∀ D⊆ X.val,Fray P h δ X D (F X D) (r X D))
variable (K:Rinse (Seat n) (Copy n))(z:Aura n→ℝ)
variable {M:Orbit n→Aura n→ FC (Dwell n)}(T:Pitch P h δ K z M)
local notation "Q"=> Cadre.chip K F
local notation "N"=> Cadre.chip (cribR z) r
local notation "Qd"=> nutL K F
local notation "Nd"=> nutL (cribR z) r
variable (w:0≤h)
open PowerSeries
-- realization fixed ω. pull syntax PS pointwise
variable (x:Orbit n)(p:FleetS P.threshold x.1)
local notation "Ωx"=> flags P.threshold x.1
abbrev fL (A:PowerSeries (Copy n))(x:Orbit n): PowerSeries (Cipher n):= mk fun i=> coeff i A x
lemma fP (A: PowerSeries (Copy n))(v:ℕ):coeff v (fL A x)= coeff v A x:=by rw [fL,coeff_mk]
lemma fProd (S:Hk)(W:Aura n→ PowerSeries (Copy n))(v:ℕ): coeff v (∏ j∈S,fL (W j) x) = coeff v (∏ j∈S,W j) x:=by
 rw [coeff_prod,coeff_prod]; simp_rw [fP]; rw [Finset.sum_apply]; apply sum_congr rfl; intro i _; rw [Finset.prod_apply]
abbrev cumQ (V:Orbit n)(P: BudgetPoint)(X:Aura n):= fL (Q X (flags P.threshold V.1∩ X.val)) V
local notation "Zq"=> cumQ F K x P
abbrev ξz(X Y:Aura n)(G: Hk):= fL (Cadre.grate K Q X (Ωx∩ X.val) Y G) x
local notation "Zp"=> ξz (P:=P) F K x
lemma tent (X:Aura n): derivative (CΞ) (Zq X) =∑ Y:Aura n,∑ G∈drum X Y (Ωx∩X.val),Zp X Y G:=by
 apply PowerSeries.ext; intro i; have he:= congrArg (fun y:PowerSeries (Copy n)=> coeff i y x) (Cadre.dash (Ωx∩X.val) K X F);
 unfold cumQ; simp_rw [coeff_derivative,map_sum]; change (coeff _ (fL _ _))* _=∑ Y:VX,∑ G∈drum X Y _,coeff i (Zp X Y G); unfold ξz; simp_rw [fP]
 simp only [coeff_derivative,stepL,Cadre.rill,map_sum,Pi.mul_apply,inter_univ,Finset.sum_apply,Pi.add_apply,Pi.one_apply,Pi.natCast_apply] at he; exact he
include T w hF p
lemma tryP(X Y:Aura n)(G:Hk)(g:G∈drum X Y (Ωx∩X.val))(i:ℕ): (coeff i (Zp X Y G)).val=Sault.rind (M x Y * (coeff i (∏ t∈G, Zq t)).val):=by
 let D:= Ωx∩X.val; let R(i:Aura n):= Q i (D∩i.val); let A:=∏ j∈G,R j
 have hp(Y':Aura n)(u:Y'∈G): Y'.val ⊆ X.val:= by rw [(drum_p ..|>.mp g).2.2]; exact Subset.trans (coneL u) subset_union_right
 have ht: (∏ t∈G,Zq t)= ∏ j∈G,fL (R j) x:=prod_congr rfl fun j h=>by unfold R cumQ D; rw [inter_assoc, inter_eq_right.mpr (hp _ h)]
 rw [ht,fProd,ξz,fP,Cadre.grate,coeff_mk]; exact T.body X Y x p (by rw [(drum_p ..|>.mp g).2.2]; exact subset_union_left) _ _ (crest F r K z X Y G D i g (fun a _ j _=> fed F r hF K z T w a _ inter_subset_right j) w)
lemma cold (X:Aura n)(i:ℕ): Flour (camp X.val) (coeff i (Zq X)).val:=by unfold cumQ; rw [fP]; exact (fed F r hF K z T w _ _ inter_subset_right i).merit.lit x
lemma star_L: (coeff 0) ∘ Zq= Vow.hailV Ωx F x:=by funext i; simp_rw [Function.comp_apply,cumQ,fP, Cadre.peg]
omit w
variable (w':1≤h)
include w'
lemma fair(X:Aura n)(D:Support (More n))(g:D=Ωx∩X.val) : pingS P.threshold (X.val\D) x.1:= (shoreK P.threshold x.1 p _).mp (Finset.disjoint_left.mpr fun {i} l t=> (mem_sdiff.mp l).2 (g.symm ▸ mem_inter.mpr ⟨t,(mem_sdiff.mp l).1⟩)) -- tune type
lemma paid (X:Aura n)(D:Support (More n))(g:D=Ωx∩X.val)(pN:Aqua (N X D)): Aqua (Zq X):=by
 unfold Aqua; rw [g] at *; unfold cumQ; simp_rw [fP]; apply Summable.of_nonneg_of_le (fun _=> norm_nonneg _) ?_ (pN.of_norm); intro i; exact (fed F r hF K z T (zero_le_one.trans w') X _ inter_subset_right i).merit.capF w' _ (fair F r hF K z T x p w' X _ rfl) -- tune
lemma print (pN:∀ X:Aura n,∀ D⊆ X.val,Aqua (N X D)) (A:Op (Single n))(y:Scree.Phys n)(W:Op (Single n))(q: IsStarProjection A)(g:Thera.TagG A W)(e:Sea A y)(v:Op SU.Slot)(vx:star v=v)(pM:∑ Y:Aura n,M x Y=Sault.dma A W (-(Tap.plankP n v)) (Dial.tickA n)):let U:=nutL K F; let c:=acts (exp (dg W)) y; let L:=nursery A q
 acts (L.cook (hGas Ωx (hitU ∘ Zq))) c=scaleZ v (acts (L.cook (hGas Ωx (hailV Ωx F x))) c):=by
 intro U c L; rw [← star_L F r hF K z T (zero_le_one.trans w') x p]; refine dance Ωx A W v y q g vx e _ _ _ _ (tent (P:=P) F K x) (tryP F r hF K z T (zero_le_one.trans w') x p) (fun X=> T.edge x X) ?_ (cold F r hF K z T (zero_le_one.trans w') x p) (fun i=> paid F r hF K z T x p w' _ _ rfl (pN _ _ inter_subset_right)) pM; intro X Y q; exact Finset.disjoint_left.mpr fun {i} g p=>Finset.disjoint_left.mp q (mem_filter.mp g).2 (mem_filter.mp p).2
end YM.CF.Stax
