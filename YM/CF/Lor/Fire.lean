import YM.CF.Lor.Ice
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Lor
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Lich Corne
open Lich.Muster
attribute [local instance] opCStarAlgebra
local notation "G₅"=> SU.group
open Pressure.Tube
open Vol
variable{c f N B:Side}{d n m l:ℕ}{a b K v v' u D D' κ τ τ' :ℝ}{p:BudgetPoint}{q:Chi}
-- common allowance-target category.Across any Horizon.S.True.N.Anchor.g
variable{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
open Fief
variable(Q:Patch){S:StepData c f}(F:Tube G₅ S) (M: Monk SU.group S)(q:Chi)(n l:ℕ)(x v s β α L:ℝ)(Z: ChartRatio G₅)(i:Site c)(d:ℝ)
variable {C D ρ η:ℝ}{U:E→ Config G₅ f}{p:E}{o:Clip}
local notation "A"=> M.key
local notation "Λ"=> Directions SU.group c
local notation "m₀"=> M.zoo x
local notation "φ"=> Stores.till x
local notation "X"=> fun z:Λ=>M.atop z x
local notation "B"=> Cloak.bent F x M d l q v L
local notation "W"=> repine F x M d l q v L
-- ratioD η envelope. supports all
lemma kilo{U:E→ Config G₅ f}(hp:F.up.Bounds F.high ρ C D)(u:∀ i:Bond f,ContDiffAt ℝ (↑n) (fun v'=> SU.group.mat (U v' i)) p)(h:∀ (Yt: Atom SU.group 2) (j:Site f), Allows n (fun t=> Yt.unmasked (U t) j) p (η*Yt.budget ρ))(i:Site f)(ht:0 ≤ η): Allows n (fun t=> gplot (batch F.up.loop φ) (U t) i) p (η*D):=by
 let V:=batch F.up.loop φ
 choose H hv Q' using fun j: Bond f=> lateB (u j); let C':= ∑ j,H j
 obtain ⟨T,v',hk⟩:= plain n 2 C' ρ hp.width (sum_nonneg fun i _=>(hv i).le); have hx:= barn hp.two φ; unfold gplot
 refine (late_sum (f':=fun j (k:E)=> (V j).unmasked (U k) i) ?_ (hx.2.1.mul_left T) (hx.2.1.mul_left η) (fun i=>h ..)).mono ?_
 · filter_upwards [eventually_all.mpr Q'] with x h j; exact hk U x (fun i=>(h i).mono (single_le_sum (f:=H) (fun w _=> (hv w).le) (mem_univ _))) _ _
 rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hx.2.2 ht
abbrev moon (R:Patch):ℝ:=(Fintype.card Axis*R.L.val^4*Rel.plot 1:ℕ)
lemma dustM {x':Λ×ℝ} (hx:S.patch=Q)(g:0 ≤ D)(h:∀ i:m₀, Allows n (fun t=> logGuard q Z s (tape (B t) i)) x' D): Allows n (dues F M q l x v s L Z i d) x' (moon Q*D):=by
 apply (summed _ _ (fun j _=> ((h j).smul (ansC (S:=S) i j.val.val)).mono (mul_le_of_le_one_left g (plant_v (w:=fun _:Fin (0+2)=> j.val.val))))).mono
 unfold moon; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr ((bed_count x i M).trans_eq (by rw [hx]))) g
private def dustZ (j:Site c)(y:Λ×ℝ):= averaged fun s=>∑ i∈ Arena.hoop S s j,prism_w F x s (W y) i
def psiG (P:Monk G₅ S):= kite F x q d l P β Z s i - Lor.shade F q l x β i d P
def papS:= dues F M q l x v s L Z i d-dustZ F M q l x v L d i
lemma sprit(hv:v≠0)(h:L≠0)(t:ℝ)(w:Λ): psiG F q l x s β Z i d (rough (X w) (t•M.z))= papS F M q l x v s L Z i d (w,t*coupling β*L/v):=by
 unfold psiG papS; rw [dual_r F M q l x v s β L Z i d t hv h]; apply congrArg ( (dues F M q l x v s L Z i d (w,t*coupling β*L/v)) - ·); unfold Lor.shade psalms dustZ; rw [belt F x M d l q v L β t w hv h]; rfl
variable {cnt:ℝ}
lemma palm_s (p:Allows n (dues F M q l x v s L Z i d) (0, cnt) C)(hx:S.patch=Q)(ht:0≤D)(hv:∀ (z: Signed)(i:Site f),Allows n (fun y=> gplot (batch F.up.loop φ) (pull z 0 (W y)) i) (0,cnt) D): Allows n (papS F M q l x v s L Z i d) (0,cnt) (C+(about Q.L 0)*D):=by
 refine subtract_p p (allowedAv _ _ fun z=> (summed _ _ (fun (j:Along S) _=>?_)).mono (mul_le_mul_of_nonneg_right ?_ ht)) -- tune
 · rcases j with j|j|j
   · exact allows_const _ (norm_zero.le.trans ht)
   · exact hv z j
   exact allows_const _ (norm_zero.le.trans ht)
 exact Nat.cast_le.mpr ((infant_p i _ _).trans_eq (by rw [hx]))
lemma turnY {R:Teller G₅}(p:R.Funds S F)(hx:LocalRatio Z) :starsW (x:=x) M (psiG F q l x s β Z i d)= (fun y=> zenA F x q d α l (X y) β Z s i):=by
 ext1 y; unfold starsW psiG zenA; rw [show flat_w F x q d α l _ β Z s i=0 from curve_l F x q d α l (X y) Z s β p hx i,ice_z F (X y) q l x β α i d (Cay.rough (X y) 0) rfl]; abel
end YM.CF.Lor
