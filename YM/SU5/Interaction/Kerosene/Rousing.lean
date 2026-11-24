import YM.SU5.Interaction.Kerosene.Vulcan
/- Loans no time tracing. Kernel evolution and flags. Will instantiate a geometry at all Keys. -/
set_option autoImplicit false
set_option maxHeartbeats 810000
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
variable {n:Side}{P:BudgetPoint}{h:ℝ}{δ:ℕ}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
variable (F:Aura n→Support (More n)→ Copy n)(r: Aura n→ Support (More n)→ℝ)(hF:∀ X:Aura n,∀ D⊆ X.val,Fray P h δ X D (F X D) (r X D))
variable {I:Type*}[DecidableEq I]
variable (K:I→Rinse (Seat n) (Copy n))(C C' B:I→Aura n→ℝ)(γ κ:ℝ)
variable (M:I→Orbit n→Aura n→ FC (Dwell n))(T G :Finset I) (D:I→ Support (More n))
variable (g: ∀ i∈ G,WickL P h δ (K i) (C i) (C' i) (M i) (D i))(u:0 ≤ h)
variable (W W':Aura n→ℝ)(pW:WarmStyle W)(hw:0 ≤ W)(hq: maestro B G W ≤ W')(hr:0 ≤ γ)(hB:∀ i∈ G,fog W' (C i) γ ≤ B i)(s:1 ≤ κ)
-- fee increase
variable (f:List I)
def woodBar (K:I→ Rinse (Seat n) (Copy n))(f:List I)(F:Cusp n): Cusp n:= f.foldl (fun F i=> volta (K i) F) F
def woodTariff (C C':I→Aura n→ℝ)(f:List I)(V:Tape (A:=Seat n)): Tape (A:=Seat n) := f.foldl (fun V i=>V+charglass (C i) (C' i) V) V
local notation "Kf" f:max=> woodBar K f F
local notation "Zr" f:max=> woodTariff C C' f r
local notation "Saf" v:max t:max=> SafeBand v κ C' B γ W W' t
include hF g u
lemma escortFray {f:List I} (p:f.toFinset⊆ G) : ∀ X:Aura n,∀ D⊆ X.val, Fray P h δ X D ((woodBar K f F) X D) ((woodTariff C C' f r) X D) := by
 induction f generalizing F r <;> rw [woodBar,woodTariff]
 case nil=> exact hF
 case cons i J H=> exact H (volta (K i) F) _ (fun X _ x=>markVolta F r hF (K i) (C i) (C' i) (M i) (g i (p (by simp))) u X _ x) (fun j x=>p (by simp only [List.toFinset_cons,mem_insert]; right; assumption))
omit hF
include hw hB hq
lemma fog_steel :∀ i∈G,0≤ B i:= by
 have hz(K':Finset I)(q:G ⊆ K') (V: VX→ℝ): 0 ≤ maestro B K' W:=fun i=> mul_nonneg (hw i) (Real.exp_pos _).le
 intro i l Y; exact (mul_nonneg (mul_nonneg ((g _ l).dice Y) ((hz G (Subset.refl _) 0).trans hq Y)) (Real.exp_pos _).le).trans (hB i l Y) -- check fog conflict
include hF pW hr s
#check SparkPlot
lemma woodCosts(p: G=f.toFinset)(v:f.Nodup)(q:SafeBand r κ C' B γ W W' G) : SafeBand (woodTariff C C' f r) κ C' B γ W W' ∅ := by
 have hh:∀ i∈ G,0≤B i:=fog_steel K C C' B γ M G D g u W W' hw hq hB -- order
 have hk:∀ i∈ G,0 ≤ C' i:= fun i y X=> ((g i y).birth X).merit.wage u
 have hx(J:List I)(U:Cadre.Tape (A:= Seat n))(h:J.Nodup)(p:J.toFinset ⊆ G)(e:Fiery U)(w:Saf U J.toFinset) : Saf (woodTariff C C' J U) ∅:=by
    induction J generalizing U <;> rw [woodTariff]
    case nil=> exact w
    case cons i j ih=>
       have hy:= p (show i∈ _ from (by simp));
       let V:= charglass (C i) (C' i) U; let H:= U+V; have hg:Fiery H:= fun j D p' => add_nonneg (e j D p') (charglass_burn _ _ _ (g i hy).dice (hk i hy) e j D p'); have hrY:= List.nodup_cons.mp h;
       apply ih H hrY.2 (fun x hx=>p (by simp only [List.toFinset_cons,mem_insert]; right; assumption)) hg
       -- tune signature
       exact SparkPlot U κ s W γ hw pW e C' C B G j.toFinset W' hh hk (fun i p=>(g i p).dice) hq hr hB i (by simpa using hrY.1) (by simpa using p) (by simpa using w)
 exact hx f r v (p ▸ Subset.refl _) (fun i D t=> (hF i D t).merit.wage u) (p ▸ q)
omit pW hw hq hB s hr

variable (x:Orbit n)(p:FleetS P.threshold x.1)(ok:∀ i∈G,(D i).Nonempty)
set_option quotPrecheck false
local notation "Ωx"=> flags P.threshold x.1
abbrev Γf(x:Orbit n)(i:I):=acts (1+∑ Y:Aura n,M i x Y)
local notation "Motion"=> List.foldl (fun z (i:I)=> Γf M x i z)
include p ok
lemma woodProgram (v:f.toFinset ⊆ G): acts (hGas Ωx (hailV Ωx (woodBar K f F) x)).val (vacuum (Dwell n))=f.foldl (fun z (i:I)=> Γf M x i z) (acts (hGas Ωx (hailV Ωx F x)).val (vacuum (Dwell n))) := by
 induction f generalizing F r
 case nil=>rfl
 case cons i l ih=>
    have ht:= v (show i∈ _ from (by simp)); let U:= volta (K i) F
    have he:= (advanceL F r hF (K i) _ _ (M i) (g i ht) u x p (ok i ht)); let Z:= hGas Ωx (hailV Ωx U x); let V:= hGas Ωx (hailV Ωx F x)
    let z:=vacuum (Dwell n); let m:Wave (Dwell n)→Wave (Dwell n):=fun y=>l.foldl (fun z (i:I)=> Γf M x i z) y
    have hB:l.toFinset ⊆ G:= (show l.toFinset ⊆ (i::l).toFinset from (by rw [List.toFinset_cons]; exact subset_insert ..)).trans v
    have h1:∀ Y:Aura n,∀ H⊆ Y.val,Fray P h δ Y H (U Y H) ((r+charglass (C i) (C' i) r) Y H):=markVolta F r hF (K i) (C i) (C' i) (M i) (g i ht) u
    have h2:=ih U _ h1 hB
    have hw: Γf M x i (acts V.val z) =acts Z.val z := he.symm
    have h0 : woodBar K (i::l) F = woodBar K l U:=rfl
    rw [List.foldl_cons,h0]; change acts (hGas Ωx (hailV Ωx (woodBar K l U) x)).val z = m (Γf M x i (acts V.val z)); rw [hw]; exact h2
end YM.CF.Stax
#print axioms YM.CF.Stax.woodProgram
