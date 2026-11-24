import Bay.D.Turret
import Bay.D.Yacht
import YM.SU5.Thin.Glacier.Layer
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

namespace D
open Exterior Precision Nacre
open scoped ContDiff
open Regis Regis.Head Etch Gleam Next.SectorChange Next.SectorChange.Gaussian
open Pressure Work.F03 ProbabilityTheory
local notation "T4"=>SU.group

open Next.Rank.Spindle
variable {c N:Side} {G:Ratio c (More N)} {X:Support c} {D:Finset (Cell (More N))}
 {p:BudgetPoint}{o:Seat N}
 {q:Clip}{Z:PathData T4}{H:Bed}{η C S:ℝ}(B:Z.Bounds q η C S)(P:Attached H Z)
 {β:ℝ}
 (V Y:Lag N)

lemma fraser{i:Cell (More N)} (h:rimB G X p.B D i)(hj:0<β):
   coupling β • river q i (iceCost B P G X p.B D Y β V)=faceCurl i (V+Y):= by
 rw [iceCost,map_smul,smul_inv_smul₀ (coupling_pos hj).ne', ←river_now q B P,map_add (tiler B P)]
 ext1 l; unfold river cup; simp[accessN,h]

lemma tideTurn (g:Kite (More N))(w:Shutter p)
 (d:Deep G X D (hallBill p.B) (g.rise o)) (b:ℝ)(u:0<β):
 Set.EqOn
    (delta q (b*coupling β) g (iceCost B P G X p.B D Y β V))
    (b • brine (g.sail (V+Y))) (Lagoon (p.B/10) o):=by
 intro i h
 have hj:= fraser B P V Y (lDeep g w d i (mem_product.mp h).1) u
 simp only [delta, Pi.smul_apply, smul_eq_mul, sea, brine_sail, ←hj, PiLp.smul_apply]; ring

abbrev rope(R:Rules T4)(p:BudgetPoint)(L b v K:ℝ):ℝ:=
   L*b^2*(2*v)^3+ L*2*(b*chia R p v)^4/K^2
abbrev mast(p:BudgetPoint)(b L:ℝ):ℝ:=
   L*b^2*p.threshold^2
def wheel (b:ℝ)(f:Pane N→ℂ) :Pane N→ℂ:=(b^2) • f

variable (R:Rules T4){b fD v L d r:ℝ}{f:Pane N→ℂ}
   {A: Icey (Cella (More N))}
lemma drives
  (t:Vessel p o (p.B/10) r d L f A)
  (g:Kite (More N))(K:ℝ)
  {U:Pane N}
  (i:0≤v)(n:v≤R.c)(j:2*v ≤ r)(m:0≤b)
  (l:TrustLogs (V+Y) U G X v)
  (k:ProbeBox (V+Y) (2*v))(z:meek p U=D)
  (w:Shutter p)(h:Deep G X D (hallBill p.B) (g.rise o))(u:0<β):
 ‖wheel b f (g.swirl U)-quay q (b*coupling β) K A g (iceCost B P G X p.B D Y β V)‖≤
      rope R p L b v K:=by
 let y:=g.sail (V+Y)
 let a:=b • brine y
 let x:=delta q (b*coupling β) g (iceCost B P G X p.B D Y β V)
 have hh:‖y‖≤2*v:=gale g k (by positivity)
 have ht:= t.skin.turns (lAwning g h z) (hh.trans j)
    (lDuct g R l h n)

 rw [zero_add] at ht
 unfold rope
 apply le_trans (norm_sub_le_norm_sub_add_norm_sub _ (splash A a) _)
 apply add_le_add
 · rw [wheel,Pi.smul_apply,splash,show a=b • brine y from rfl,
       swirl_xyScale,←sq,←smul_sub,norm_smul, Real.norm_of_nonneg (sq_nonneg _)]
   rw[mul_comm L]; refine le_trans (mul_le_mul_of_nonneg_left ht (sq_nonneg _)) ?_
   have :=t.vinyl.nonneg -- ?
   rw[mul_assoc];exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hh _) ‹0≤L›) (sq_nonneg b)
 let hya:= tideTurn B P V Y g w h b u
 have e:Set.EqOn (pur K ∘ x) (pur K ∘ a) (Lagoon (p.B/10) o):=fun _ p=>congrArg (pur K) (hya p)
 change ‖splash A a-splash A (pur K ∘ x)‖≤_
 rw [splash,splash,t.skin.rake.swirl_same e e]
 refine wave_crest t.skin.rake a (mul_nonneg m (chia_p R p _)) ?_
 intro q c; unfold a y;rw [Pi.smul_apply, smul_eq_mul,abs_mul,abs_of_nonneg m]
 exact mul_le_mul_of_nonneg_left (lCurl g R w h l i n z _ (mem_product.mp c).1) m

lemma wheel_max(t:Vessel p o (p.B/10) r d L f A)
 (U:Pane N):
 ‖wheel b f U‖≤ mast p b L:=by
 unfold mast wheel; rw [Pi.smul_apply,norm_smul,Real.norm_of_nonneg (sq_nonneg _)]
 have h:‖f U‖ ≤ L*p.threshold^2:=by

    by_cases hh:U∈setAwning p o
    · simpa only [sub_zero] using t.skin.small U hh
    rw [t.vinyl.fence U hh,norm_zero]; exact mul_nonneg t.vinyl.nonneg (sq_nonneg _)
 exact (mul_le_mul_of_nonneg_left h (sq_nonneg b)).trans_eq (by ring)
end YM.CF.Bay.D
#print axioms YM.CF.Bay.D.drives
