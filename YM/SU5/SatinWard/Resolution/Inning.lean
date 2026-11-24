import YM.SU5.SatinWard.Resolution.Tariff

/-!
# Character frames (physics-specific Sweep reps)
-/
set_option autoImplicit false
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
open Tap Waxy Ione.Clock StressFlux SU
namespace ShapeLab
open Module
local notation "EndC"=> Op SU.Slot
variable {ι:Type}[Fintype ι][DecidableEq ι]

open ResolutionFrame
variable (F:ResolutionFrame ι) (C K A:ℝ) (L: Side)
local notation "cι"=> (Fintype.card ι:ℝ)
local notation "ε1" => Real.exp (1:ℝ)
namespace ResolutionFrame
noncomputable abbrev rota (L:Side) := (L.val:ℝ)
structure PantryFin (ι:Type)[Fintype ι][DecidableEq ι](F:ResolutionFrame ι)(L:Side)(A C H:ℝ):Prop where
 loss : F.pulseBase L/sprintCost L ≤ 1/2
 hidden : 128*ε1*receiptCost * F.pulseHidden L C H A ≤ 1 / 16
 growth : 4*receiptCost*(rota L)^4 * ((rota L)^(7/8:ℝ)) ≤ sprintCost L

-- hearts for both loss & hidden. power: Finance at actual L after choosing A big. Need `lose ≤ L^-7/8` <=1. factor m(v) estimated upper /μ. μ-L ratio.P.
lemma feetPole (L:Side)(F:ResolutionFrame ι): F.chiLoss L=(rota L)⁻¹^F.deg:=rfl
lemma pulse_power (L:Side)(F:ResolutionFrame ι): F.pulseBase L=receiptCost*(rota L)^F.deg:=by rw [pulseBase,div_eq_mul_inv,chi_inverse]
lemma panPower (A C H:ℝ)(F:ResolutionFrame ι)(b:1≤ A)(u:1≤ C)(v:1≤ H):∀ᶠ n:ℕ in atTop,∀ L:Side,n≤L.val→ PantryFin ι F L A C H:=by
 let X:=receiptCost; let W:= accuracy C H A; have h:=receipt_pos; have he:0<W:=accuracy_pos C H A u v b
 filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (128*ε1*X * X*W*16), ((tendsto_rpow_atTop (by norm_num :(0:ℝ)<1/16)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop (4*X)] with n c y L l
 let r:=rota L; have hp:0 < r:= Nat.cast_pos.mpr L.property; have k:1≤ r:= Nat.one_le_cast.mpr L.property; have ru:(n:ℝ)≤ r:=Nat.cast_le.mpr l
 have h0:0<X:=receipt_pos
 have hs:4*X ≤ r^(1/16:ℝ):=le_trans (show 4*X≤ (n:ℝ)^(1/16:ℝ) from y) (by gcongr)
 have H: F.deg ≤ 4:= by unfold deg; split <;> norm_num
 have hx: F.pulseBase L ≤ X*r^4:=by rw [pulse_power]; gcongr -- tune
 have hi:sprintCost L=r^(79/16:ℝ):=rfl
 have he'(a:ℝ)(s:Real):r^a*r^s=r^(a+s):= (Real.rpow_add hp a s).symm
 have hw:4*X*r^4 * r^(7/8:ℝ) ≤ sprintCost L:= calc
    _ ≤ r^(1/16:ℝ)*r^4*r^(7/8:ℝ):=by gcongr
    _ = sprintCost L:=by rw [←Real.rpow_ofNat r 4,he',he',hi]; norm_num -- `(r:ℝ)`?
 have ht:F.pulseBase L/sprintCost L ≤ (1/2:ℝ):=by
    apply (div_le_iff₀ (sprint_pos L)).2; have he' := (le_mul_of_one_le_right (show 0≤4*X*r^4 by positivity) (Real.one_le_rpow k (by norm_num : (0:ℝ) ≤ 7/8))).trans hw; linarith only [hx,he',(sprint_pos L)] -- shadow hx(x geom)
 refine ⟨ht,?_, hw⟩
 have hx₁:=zero_le_one.trans u; unfold pulseHidden
 let U:=nullLoss L; have hv:0<U:=null_pos _; let W':=128*ε1*X; have v:0≤W':=by unfold W'; positivity
 change W'*(F.pulseBase L*(W* U))≤ _
 calc
    _ ≤ W'*(X*r^4*(W* U)):=by gcongr
    _ = 128*ε1*X*X*W/r:=by unfold W' U; rw [show nullLoss L=r⁻¹^5 from rfl]; field_simp
    _ ≤ _:= by
         change 128*ε1*X*X*W*16≤(n:ℝ) at c
         apply (div_le_iff₀ hp).mpr; linarith only [c.trans (show (n:ℝ)≤r from ‹_›)] -- shadow hx needed

-- portfolios.Z_rec. Build TL chain from ℕ.Positivity sum weights.B recurrence expressed via interpol composed U and IEM.Elapsed maturity `t=j-s0`.
variable {η :Type}[Fintype η][DecidableEq η](R:ℕ→ Reflow ι η)
local notation "Δ" i:max => (R i).U.symm
-- use composition notation .trans
noncomputable def slip (s j:ℕ) : Coords ι≃ₗ[ℝ]Coords ι:= Nat.rec (.refl ℝ _) (fun j a=> a.trans ((R (s+j)).U.symm)) j -- ascending composition
lemma slip_one(s j:ℕ): slip R s (j+1)=(slip R s j).trans (R (s+j)).U.symm:=rfl
lemma slip_back(s j:ℕ): slip R s (j+1)= (Δ s).trans (slip R (s+1) j):=by induction j with| zero=>rfl| succ k ih=> rw [slip_one,ih,slip_one R (s+1),←Nat.add_assoc s _,Nat.add_right_comm s k 1]; rfl
lemma slip_arrive (s j k:ℕ) : slip R s (j+k)=(slip R s j).trans (slip R (s+j) k):=by induction k with| zero=>rfl | succ k ih=> rw [←Nat.add_assoc,slip_one,ih,slip_one R (s+j),←Nat.add_assoc s]; rfl

local notation "P'"=> F.pulseBase L
local notation "U'" => sprintCost L
local notation "W'" =>F.pulseHidden L C K A
-- Define frontend coefficient Z by ascending from s to g updating last leak only. recursion prefix.Z'= leak high + μ^-1 * Δ_high Z.
noncomputable def jetlag (s j:ℕ)(x:η): Coords ι:= Nat.rec 0 (fun j z=> (R (s+j)).leaks x+(U')⁻¹ • (R (s+j)).U.symm z) j
lemma jetlag_v (s j:ℕ)(x:η): jetlag L R s (j+1) x=(R (s+j)).leaks x+(U')⁻¹ • (Δ (s+j)) (jetlag L R s j x):=rfl -- syntax
lemma jetlag_stop (s j k:ℕ)(x:η) : jetlag L R s (j+k) x=jetlag L R (s+j) k x+(U'⁻¹)^k • slip R (s+j) k (jetlag L R s j x):=by induction k with
 | zero=> erw [show jetlag L R (s+j) 0 x=0 from rfl,pow_zero,one_smul,zero_add]; rfl -- indentation
 | succ k ih=> rw [←Nat.add_assoc,jetlag_v,ih,jetlag_v L R (s+j),slip_one R (s+j) k,pow_succ', ←Nat.add_assoc s]; simp only [LinearEquiv.trans_apply]; rw [map_add,map_smul,smul_add, smul_smul,add_assoc]; abel
variable {F C K A}{L} {κ θ τ:ℕ→ℝ}{P Q:ℕ→BudgetPoint}{R:ℕ→Reflow ι η} {s j:ℕ} (x:∀ i:ℕ,i<j→Economics F C K A L (P i) (Q i) (κ i) (θ i) (τ i) (R (s+i)))
include x
lemma jet_e (p:1 ≤ C)(q:1≤ K)(l:1≤ A)(s₀: PantryFin ι F L A C K)(z:η) : ‖jetlag L R s j z‖ ≤2* W':=by
 have hx:= s₀.loss; have h:=sprint_pos L; let w:=W'; have hw:0<w:=mul_pos (div_pos receipt_pos (F.chi_pos _)) (mul_pos (accuracy_pos C K A p q l) (null_pos _)); induction j with
 | zero=> exact (show ‖(0:Coords ι)‖=0 from norm_zero).le.trans (show 0≤2*w by positivity)
 | succ k ih=>
    let e:=x k (by omega); have hv:= ih (fun i v=> x i (by omega)); rw [jetlag_v]; apply le_trans (norm_add_le ..); rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr h)]
    apply (add_le_add (e.bek z) (mul_le_mul_of_nonneg_left ((e.sail _).trans (mul_le_mul_of_nonneg_left hv (div_pos receipt_pos (F.chi_pos _)).le)) (inv_nonneg.mpr h.le))).trans; rw [div_eq_inv_mul] at hx
    nlinarith only [mul_le_mul_of_nonneg_right hx hw.le]
-- spend sprint differentiation chains; norm limits use inverse.R.Aspect.
lemma slip_e (v:Coords ι): ‖slip R s j v‖ ≤ P'^j*‖v‖:=by
 induction j with
 | zero=> rw [pow_zero,one_mul]; exact le_refl _
 | succ k ih=>
    have he:= ih (fun i v=> x i (by omega)); rw [pow_succ',mul_assoc]; exact ((x k (by omega)).sail _).trans (mul_le_mul_of_nonneg_left he (div_pos receipt_pos (F.chi_pos _)).le)
#print axioms slip_e
end ResolutionFrame
end ShapeLab
end YM.CF.QuadClock
