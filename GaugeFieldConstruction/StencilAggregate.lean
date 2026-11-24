import GaugeFieldConstruction.AuldΘJ
import GaugeFieldConstruction.LunaraR
import GaugeFieldConstruction.FlorinBowNX
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Spine
open Aria Casting Six
open CF.Velvet CF.Pannier.Chancel Pitching.Focus
open YM.CF.Oath.BellPrice CF.Fief
open Oath
open Papal AUbard
open Papal FrameP Yoke.Promena WorldJ Frugal CF.Scroll MirrorCost
open Py Yoke.Promena
open CF.Neon CF.XGarden CF.XGarden.MastTin CF.XGarden.MastTin.ArtCart
open CF.TableF CF.TableF.Lenten CF.XGarden CF.XGarden.Shield
open WorldJ
open scoped YM.CF.Mew
open Pitching.Focus.CoeffArc TableF TableF.Lenten TableF.Lenten.Layout TableF.Lenten.Layout.Fren
open Ing Ing.Ivey CF.XGarden.MastTin
open CF.Pastry CF.Hive
open CF.Scroll
namespace RosterJ
namespace BoonsθJ
variable {P:Spine}{n:ℕ} {θ:BandS→ℕ}{G:ℝ}{f0:ℕ}(p:RosterJ P θ G f0)
variable (B0:SωJ θ)(M:JωL θ)(R:Signed × Bool)(u:BandS)(pu:Adept_T θ B0 M G)
  (A: CalendarJ p B0 M) (T:LampHouseJ (θ:=θ) u) (D:P.Heritor) (V:LampΤJ p B0 M (0:P.VMark) R u A T D.path)
variable {I:Type*}[Fintype I] (Q : I → BeaconNX n)
local notation "Κ"=> Panmart p B0 M 0 R u pu A T D V f0 le_rfl
local notation "Δ" s:max i:max => FingerprintNX P u s i
local notation "Φ" i:max=> P.plaqueStakeNX (Q i)
variable (W:SocietyNX P p)(ε:Fin (θ u))(z:ℕ→I→ℂ)
open Submodule Lead
private lemma scent_sum {i:Axis} (A:I→P.Test)(X:I→P.Slabs i)(σ τ: PermWallJ P)(v:Finset I) (u:∀ k∈v,CallBoxJ (0:P.VMark) σ τ i (A k) (X k) n): CallBoxJ (0:P.VMark) σ τ i (∑ k∈v,A k) (∑ k∈v,X k) n:= by
 induction v using Finset.induction with
 | empty=> simpa [CallBoxJ] using ((UnitWallJ (P:=P) 0 σ τ i n).minus (UnitWallJ 0 σ τ i n))
 | insert j v e ht=> simp only [sum_insert e]; exact (u j (mem_insert_self ..)).plus (ht (fun i p=>u i (mem_insert_of_mem p)))
include p u W ε T
-- nonempty I needed? no choose.
def marksPriced (P:Spine)(F:ℕ→P.Test)(X:ℕ→ScreensJ P):Prop:=∀ (j:Axis)(σ τ:PermWallJ P), ∃ A:ℕ→P.Slabs j,(∀ᶠ i in atTop,CallBoxJ 0 σ τ j (F i) (A i) i)∧ Tendsto (fun i=> A i-X i j σ τ) atTop (𝓝 0)
lemma marksCombine
    (h:∀ k (A:ℝ)(g:f0≤ k)(i:I), Tendsto (fun s:ℕ=> ‖z s i‖*(A*FingerprintNX P u k s)) atTop (𝓝 0)):
    ∃ F: ℕ → ScreensJ P, (∀ i, F i∈ Κ) ∧ marksPriced P (fun i=>∑ k:I,z i k • P.plaqueStakeNX (Q k)) F:=by
 choose m a p₁ hs using fun i=> StampClockNX p B0 M R u pu A T D (Q i) W ε V
 let f(i:I)(k:ℕ):ScreensJ P:= if x:m i≤ k then (hs i k x).choose else 0
 have hv(i k): f i k ∈ Κ:= by
    unfold f; split
    next h=> exact (hs i k h).choose_spec.1
    next h=> exact (Κ).zero_mem
 let g(k:ℕ):=∑ i:I, z k i • f i k; refine ⟨g,(fun k=> (Κ).sum_mem fun i _=> (Κ).smul_mem _ (hv i k)),?_⟩
 intro j σ τ; let d(i:I)(k:ℕ):= costΞJ P j 0 k σ τ (Φ i); let Xq(k:ℕ):=∑ i:I,z k i • d i k; refine ⟨Xq,?_,?_⟩
 all_goals obtain ⟨t,pt,a₀,V'⟩:= ((eventually_ge_atTop f0).and ((farWallJ σ τ).and (eventually_all.mpr fun x=> eventually_ge_atTop (m x)))).exists
 all_goals have ht(i:I)(k:ℕ)(p:t ≤ k) : CallBoxJ 0 σ τ j (Φ i) (d i k) k ∧ ‖d i k-f i k j σ τ‖ ≤ a i*Δ t k:=by unfold f; rw [dif_pos ((V' i).trans p)]; exact (hs i k ((V' i).trans p)).choose_spec.2 t (V' i) p σ τ j a₀ -- let f.
 · filter_upwards [eventually_ge_atTop t] with k a; exact scent_sum _ _ _ _ _ (fun i _=> (ht i k a).1.scale _)
 have hh:Tendsto (fun k:ℕ=>∑ i:I,‖z k i‖*(a i*Δ t k)) atTop (𝓝 0):=by simpa using tendsto_finset_sum Finset.univ (fun i (_:i∈ Finset.univ)=> h t (a i) pt i)
 rw[tendsto_zero_iff_norm_tendsto_zero]; refine squeeze_zero' (Eventually.of_forall (fun _=>norm_nonneg _)) ?_ hh; filter_upwards [eventually_ge_atTop t] with k p
 simp only [Xq,g, Finset.sum_apply,Pi.smul_apply, ←Finset.sum_sub_distrib, ← smul_sub]; exact le_trans (norm_sum_le ..) (sum_le_sum fun i _=> (norm_smul ..).trans_le (mul_le_mul_of_nonneg_left (ht i k p).2 (norm_nonneg _)))
#print axioms marksCombine
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
