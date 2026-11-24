import SatinFixedContrastNovember4
import YM.SU5.Assay.Trellage
import YM.SU5.Assay.Audit
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set OS.Semigroup Ballad Six
variable (P:Spine)(R:P.Register)(x:P.Spectrum0 3)
local notation "Zs"=>Ballad.Lead.Clan
local notation "κ"=>P.coffee 3 x
local notation "σ"=>P.rawSlot 3 x
local notation "β"=>P.base 3 x
local notation "Ω"=>P.heaven 3 x
local notation "O"=>(P.ManyF 3 x).Op
local notation "⟪" T "⟫"=> inner ℂ Ω ((T:O) Ω)
local notation "L"=>P.LagOp 3 x
variable (A : Lead.Clan → ℕ→P.Apron)(l:Lead.Clan→ℕ→P.Folio)(T:Lead.Clan→P.LagOp 3 x)
variable (B : Lead.Clan → ℕ→P.Apron)(m:Lead.Clan→ℕ→P.Folio)(U:Lead.Clan→P.LagOp 3 x)
-- PRE argument order for future
open DoseTravel TopologicalSpace
variable {P R x A B l m T U}{D N:Doorway}{s n:ℕ}{o:Orders}
variable {F G:SampleDose}{f g:ℕ→SampleDose}{i j t:ℕ→ℕ}
variable (p:P.Assay R x s n D N o F G A B l m T U)
local notation "a"=>(D.lower 3)
local notation "b"=>(D.turnCut N)
local notation "c"=>(N.upper 3)
local notation "R1"=>litRow 3 a b 0
local notation "R2"=>litRow 3 b c 0
/-! Uniform C⁰ perturbations **also** pay prices. Used on mixtures if choosing
 old-test commitments. Not changing the commitments themselves or compensating
 for any drift in clock/body/character. Use closed spare zones for C⁰ chamber costs.
-/
namespace Doorway
def plot (D:Doorway):Compacts Vantage:= ⟨closure D.spare.invites,D.spare.doorSeal.symm ▸ D.spare.door_compact⟩
lemma plots (u:D.Later N o 0):(D.plot:Set Vantage)⊆R1∧(N.plot:Set Vantage)⊆R2:=by
 obtain ⟨y,z⟩:=u.split
 constructor
 · intro i t;obtain ⟨p,q⟩:=D.sparesDoor t 3 trivial; exact ⟨sub_pos.mpr p,sub_pos.mpr (q.trans y)⟩
 · intro i t;obtain ⟨p,q⟩:=N.sparesDoor t 3 trivial; exact ⟨sub_pos.mpr (z.trans p),sub_pos.mpr q⟩
-- trivials normalization
abbrev Suitable (D:Doorway)(F:SampleDose):=tsupport F.val⊆D.spare.invites∧F.Normalized
def Rival (D:Doorway)(F:SampleDose)(f:ℕ→SampleDose):Prop:= (∀i,D.Suitable (f i)) ∧ D.Suitable F∧∀ε>0,∀ᶠ i in atTop,AltNear ε F (f i)
end Doorway
lemma SeedBook.rival {M I:Type*}[NormedAddCommGroup M][NormedSpace ℝ M]{r:I→ SampleDose → M}{Z:Row}
 (h:SeedBook Z r)(v:(D.plot:Set Vantage)⊆Z)(p:D.Rival F f)(i:ℕ→I):
 Tendsto (fun k=>‖r (i k) (f k)-r (i k) F‖) atTop (𝓝 0):=by
 obtain ⟨cc,n,z⟩:=h.cash _ v
 have qD:∀f:SampleDose,D.Suitable f→tsupport f.val⊆D.plot:=fun f t=>Subset.trans t.1 subset_closure
 refine Metric.tendsto_nhds.mpr fun ε t=>?_
 let u:=ε/(cc+1); have w:0<u:=div_pos t (by linarith)
 have y:cc*u<ε:=by calc
   _ < (cc+1)*u:=mul_lt_mul_of_pos_right (lt_add_one _) w
   _ = _:=mul_div_cancel₀ _ (by linarith :cc+1≠0)
 filter_upwards [p.2.2 u w] with k aa
 let x':=germinate ((qD _ (p.1 k)).trans v); let y':=germinate ((qD _ p.2.1).trans v)
 let M':=extract (x'-y')
 have ht:tsupport M'.val⊆ D.plot:= (tsupport_sub ..).trans (union_subset (qD _ (p.1 k)) (qD _ p.2.1))
 have he:r (i k) M'= r (i k) (f k)-r (i k) F:=by
    have e:=h.seeds (i k) x' y' (x'-y') 1 (-1) (by simp [sub_eq_add_neg]); rw [neg_smul,one_smul,one_smul] at e
    exact e.trans (sub_eq_add_neg ..).symm
 rw [dist_zero_right,norm_norm,←he]
 exact (z _ _ ht _ w.le (fun q=>(aa q).le)).trans_lt y

local notation "Old"=>(P.arrayReading x s n b)
include p
lemma Assay.alter (J:P.Ellis 3 x)(u:D.Rival F f)(v:N.Rival G g) {Paid:Set CrossRead}(z:Paid∈𝓝 (Old F G)):
 ∀ᶠ k in atTop, Old (f k) (g k)∈Paid ∧ P.Assay R x s n D N o (f k) (g k) A B l m T U:=by
 have t:=p.old.taps
 obtain ⟨e,y,h⟩:=P.near_wall x s n b F G _ _ D.plot.isCompact N.plot.isCompact
  (u.2.1.1.trans subset_closure) (v.2.1.1.trans subset_closure) _
  (inter_mem z (readsSix_open.mem_nhds p.old.paid.poles))
 filter_upwards [u.2.2 e y,v.2.2 e y] with k w r
 obtain ⟨ψ,φ⟩:=u.1 k; obtain ⟨γ,phi⟩:=v.1 k
 obtain ⟨P',I⟩:=h _ _ (ψ.trans subset_closure) (γ.trans subset_closure) w r
 have ht:∀Z,P.WallBefore (P.RTest Z s n) (f k) b:=fun _=> Walled.WallBefore (Doorway.first t.left ψ t.sep)
 have hu:∀Z,P.WallAfter (P.FTest Z s n) (g k) b:=fun _=> Walled.WallAfter (Doorway.second t.right γ t.sep)
 exact ⟨P',t.portrait R J φ phi ψ γ (P.paidReturn x s n b _ _ ht hu J I t.extent),p.early,p.late⟩
-- NB notation a b c with trailing literals needs ()
lemma Assay.alterFine (J:P.Ellis 3 x)(u:D.Rival F f)(v:N.Rival G g)(e:Tendsto t atTop atTop):
 Tendsto (fun k=>P.arrayFine x s n (t k) (f k) (g k)) atTop (𝓝 (Old F G)):=by
 refine tendsto_pi_nhds.mpr fun Z=>tendsto_pi_nhds.mpr fun W=>?_
 let I:= P.RTest Z s n;let L':=P.FTest W s n
 have α:= (prior_shelf (x:=x) (a) (b) I R1).rival (Doorway.plots p.old.taps.sep).1 u (fun k=>((),t k))
 have α':=(prior_shelf (x:=x) (b) (c) L' R2).rival (Doorway.plots p.old.taps.sep).2 v (fun k=>((),t k))
 have θ:= (((P.grid_base _ _ (P.metered _ x R) I (a) (b) F).visit e).squeeze' α
      («b»:=fun k=>σ (t k) I (a) (b) (f k)) (Eventually.of_forall fun _=>le_rfl))
 have θ':= (((P.grid_base _ _ (P.metered _ x R) L' (b) (c) G).visit e).squeeze' α'
      («b»:=fun k=>σ (t k) L' (b) (c) (g k)) (Eventually.of_forall fun _=>le_rfl))
 rw [(p.old.old_brew Z W _ _ _ p.old.old_walls.1 p.old.old_walls.2).2]
 refine (θ.mul θ').price.congr' ?_
 filter_upwards [p.alter J u v univ_mem,e.eventually (eventually_ge_atTop s)] with k h r
 exact (h.2.old.old_fee Z W _ _ _ h.2.old.old_walls.1 h.2.old.old_walls.2 _ r).2.symm
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
