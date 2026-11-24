import SatinProbeCompatibilityNovember6
import YM.SatinExist.Liber
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 280000
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
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open OS.Semigroup (F)
open OS.Semigroup.Balloon
open Set
variable (P:Spine)(x:P.Spectrum0 3)(Z:Lead.Clan)(k:Street)(s:ℕ)(c r:ℕ→ℕ)
local notation "β" => P.otherSpectrum 3 3 x
local notation "S" => P.physicalEnergy 3 (β)
local notation "V" => P.ColorHil 3 (β)
local notation "Ψ" => P.voyageF 3 (β)
local notation "yb@" i:max=> P.shard x Z (c (i:ℕ)) (r (i:ℕ))
local notation "ρ" i:max=> P.dew (c (i:ℕ)) (r (i:ℕ))
local notation "Γ" => marks (timeMesh P.par)
local notation "Nt" => notch (timeMesh P.par)
open Aria Casting Six
local notation "H"=> P.ColorHil 3 (β)
local notation "B"=> P.par.block
local notation "l₀"=> P.width
local notation "Λ"=> P.par
local notation "K"=> P.calibration
local notation "q@" n:max => P.asked_at n
local notation "ρₛ" t:max=> Selected.gaugeMesh Λ t
local notation "θ" t:max => Selected.gaugePosition Λ t
local notation "ℓ"=> P.calibration.ℓ
-- horizontal/integer growth from ANY mixed roster, keeping every stencil at SAME height. useful later for pure/pure.
variable (j:Axis)
local notation "ϕ"=> P.singleState 3 s x
local notation "ξ"=> P.advocate 3 x j
local notation "ω"=> P.ColorHil j ξ
local notation "e₀"=> P.physicalEnergy j ξ

def Prized {I:Type}[Fintype I][DecidableEq I](A:Matrix I I ℂ) := A.det≠0 ∧ ∀ i,A i i ≠0
variable {I:Type}[Fintype I][DecidableEq I]
section laurels
variable (F G: I→  P.Test)
def ticketGold : Matrix I I ℂ := Matrix.of (fun i j=> ϕ (F i * G j))
lemma strollPrice (e:∀ i,P.birthF j s (P.reflectTest j (F i))) (f:∀ i,P.birthF j s (G i)) (h:Prized (P.ticketGold x s F G)) :
    ∃ᶠ n:ℕ in atTop, Prized (P.ticketGold x s F (fun i=> P.shifts j (n:ℤ) (G i))) := by
 let X(i):= P.viewF j ξ s (e i); let Y(i):= P.viewF j ξ s (f i)
 let Q:= _root_.YM.SatinExist.Lancet.ahead (e₀) X Y; let L:= mill (timeMesh Λ) s
 have Hp(n:ℕ): P.ticketGold x s F (fun i=> P.shifts j (n:ℤ) (G i))=Q (n * (L:ℝ)) := by
    have ht:(((n:ℝ)*(L:ℝ)).toNNReal)= whenly (timeMesh Λ) s n:= by ext; unfold whenly; push_cast; rw [Real.coe_toNNReal _ (by positivity)]
    ext a b
    change ϕ _=inner ℂ (P.viewF j ξ s (e a)) ((e₀).E _ _)
    rw [P.mint_ordered_label x s j (F a) (G b) (e a) (f b) n,ht]
 have hv : Q 0=P.ticketGold x s F G:=by
    rw [show (0:ℝ)=(0:ℕ)*(L:ℝ) by simp,←Hp]; simp_rw [Nat.cast_zero,P.shifts_zero]
 let Z:= _root_.YM.SatinExist.Lancet.happy_clock e₀ X Y (show Prized (Q 0) from hv.symm ▸ h) (L:ℝ) (mill_pos ..) -- tune
 exact Z.mono fun i q=> (Hp i).symm ▸ q
private lemma translated_billl (p:ℤ): P.ticketGold x s (fun i=> P.shifts j p (F i)) G= P.ticketGold x s F (fun i=>P.shifts j (-p) (G i)):=by
 ext i k; change ϕ _=ϕ _
 rw [← P.stamp_title x s j (-p) _,map_mul,P.shifts_sum,neg_add_cancel,P.shifts_zero]
lemma pre_strollPrice (e:∀ i,P.birthF j s (P.reflectTest j (F i))) (f:∀ i,P.birthF j s (G i)) (h:Prized (P.ticketGold x s F G)) :
    ∃ᶠ n:ℕ in atTop, Prized (P.ticketGold x s (fun i=> P.shifts j (-(n:ℤ)) (F i)) G) := by
 refine (P.strollPrice x s j F G e f h).mono (fun i p=> ?_); simpa only [translated_billl,neg_neg] using p
end laurels
structure EarshotAlpha (U: Finset Cover)(F:I→P.Test): Prop where
 sectionP(i:I) : F i ∈ bay P.calibration U false ∧ F i∈ enclave K ∧ P.singleState 3 s x (F i)=0 ∧ PureMatter K (F i)
variable (p:ℤ)
local notation "lm@" n:max U:max=> plow K j (n:ℤ) U
local notation "T@" n:max F:max=> fun (i:I)=> P.shifts j (n:ℤ) (F i)
namespace EarshotAlpha
variable {P x s} {F G:I→ P.Test}{U:Finset Cover}(S':EarshotAlpha P x s U F)
-- all-stamp relocation; SHIFT for same meter
include S'
lemma invoice (i:I) : F i ∈ bay P.calibration U true:=
 (Tapestry.locates ..).2 (((Tapestry.locates ..).1 (S'.sectionP i).1).widen)
lemma plus (p:ℤ) : EarshotAlpha P x s (plow P.calibration j p U) (T@ p F) :=
 ⟨fun i=>⟨P.shifts_support j _ _ (S'.sectionP i).1, P.shifts_keep _ _ (S'.sectionP i).2.1,(P.stamp_title x s j p _).trans (S'.sectionP i).2.2.1,P.copyIndependent j (S'.sectionP i).2.2.2 p⟩⟩
variable {L:Finset Axis} (v:0 ≤ p)
include v
lemma view_as (t:Punctus (P:=P) true L p U)(i:I): P.birthF j s (F i):= by
 refine P.criteria j s (S'.invoice i) (fun z x=>?_) (S'.sectionP i).2.1
 have hz:=t z x j; simp only [ite_true] at hz; split at hz<;> omega
lemma past_as (t:Punctus (P:=P) false L p U)(i:I): P.birthF j s (P.reflectTest j (F i)):= by
 refine P.criteria j s (P.canFlip _ _ (S'.invoice i)) ?_ (P.mirror_keeps j _ (S'.sectionP i).2.1)
 intro z q'; obtain ⟨w,g,t'⟩:= reflect_stays j 0 U q'; rw [t',if_pos rfl]; have hp:=t w g j; simp only [Bool.false_eq_true,ite_false] at hp; split at hp<;> omega
end EarshotAlpha
variable {L:Finset Axis}{Sx Fx:Finset Cover}
local notation "P*"=> @Punctus P
-- maintain representation not lost. just shifts of very same mark.
variable {F G:I→ P.Test}
noncomputable def amplot(F:I→P.Test)(D:Finset Cover) (L:List (Axis×ℤ)): I→ P.Test:= L.foldr (fun i Uq=> (fun x=> P.shifts i.1 i.2 (Uq x))) F
lemma amplop (z: Finset Cover)(D: List (Axis×ℤ))(F:I→ P.Test) (U:EarshotAlpha P x s z F):P.EarshotAlpha x s (P.zoneCost z D) (P.amplot F z D):=by
 induction D with| nil=> exact U| cons i L h=> exact h.plus i.1 i.2 -- implicit args
private lemma next_stamped (m:ℤ)(D D': Finset Axis)(u:j ∈ D')(p:Punctus (P:=P) false D' m Fx)(q:Punctus (P:=P) true D m Sx)(h:Prized (P.ticketGold x s F G))(v:0 ≤ m)(H':P.EarshotAlpha x s Fx F)(k:P.EarshotAlpha x s Sx G): ∃ n:ℕ, Punctus (P:=P) true (insert j D) m (lm@ n Sx) ∧ Prized (P.ticketGold x s F (T@ n G)):=
 ((P.stroll_area j m q).and_frequently (P.strollPrice x s j _ _ (H'.past_as j m v p) (k.view_as j m v q) h)).exists
-- calibrated gap increases from any starting in open axes along exactly same stamp meter. thus matter/literal preserved
lemma blazeC (m:ℤ)(v:0 ≤ m)(H':P.EarshotAlpha x s Fx F)(k:P.EarshotAlpha x s Sx G) (p:Punctus (P:=P) false ∅ m Fx)(q:Punctus (P:=P) true ∅ m Sx)(t:Prized (P.ticketGold x s F G)) :
    ∃ L L':List (Axis×ℤ), let R:= P.zoneCost Fx L; let R':= P.zoneCost Sx L'; Punctus (P:=P) false Finset.univ m R ∧ Punctus (P:=P) true Finset.univ m R' ∧ Prized (P.ticketGold x s (P.amplot F Fx L) (P.amplot G Sx L')):=by
 suffices he:∀ D:Finset Axis,∃ L L', (P*) false D m (P.zoneCost Fx L) ∧ (P*) true D m (P.zoneCost Sx L') ∧ Prized (P.ticketGold x s (P.amplot F Fx L) (P.amplot G Sx L')) from he Finset.univ
 intro D; induction D using Finset.induction_on with
 | empty=> exact ⟨[],[],p,q,t⟩
 | @insert j L h ih=>
    obtain ⟨R,Z,p,q,t⟩:=ih; let f:= P.amplot F Fx R; let g:= P.amplot G Sx Z
    let U:= P.zoneCost Fx R
    let h':= P.amplop x s Fx R F H'; let w:=P.amplop x s Sx Z G k
    obtain ⟨n,a,b⟩:= ((P.recoil_area j m p).and_frequently (P.pre_strollPrice x s j _ _ (h'.past_as j m v p) (w.view_as j m v q) t)).exists
    let R₀:= (j,-(n:ℤ))::R
    obtain ⟨i,t',v'⟩:= P.next_stamped x s j m L (insert j L) (Finset.mem_insert_self ..) (p:=a) q b v (P.amplop x s Fx R₀ F H') w
    exact ⟨R₀, (j,(i:ℤ))::Z, a, t', v'⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
