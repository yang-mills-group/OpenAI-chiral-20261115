import YM.SatinExist.Purchaser
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
local notation "VS" => P.ColorHil 3 (β)
local notation "Ψ" => P.voyageF 3 (β)
local notation "yb@" i:max=> P.shard x Z (c (i:ℕ)) (r (i:ℕ))
local notation "ρ" i:max=> P.dew (c (i:ℕ)) (r (i:ℕ))
local notation "Γ" => marks (timeMesh P.par)
local notation "Nt" => notch (timeMesh P.par)
open Aria Casting Six
local notation "Hw^"=> P.ColorHil 3 (β)
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
structure Earshot (U: Finset Cover)(F:Lead.Clan→P.Test): Prop where
 sectionP(i:Lead.Clan) : F i ∈ bay P.calibration U false ∧ F i∈ enclave K ∧ P.singleState 3 s x (F i)=0 ∧ PureMatter K (F i)
def Punctus {P:Spine}(b:Bool)(Q:Finset Axis)(k:ℤ)(U:Finset Cover):Prop:= ∀ x∈U, ∀ j:Axis, let δ:=if j∈Q then k else 0
                                                                                       if b then (P.calibration.ℓ:ℤ)+δ < x j else x j+(P.calibration.ℓ:ℤ)< -δ
variable (p:ℤ)
local notation "lm@" n:max U:max=> plow K j (n:ℤ) U
local notation "T@" n:max F:max=> fun (i:Lead.Clan)=> P.shifts j (n:ℤ) (F i)
namespace Earshot
variable {P x s} {F G:Lead.Clan→ P.Test}{U:Finset Cover}(S':Earshot P x s U F)
-- all-stamp relocation; SHIFT for same meter
include S'
lemma invoice (i:Lead.Clan) : F i ∈ bay P.calibration U true:=
 (Tapestry.locates ..).2 (((Tapestry.locates ..).1 (S'.sectionP i).1).widen)
lemma plus (p:ℤ) : Earshot P x s (plow P.calibration j p U) (T@ p F) :=
 ⟨fun i=>⟨P.shifts_support j _ _ (S'.sectionP i).1, P.shifts_keep _ _ (S'.sectionP i).2.1,(P.stamp_title x s j p _).trans (S'.sectionP i).2.2.1,P.copyIndependent j (S'.sectionP i).2.2.2 p⟩⟩
variable {L:Finset Axis} (v:0 ≤ p)
include v
lemma view_as (t:Punctus (P:=P) true L p U)(i:Lead.Clan): P.birthF j s (F i):= by
 refine P.criteria j s (S'.invoice i) (fun z x=>?_) (S'.sectionP i).2.1
 have hz:=t z x j; simp only [ite_true] at hz; split at hz<;> omega
lemma past_as (t:Punctus (P:=P) false L p U)(i:Lead.Clan): P.birthF j s (P.reflectTest j (F i)):= by
 refine P.criteria j s (P.canFlip _ _ (S'.invoice i)) ?_ (P.mirror_keeps j _ (S'.sectionP i).2.1)
 intro z q'; obtain ⟨w,g,t'⟩:= reflect_stays j 0 U q'; rw [t',if_pos rfl]; have hp:=t w g j; simp only [Bool.false_eq_true,ite_false] at hp; split at hp<;> omega
end Earshot
variable {L:Finset Axis}{Sx Fx:Finset Cover}
local notation "P*"=> @Punctus P
lemma stroll_area (u:Punctus (P:=P) true L p Sx) : ∀ᶠ i:ℕ in atTop, (P*) true (insert j L) p (plow K j (i:ℤ) Sx):=by
 -- even ℓ bundling. Use ruler≥1.
 filter_upwards [eventually_ge_atTop p.toNat] with i v; intro x y z
 obtain ⟨q,t,rfl⟩:=plow_stays K j (i:ℤ) _ y; simp only [ite_true]; by_cases h:z=j
 · subst z; specialize u q t j; simp only [ite_true] at u; rw [if_pos (Finset.mem_insert_self ..),SlabMark.moves,if_pos rfl]; have h : (i:ℤ) ≤ ruler (K).B * i:= le_mul_of_one_le_left (by positivity) (ruler_gene _); split at u<;> omega
 specialize u q t z; rw [SlabMark.moves,if_neg h]; simpa only [Finset.mem_insert,h,false_or,ite_true] using u
lemma recoil_area (u:Punctus (P:=P) false L p Sx) : ∀ᶠ i:ℕ in atTop, (P*) false (insert j L) p (plow K j (-(i:ℤ)) Sx):=by
 filter_upwards [eventually_ge_atTop p.toNat] with i v; intro x y z
 obtain ⟨q,t,rfl⟩:=plow_stays K j (-(i:ℤ)) _ y; simp only [Bool.false_eq_true,ite_false]; by_cases h:z=j
 · subst z; specialize u q t j; simp only [Bool.false_eq_true,ite_false] at u; rw [if_pos (Finset.mem_insert_self ..),SlabMark.moves,if_pos rfl]; have h : (i:ℤ) ≤ ruler (K).B * i:= le_mul_of_one_le_left (by positivity) (ruler_gene _); rw [mul_neg]; split at u<;> omega
 specialize u q t z; simp only [Bool.false_eq_true,ite_false] at u; rw [SlabMark.moves,if_neg h]; simpa only [Finset.mem_insert,h,false_or] using u
-- maintain representation not lost. just shifts of very same mark.
variable {F G:Lead.Clan→ P.Test}
noncomputable def amply(F:Lead.Clan→P.Test)(D:Finset Cover) (L:List (Axis×ℤ)): Lead.Clan→ P.Test:= L.foldr (fun i Uq=> (fun x=> P.shifts i.1 i.2 (Uq x))) F
noncomputable def zoneCost (D:Finset Cover)(L:List (Axis×ℤ)):Finset Cover:= L.foldr (fun i Z=> plow K i.1 i.2 Z) D
lemma ampp (z: Finset Cover)(D: List (Axis×ℤ))(F:Lead.Clan→ P.Test) (U:Earshot P x s z F):P.Earshot x s (P.zoneCost z D) (P.amply F z D):=by
 induction D with| nil=> exact U| cons i L h=> exact h.plus i.1 i.2 -- implicit args
private lemma next_stamp (m:ℤ)(D D': Finset Axis)(u:j ∈ D')(p:Punctus (P:=P) false D' m Fx)(q:Punctus (P:=P) true D m Sx)(h:ReadsSix (P.ticketRank x s F G))(v:0 ≤ m)(H':P.Earshot x s Fx F)(k:P.Earshot x s Sx G): ∃ n:ℕ, Punctus (P:=P) true (insert j D) m (lm@ n Sx) ∧ ReadsSix (P.ticketRank x s F (T@ n G)):=
 ((P.stroll_area j m q).and_frequently (P.stroll_price x s j _ _ (H'.past_as j m v p) (k.view_as j m v q) h)).exists
-- calibrated gap increases from any starting in open axes along exactly same stamp meter. thus matter/literal preserved
lemma blaze (m:ℤ)(v:0 ≤ m)(H':P.Earshot x s Fx F)(k:P.Earshot x s Sx G) (p:Punctus (P:=P) false ∅ m Fx)(q:Punctus (P:=P) true ∅ m Sx)(t:ReadsSix (P.ticketRank x s F G)) :
    ∃ L L':List (Axis×ℤ), let R:= P.zoneCost Fx L; let R':= P.zoneCost Sx L'; Punctus (P:=P) false Finset.univ m R ∧ Punctus (P:=P) true Finset.univ m R' ∧ ReadsSix (P.ticketRank x s (P.amply F Fx L) (P.amply G Sx L')):=by
 suffices he:∀ D:Finset Axis,∃ L L', (P*) false D m (P.zoneCost Fx L) ∧ (P*) true D m (P.zoneCost Sx L') ∧ ReadsSix (P.ticketRank x s (P.amply F Fx L) (P.amply G Sx L')) from he Finset.univ
 intro D; induction D using Finset.induction_on with
 | empty=> exact ⟨[],[],p,q,t⟩
 | @insert j L h ih=>
    obtain ⟨R,Z,p,q,t⟩:=ih; let f:= P.amply F Fx R; let g:= P.amply G Sx Z
    let U:= P.zoneCost Fx R
    let h':= P.ampp x s Fx R F H'; let w:=P.ampp x s Sx Z G k
    obtain ⟨n,a,b⟩:= ((P.recoil_area j m p).and_frequently (P.pre_stroll_price x s j _ _ (h'.past_as j m v p) (w.view_as j m v q) t)).exists
    let R₀:= (j,-(n:ℤ))::R
    obtain ⟨i,t',v'⟩:= P.next_stamp x s j m L (insert j L) (Finset.mem_insert_self ..) (p:=a) q b v (P.ampp x s Fx R₀ F H') w
    exact ⟨R₀, (j,(i:ℤ))::Z, a, t', v'⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
