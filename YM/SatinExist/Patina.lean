import YM.SatinExist.Cuspida
import YM.SatinExist.Liber
import YM.SatinExist.Tickets
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
open FirstWindows
-- complete footprint; stamps may move *far larger* still on same height. charge budget in this earmarked mass.
local notation "Π" i:max => Selected.gaugePosition Λ s i
variable (p:ℝ)
lemma length_funds (T:Finset Cover)(q:ℤ)(t:p < (q:ℝ)*Selected.gaugeMesh Λ s)(v:Punctus (P:=P) true Finset.univ q T) : P.pinFoot s T ⊆ {x|∀ j:Axis,p< x j}:=by
 rw [P.foyer_foot]; intro x h j; obtain ⟨a,k,r⟩:= Set.mem_iUnion₂.mp h; rw [shield_region_exact] at r; refine lt_of_lt_of_le t ((?_: _≤ Selected.gaugePosition Λ s a j - (ℓ:ℝ)*ρₛ s).trans (r j (Set.mem_univ _)).1); let G:= v a k j; simp only [ Finset.mem_univ, ite_true] at G
 change (q:ℝ)*_ ≤ _; unfold Selected.gaugePosition; have e: (ℓ:ℝ)+(q:ℝ)≤ (a j:ℝ):=by exact_mod_cast G.le
 linarith only [mul_le_mul_of_nonneg_right e (Selected.gaugeMesh_pos Λ s).le]
lemma neg_funds (T:Finset Cover)(q:ℤ)(t:p < (q:ℝ)*Selected.gaugeMesh Λ s)(v:Punctus (P:=P) false Finset.univ q T) : P.pinFoot s T⊆ {x|∀ j:Axis,x j < -p}:=by
 rw [P.foyer_foot]; intro x h j; obtain ⟨a,k,r⟩:= Set.mem_iUnion₂.mp h; rw [shield_region_exact] at r; apply lt_of_le_of_lt (r j (Set.mem_univ _)).2; apply lt_of_le_of_lt _ (neg_lt_neg t)
 let G:= v a k j; simp only [Bool.false_eq_true, Finset.mem_univ,ite_false, ite_true] at G
 change Selected.gaugePosition Λ s a j + (ℓ:ℝ)*ρₛ s ≤ -_; unfold Selected.gaugePosition; have he:(a j:ℝ)+(ℓ:ℝ)≤ -(q:ℝ):=by exact_mod_cast G.le
 linarith only [mul_le_mul_of_nonneg_right he (Selected.gaugeMesh_pos Λ s).le]
lemma zone_one (Sx:Finset Cover)(z:Cover)(e:Sx={z}) (L:List (Axis×ℤ)): ∃ z, P.zoneCost Sx L={z}:=by
 induction L with
 | nil=> exact ⟨z,e⟩
 | cons i L h=> obtain ⟨z,hz⟩:=h; change ∃ v, plow K i.1 i.2 (P.zoneCost Sx L)={v}; rw [hz]; unfold plow address; simp
-- Our initial-height heights and r. Use truly on-site mark with *same* R & spin, arbitrary motions as allowed. At large i CP18 roll;
-- no claim those movements' lengths remain bounded uniformly in i or charges
local notation "Lt" v:max i:max=> discrete (r i) v
local notation "St" i:max v:max => ({nodeC (Lt v i)}:Finset Cover)
local notation "Ft" i:max v:max a:max => P.centeredSun x (c i) (P.equinox a (Lt v i) (r i))
local notation "C@" i:max A:max Y:max L:max => P.Earshot x (c i) (P.zoneCost A L) (P.amply Y A L) -- implementation test
variable (y z: Gaia)
variable {P x r c}(A:Launch P c r){d:ℕ→ℝ}(h:readyUV P c r x d)(u:Tendsto d atTop (𝓝 0))
include A
private lemma round_height (v:0 < y j) : Tendsto (fun i=>discrete (r i) y j) atTop atTop :=by
 let z:=y j; let f(i:ℕ):ℝ:= r i; have g:Tendsto (fun i=> f i*z) atTop atTop:=(tendsto_natCast_atTop_atTop.comp A.eager.tendsto_atTop).atTop_mul_const v
 apply Filter.tendsto_atTop.2; intro a; filter_upwards [g.eventually_ge_atTop (a:ℝ)] with i p; exact Int.le_floor.mpr p
private lemma round_night (v:y j<0) : Tendsto (fun i=>discrete (r i) y j) atTop atBot:=by
 let z:=y j; let f(i:ℕ):ℝ:= r i; have g:Tendsto (fun i=> -(f i*z)) atTop atTop:=((tendsto_natCast_atTop_atTop.comp A.eager.tendsto_atTop).atTop_mul_const (neg_pos.mpr v)).congr fun i=> mul_neg ..
 apply tendsto_atBot.2; intro a; filter_upwards [g.eventually_ge_atTop (-(a:ℝ))] with i p; apply (Int.cast_le (R:=ℝ)).mp; exact (Int.floor_le ((r i:ℝ)*z)).trans (le_of_neg_le_neg p)
private lemma rising_price (v:∀ i:Axis,y i<0)(t:∀ i:Axis,0< z i) : ∀ᶠ i:ℕ in atTop,∀ m:ℤ,Punctus (P:=P) false ∅ m (St i y) ∧ Punctus (P:=P) true ∅ m (St i z):=by
 have ho(j:Axis):= Filter.Eventually.and ((round_night j y A (v j)).eventually (eventually_lt_atBot (-(ℓ:ℤ)))) ((round_height j z A (t j)).eventually_gt_atTop (ℓ:ℤ))
 filter_upwards [eventually_all.mpr ho] with i e m
 constructor <;> intro x u j <;> obtain rfl:= Finset.mem_singleton.mp u <;> simp [nodeC] <;> have hp:=e j <;> omega
omit A
variable (P x c r)
private lemma centered_mat (i:ℕ): P.Earshot x (c i) (St i y) (fun k=> Ft i y k):=by
 constructor
 intro a
 let S':=P.equinox a (Lt y i) (r i)
 obtain ⟨l,b,t⟩:= P.pieces_blue a (Lt y i) (r i)
 let C:= bay K (St i y) false; let H:= enclave K
 let p:= P.singleState 3 (c i) x S'
 refine ⟨C.sub_mem t (C.smul_mem C.one_mem p),H.sub_mem b (H.smul_mem H.one_mem p),P.centeredSun_good ..,fun j x y=>?_⟩
 change S'.val j x-p • 1 = S'.val j y-p • 1
 exact congrArg (·-p • 1) (l j x y)

variable {P x c r}
-- Eu interpreter uses projection θ at same REG consultations; include passage & footprints into D
include u A h
lemma mature_fullbank (v:∀ i:Axis,y i<0)(t:∀ i:Axis, 0<z i):
   ∀ᶠ i:ℕ in atTop, ∀ (a:ℝ), ∃ L₀ L₁:List (Axis×ℤ),
     let Yx:= P.zoneCost (St i y) L₀
     let Zx:= P.zoneCost (St i z) L₁
     let F':= P.amply (fun k=> (Ft i y k)) (St i y) L₀
     let G:= P.amply (fun k=> (Ft i z k)) (St i z) L₁
     P.Earshot x (c i) Yx F' ∧ P.Earshot x (c i) Zx G ∧
      (∃ z, Yx={z}) ∧ (∃ z,Zx={z}) ∧ P.pinFoot (c i) Yx⊆ {x|∀ j:Axis,x j < -a} ∧
      P.pinFoot (c i) Zx ⊆ {x|∀ j:Axis, a < x j} ∧ ReadsSix (P.ticketRank x (c i) F' G) :=by
 filter_upwards [rising_price y z A v t,mature_six A h u y z ((v _).trans (t _))] with i l hp a
 let e:= Selected.gaugeMesh P.par (c i); have he:0<e:= Selected.gaugeMesh_pos ..
 obtain ⟨w,g⟩:= exists_nat_gt (a/e); let m:ℤ:= w; have hk:a< (m:ℝ)*ρₛ (c i):=by unfold m; push_cast; exact (div_lt_iff₀ he).mp g
 let H:= P.centered_mat x c r y i -- arg order
 let S':=P.centered_mat x c r z i
 obtain ⟨U,A0,p,v,h⟩:= P.blaze x (c i) m (by unfold m; omega) H S' (l m).1 (l m).2 hp
 exact ⟨U,A0,P.ampp x (c i) _ U _ H,P.ampp x (c i) _ A0 _ S',P.zone_one _ _ rfl U,P.zone_one _ _ rfl A0,P.neg_funds (c i) a _ m hk p,P.length_funds (c i) a _ m hk v,h⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
