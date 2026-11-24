import YM.SU5.SatinWard.Resolution.Lunar
import YM.SU5.SatinWard.Resolution.Waive
import YM.SU5.SatinWard.Resolution.Belfry
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 700000
set_option maxRecDepth 8000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
open MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
open Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
open scoped ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
open Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus QuadClock Ione Vow Swell
open _root_.Zephyr.Chern
universe uΩ


open Papal CF.Papyrus.Franc.SatinForce CF.Pannier.Chancel Checkers

open CF.Papyrus.Franc.Loaves
-- CP3 package. PUBLIC, no topology/order changes
open Moon
open Horizons FoliageP BareProgram Moonlit Moonlit.SwitchC
open _root_.YM.Regis.Head.Brecht _root_.YM.Regis.Circuit _root_.YM.Regis.Circuit.SpringDay
open SlabMark VelourBoard Papal.SkyTax Cygnet VelourWiggle
open YM.Stationary (Gaia)
open SwitchC.Garland SwitchC.Garland.Terrace SwitchC.Garland.Terrace.Juniper
open Abacus CheckerFlag SlopeCharge Maxwell
open scoped RealInnerProductSpace ContDiff
namespace Fame
open BProof Pressure
namespace Regulator

open _root_.YM.Gleam.Luster.Almanac Grade
open Papal.SkyTax
open _root_.YM.Regis.Head
open _root_.YM.Gleam.Luster.Almanac Grade
open _root_.YM.CF.Py.Rate.LocalLimit.Preparation _root_.YM.CF.Py.Rate.LocalLimit.Preparation.Tabletop Shrine Ione.Clock Moto
variable (P:Spine)
local notation "W★"=>P.calibration
local notation "Ω★"=>P.run.meter
open Preparation.Yoke Spine.Gingham Spine.Gingham.Diary
open ShapeLab ResolutionFrame Shrine 
-- larger apertures for Ward fields.Proofs alongside clock.Heights already installed. uniform all moved roots.
noncomputable abbrev rentWidth (j s:ℕ):ℕ:= P.thresholdF s+12+2*j+petalD
local notation "V$" v:max=>P.clockPlate
local notation "L"=>P.par.R.L
local notation "θ" s:max=>moonSpan P s
local notation "B" v:max=> P.thresholdF v
local notation "ℓ"=> P.calibration.ℓ
variable {w s v j:ℕ}{p:Cover}
structure Closeted (j:ℕ)(p:Cover)(s v w:ℕ) :Prop where
 extent : ∀ a:Axis,Between P.calibration a 0 (ruler P.par.block *P.reachLeaf s v w) (pavilion (P.clockPlate s v p) (rentWidth P j v))
-- j arbitrary smearing. Want extend real relative x.d.Fee model.S.Width
open Worth Pays
local notation "dσ"=> P.calibration.ℓ
local notation "R$" v:max=> rentWidth P j v
lemma thresholdJ (j:ℕ) : ∀ᶠ s:ℕ in atTop, rentWidth P j s+(dσ)+P.sidesPerTick ≤ waitZ P s:=by
 let N:= 12+2*j+petalD+(dσ)+P.sidesPerTick
 filter_upwards [(Yoke.waist P.run 0).eventually (eventually_ge_atTop N)] with s h; unfold waitZ rentWidth; change N≤ (B s) at h; unfold N at h; let he: B s + 1≤ (B s+1)^4:=le_self_pow₀ (by omega) (by norm_num); omega
variable (pL:64≤ P.par.R.L.val)
private lemma big_up :∀ᶠ f0 in atTop,∀ s,Nat.le f0 s→∀ v,s ≤ v→ rentWidth P j v+(dσ) ≤2^(v-s)*(rentWidth P j s+(dσ)):=by
 have ht:∀ᶠ v in atTop, (B (v+1))≤2*B v:=by
    filter_upwards [(turnover P.par).eventually (Extra.Iteration.Rebuild.geometry (billX L))] with v h; let x:= hat P.par.R.L P.par.x v; rw [show B (v+1)= _ from (P.run.meter.boot (v+1)).2.1,show B v= _ from (P.run.meter.boot v).2.1,paceEq]; exact h.1.1
 filter_upwards [eventually_forall_ge_atTop.mpr ht] with N hn s h v x
 induction x with
 | refl=> simp
 | step v' ih=>
    rename_i v; have f:=hn v (Nat.le_trans h v'); rw [Nat.succ_sub v',pow_succ',mul_assoc]; exact le_trans (by unfold rentWidth; omega: R$ (v+1)+(dσ) ≤2*(R$ v+(dσ))) (Nat.mul_le_mul_left 2 ih)
include pL
set_option linter.constructorNameAsVariable false in
lemma narrow_clock (j:ℕ) : ∀ᶠ s in atTop,∀ v,s ≤ v→∀ a:Cover,ResidualPermit a→ ∀ p:Cover, ShowField P s (homeTag P a) p→ Closeted P j p s v (moonSpan P s):=by
 filter_upwards [big_up (j:=j) P,thresholdJ P j] with s ht hm v hu a ha p t
 constructor; intro i x w; change x∈ pavilion (P.clockPlate s v p) (rentWidth P j v) at w
 let o:= P.clockPlate s v p; rw [pav_v _ _ _] at w; specialize w i
 have hs:1≤(P.sidesPerTick:ℤ):= by exact_mod_cast P.sides_pos
 let n:=waitZ P s; let d:ℤ:= P.sidesPerTick*(n:ℤ); let f:= nodeC p i; let u:= P.par.R.L.val^(v-s); let r₁:=rentWidth P j s; let r₂:=rentWidth P j v
 have hℓ: (n:ℤ)≤ d:=le_mul_of_one_le_left (by positivity) hs
 have hx: (ruler P.par.block)*(moonSpan P s:ℕ)=2*d:=by
    unfold d n; rw [pay_half,rulerTicks]; conv_lhs=> rhs; rw [Nat.cast_mul,Nat.cast_ofNat]
    ac_rfl
 have hv': (r₂:ℤ)+(dσ)≤ (u:ℤ)*((r₁:ℤ)+(dσ)):=by
    have he:2^(v-s) ≤ u:= pow_le_pow_left' (by omega) _; exact_mod_cast (ht s (Nat.le.refl) v hu).trans (Nat.mul_le_mul_right (r₁+(dσ)) he)
 have ho:o i=u*f:= by unfold o clockPlate; rw [Pi.smul_apply,nsmul_eq_mul]
 have he:f=homeTag P a i+d:=by unfold f; rw [t.reach]; simp only [Pi.add_apply,Pi.smul_apply,nsmul_eq_mul]; rfl -- try
 have h': (ruler P.par.block)*(P.reachLeaf s v (moonSpan P s):ℤ)=2*((u:ℤ)*d):=by rw [reachLeaf,Nat.cast_mul,mul_left_comm _ (↑(P.par.R.L.val ^(v-s)):ℤ) _, hx,mul_left_comm]
 have hp:= abs_le.mp (homeCost P a ha i); change r₁+_+_≤ n at hm; change _ ≤ x i ∧ x i+_ ≤ _; change o i - (r₂:ℤ) ≤ x i ∧ x i ≤ o i + (r₂:ℤ) at w
 rw [h']; let u₀:= mul_le_mul_of_nonneg_left (show (r₁:ℤ)+dσ ≤ f from by omega) (by positivity:0≤(u:ℤ)); let h₁:= mul_le_mul_of_nonneg_left (show f+((r₁:ℤ)+dσ)≤ 2*d from by omega) (by positivity:0≤(u:ℤ)); obtain ⟨t₂,t₃⟩:=w; constructor <;> linarith -- expensive
omit pL
lemma placement_m (m:P.par.R.L.val%16=1)(s v:ℕ)(p:Cover) : ∃ x, nodeC x=P.clockPlate s v p:=by
 let d:ℕ:=P.par.R.L.val^(v-s); let q:Cover:= d • p
 have ht:Odd d:= (show Odd P.par.R.L.val from ⟨P.par.R.L.val/2,by omega⟩).pow
 obtain ⟨k,h⟩:=ht; refine ⟨q+fun _=> (k:ℤ),?_⟩; have hQ(p:Cover)(i:Axis): nodeC p i=2*p i+1:=by change (2:ℕ) • p i+1=_; push_cast; rfl
 funext i; unfold clockPlate; simp only [hQ,q,Pi.add_apply,Pi.smul_apply,nsmul_eq_mul]; change (2:ℤ)*((d:ℤ)*p i+k)+1=(d:ℤ)*_; rw [h]; push_cast; ring
lemma plaza_node (h:s≤v)(p o:Cover)(q:nodeC o=P.clockPlate s v p)(i:ℕ) : upRoot P.run i h (P.rootAt s i p)=wrap (side P.run i v) o:= QuadClock.node_inj _ (by rw [node_of,P.high_root h,q])
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
