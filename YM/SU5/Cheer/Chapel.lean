import YM.SU5.Cheer.Pavilion
import YM.SU5.Cordial.Grotto
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 60000
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
open Cheer
open Cheer (Narrow)
variable (P:Spine)(x:P.Spectrum0 3)(Z:Lead.Clan)(s n:ℕ)(c r:ℕ→ℕ)
local notation "S"=> P.seasons 3 (P.otherSpectrum 3 3 x)
local notation "ψ"=> P.lucid x Z
local notation "ξ"=> P.otherSpectrum 3 3 x
local notation "H"=> P.ManyF 3 ξ
local notation "Ω"=> P.heaven 3 ξ
def allowance : ℂ:= P.singleState 3 s ξ (P.stockS Z (P.flash n))
def birthCloud : H:= ψ s n - P.allowance x Z s n • Ω
lemma halo_split : ψ s n= P.birthCloud x Z s n+P.allowance x Z s n • Ω :=(sub_add_cancel ..).symm
lemma sky_birth : P.birthCloud x Z s n=P.wealth 3 ξ (P.centered 3 ξ (flourish (P.flash n) Z) (P.flash_here n) s) := by
 let F:=P.flash n; let Λ:=P.centered 3 ξ (flourish F Z) (P.flash_here n) s
 let ι:=P.colorZero 3 ξ; let S0:=P.wealth 3 ξ
 let M:= P.allowance x Z s n; have he:P.shard x Z s n= Λ + M • ι:= (P.photon x Z s n).trans (P.coined 3 ξ (flourish F Z) (P.flash_here n) s); have ht:P.lucid x Z s n = S0 Λ + M • Ω:= (congrArg S0 he).trans ((map_add S0 Λ (M • ι)).trans (congrArg ((S0 Λ) + ·) ((map_smul S0 M ι).trans (congrArg (M • ·) (P.stone_mark 3 ξ)))))
 exact (congrArg (· - M • Ω) ht).trans (add_sub_cancel_right ..)
lemma halo_zero : inner ℂ Ω (P.birthCloud x Z s n) = 0:= by
 let Λ:= P.centered 3 ξ (flourish (P.flash n) Z) (P.flash_here n) s; exact (congrArg (inner ℂ Ω) (P.sky_birth x Z s n)).trans (P.bank_orth 3 ξ Λ (P.center_value 3 ξ (flourish (P.flash n) Z) (P.flash_here n) s))
variable (p:Space3)(t:ℝ≥0)
section
variable {j:Axis}{G:Hilbert}
private lemma allowance_sub (G':OS.Semigroup G j)(U V W:G)(p:OS.Cross j)(a:ℂ)(t:ℝ≥0)(h: W = U + a • V)(hZ: inner ℂ V U=0)(hy: ‖V‖=1)(hp:G'.U p V= V)(hu:G'.E t V=V) : inner ℂ U (G'.U p (G'.E t U))= inner ℂ W (G'.U p (G'.E t W))-(↑‖a‖:ℂ)^2:=by
 have hv:inner ℂ V (G'.U p (G'.E t U))=0:= by
   nth_rw 1 [← hp]; rw [minted,← G'.swing,hu,hZ]
 rw [h,map_add,map_add,map_smul,map_smul,hu,hp,inner_add_left,inner_add_right,inner_add_right,inner_smul_left (y:=G'.U p _), hv,inner_smul_right (x:=U),←inner_conj_symm (𝕜:=ℂ) U V,hZ,inner_self_eq_norm_sq_to_K]; simp [norm_smul,hy]
end
abbrev cutPulse (p:Space3) : Bank:= Cheer.shore p
lemma background_zeroed (a:OS.Cross (3:Axis))(t:ℝ≥0)(y:P.lodestarHere 3 ξ): let Z':=P.birthCloud x Z s n; let G:=ψ s n; inner ℂ Z' ((S).U a ((S).E t Z')) = inner ℂ G ((S).U a ((S).E t G)) - (↑‖P.allowance x Z s n‖:ℂ)^2:=by
 have he: (S).E t Ω=Ω:= by apply (heat_iff_edge (3:Axis) S _).mpr _ t; exact ((P.heavenRank 3 ξ y _).1 (Submodule.subset_span (Set.mem_singleton _))).1 -- check
 exact allowance_sub (S) (P.birthCloud x Z s n) Ω (ψ s n) a (P.allowance x Z s n) t (P.halo_split ..) (P.halo_zero ..) (P.stone_norm ..) (P.stone_warm 3 ξ y a) he
-- marsh
abbrev basisWeight : ℝ≥0:= Window.dimf Z /25
lemma paid_basis : 0 < basisWeight Z:=by
 have h:0<dimf Z:=by unfold dimf; split<;> norm_num
 unfold basisWeight; positivity
noncomputable def promenade : Narrow:= ⟨basisWeight Z • Cheer.moving ⟨2,by norm_num⟩ ⟨4,by norm_num⟩, by infer_instance⟩
noncomputable def comesFrom : Narrow:=Cheer.outlay (S) (P.birthCloud x Z s n) (P.dew s n)
lemma pays_move (z:ℂ)(h:0≤z.re): Cheer.FLap (promenade Z) p z= numberX Z/25*(Cheer.plum p (z+2)*Cheer.plum p (z+4)):=by
 let a:Pasture:=⟨2,by norm_num⟩; let b:Pasture:=⟨4,by norm_num⟩
 change (∫ y, Cheer.tendsK p z y ∂(basisWeight Z • Cheer.moving a b))= _; rw [integral_smul_nnreal_measure, Cheer.consecrated a b p z h]; simp [NNReal.smul_def,basisWeight, a, b, numberX, Complex.real_smul]
lemma pays_plum (z:ℝ): Cheer.plum p (z:ℂ) = Cordial.plume z (cutPulse p):=by
 have ht: ‖p‖^2 = ‖cutPulse p‖^2:= by
   rw [show ‖cutPulse p‖=‖position p 0‖ from rfl,Mink.squares]; simp only [spatial_position,time_position, OfNat.ofNat_ne_zero,not_false_eq_true, zero_pow,add_zero,ne_eq]
 have hv:(cutPulse p).val (2:Axis)= p 2:=by rfl -- maybe Fin cast
 unfold Cheer.plum Cheer.wind Cheer.cab Cordial.plume Cordial.pearly; rw [hv,Complex.real_smul,← ht]; push_cast; ring
lemma blinded : ovoid Z (t:ℝ) (cutPulse p) - (purePrice Z:ℂ)^2= Cheer.FLap (promenade Z) p ↑(t:ℝ):= by
 let u:=(t:ℝ); rw [pays_move Z p _ (show 0≤_ from t.property)]; change ovoid Z u _ - _= _
 unfold ovoid; simp_rw [show ↑(t:ℝ)+(2:ℂ)= ↑(u+2) by push_cast; rfl, show ↑(t:ℝ)+(4:ℂ)= ↑(u+4) by push_cast; rfl, pays_plum]
 rw [show (purePrice Z:ℂ)=numberX Z * _ / 5 from price_as Z]; ring
lemma promenade_strict : ∀ᵐ z∂(promenade Z: Measure E4), z∈ Mink.inside:=by change ∀ᵐ z∂(basisWeight Z • Cheer.moving _ _), z∈ Mink.inside; exact Measure.ae_smul_measure (Cheer.strictly _ _) _ -- tune
lemma importance {a:Set E4}(h:IsOpen a)(t:(Mink.inside ∩ a).Nonempty): 0 < (promenade Z:Measure E4) a:=by
 let b:= (basisWeight Z:ℝ≥0∞); change 0<b * (Cheer.moving _ _) a; exact ENNReal.mul_pos (ENNReal.coe_ne_zero.mpr (paid_basis Z).ne') (Cheer.all_inside _ _ h t).ne'
lemma promenade_ne : (promenade Z:Measure E4)≠0:=by
 have h:= importance Z isOpen_univ ⟨position 0 1,by simp [Mink.inside],Set.mem_univ _⟩; exact Measure.measure_univ_pos.mp h -- find
lemma home_bright : Cheer.Brilliant (promenade Z):= Eventually.mono (promenade_strict Z) (fun _ h=> ((Mink.strict_self _).1 h).1.le)
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
#print axioms halo_zero
#print axioms blinded
#print axioms background_zeroed
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
