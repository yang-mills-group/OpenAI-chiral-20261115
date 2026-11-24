import SatinFixedContrastNovember4

import SatinThinCentury

/-! # CP12 Canvas: assembly of the regulator. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six OS.Semigroup.Balloon


variable (P:Spine) (j:Axis)(x:P.Spectrum0 3)
local notation "W"=>P.calibration
local notation "T"=>P.run
local notation "G"=>P.large
local notation "L"=>P.par.R.L.val
local notation "Λ" => P.par
local notation "ℓ"=> (W).ℓ
local notation "b₀"=>ruler P.par.block
local notation "Υ"=> timeMesh P.par
lemma reframe {S:Finset Cover}{u t:ℤ}(e:Between W j u t S)(h:ℕ): Between W j ((L:ℤ)^h*u) ((L:ℤ)^h*t) (volumeAround Λ P.width h S):=by
 intro w z
 obtain ⟨v,mY,p⟩:=Tower.shield Λ P.width S h z
 obtain ⟨f,y⟩:= e v mY; have wU:=p j; change |(w-(L)^h • v) j|+ ((ℓ):ℕ) ≤ (L)^h * (((ℓ):ℕ):ℤ) at wU
 let c:ℤ:=(P.par.R.L.val:ℤ)^h; have hC:0≤ c:=by unfold c; positivity
 have hv:= abs_le.mp (show |(w-(L)^h • v) j| ≤ c*(((ℓ):ℕ):ℤ)-(((ℓ):ℕ):ℤ) from by unfold c; linarith only [wU])
 simp only [Pi.sub_apply,nsmul_eq_mul,Nat.cast_pow,Pi.mul_apply,Pi.natCast_apply,Pi.pow_apply] at hv
 change (c*u+ (↑(ℓ):ℤ) ≤ w j) ∧ w j+(((ℓ):ℕ):ℤ)≤c*t
 constructor <;> (unfold c at *; nlinarith only [hv.1,hv.2,mul_le_mul_of_nonneg_left f hC,mul_le_mul_of_nonneg_left y hC])
open MacroGrid
variable {ι : Type} (A:ι→ P.Apron) (I:Finset ι)(h:Axis→ℕ)(s:ℕ)
variable (u:∀ j,0< h j) (t:∀ i∈I,(A i).s ≤ s) (f:∀ i∈ I,∀ j,(A i).zoom P s j ≤ h j)
lemma apron_sweep : (∀ i∈ I,∀ k,(A i).zoom P s k≤h k) → Between W j (-b₀*h j) (b₀ * h j) (I.biUnion (fun i=>volumeAround Λ P.width (s-(A i).s) (A i).S)):=by
 intro e q v; obtain ⟨i,b,z⟩:= mem_biUnion.mp v
 let H:=A i; let w:= (L)^(s-H.s); let Tx:=H.zoom P s j; let B:=h j
 obtain ⟨x,y⟩:= P.reframe j ((A i).shelter j) (s-(A i).s) _ z
 have he:(Tx:ℤ) ≤ (B:ℤ):=by exact_mod_cast e i b j
 have hp:b₀* (Tx:ℤ)=(↑(L):ℤ)^(s-(A i).s)*(b₀*(A i).u j):=by unfold Tx H Apron.zoom; rw [Nat.cast_mul,Nat.cast_pow,mul_left_comm]
 have hr:0 ≤ (b₀):=by unfold ruler; positivity
 rw [neg_mul, _root_.mul_neg,←hp] at x; rw [←hp] at y; rw [neg_mul]; constructor <;> linarith only [x,y,mul_le_mul_of_nonneg_left he hr]
variable (z:ι → ℂ)
noncomputable def canvas (u:∀ j,0< h j) (_t:∀ i∈ I,(A i).s ≤ s)(f:∀ i∈ I,∀ j,(A i).zoom P s j ≤ h j) (z:ι → ℂ): P.Apron where
 s:=s
 u:=h
 pos:=u
 S:= I.biUnion (fun i=>volumeAround Λ P.width (s-(A i).s) (A i).S)
 F:= ∑ i∈ I,z i • (A i).full P s
 bay:=by
     apply Subalgebra.sum_mem _; intro i y; apply Subalgebra.smul_mem _ _ _; have he:= (Tower.proceeds T G P.history.circuit (A i).s (s-(A i).s) ((Tapestry.locates ..).1 (A i).bay)).1
     exact he.mono (subset_biUnion_of_mem (fun i=>volumeAround Λ P.width (s-(A i).s) (A i).S) y)
 realM:= Subalgebra.sum_mem _ fun i e=> Subalgebra.smul_mem _ ((A i).fullColor P s) _
 shelter j:= P.apron_sweep j A I h s f
lemma reflectorSum(l:List Axis)(R:ι→ℝ):
    ((P.canvas A I h s u t f (fun i=>(R i:ℂ))).pivot P l).F=∑ i∈ I,(R i:ℂ) • ((A i).pivot P l).full P s:=by
 induction l with
 | nil=>rfl
 | cons j l g=>
    simp_rw [Apron.pivot_cons, Apron.full_exchange]; change P.reflectTest j _ = _; rw [g,map_sum]; exact sum_congr rfl fun i _=> Eq.trans (P.scale_mirror ..) (by rw [Complex.star_def, Complex.conj_ofReal])
local notation "ξ"=>P.advocate 3 x j
local notation "E"=> (P.physicalEnergy j ξ).E
lemma zoom_check (x':ℕ) (A':P.Apron)(v:A'.s ≤ s): A'.zoom P s j ≤ x' ↔ A'.realWidth P j ≤ bell Υ s x':=by
 rw [←A'.zoom_bell P j s v]; rw [← Int.ofNat_le, ← bell_le Υ s] -- lemma maybe `[Nat.cast_ofNat]`
include t in
lemma canvas_exact (B:P.Apron)(z:ι→ℂ)(p:B.F= ∑ i∈ I,z i • (A i).full P s)(v:B.s=s)(f:∀ i∈ I,(A i).realWidth P j ≤ B.realWidth P j)(r:ℝ)(h:B.realWidth P j ≤ r): P.beamRaw j x B r=∑ i∈ I,z i • P.beamRaw j x (A i) r:=by
 let q:=B.realWidth P j; let z₀:Cover:= fun _=>(B.u j:ℤ); let C:= P.truck j ξ (P.vtile s z₀); have hp:P.meshPose s z₀ j=q:=by
    unfold q Apron.realWidth; rw [v]; rfl
 let X:= P.beamRaw j x B q; let Y(i:ι):= P.beamRaw j x (A i) q; have Z: P.issuing s B z₀=∑ i∈ I,z i • P.issuing s (A i) z₀:=by
    have hg:= P.issuing_here B z₀; rw [v,p,map_sum] at hg; rw [hg]; exact sum_congr rfl fun i _=> map_smul ..
 have hx(i:ι)(e:i∈ I): ∃ h:P.birthF j s (z i • P.issuing s (A i) z₀), P.viewF j ξ s h=z i • C (Y i):=by obtain ⟨d,w⟩:=P.beam_grid_pose_view j x _ s z₀ ((f i e).trans hp.ge) (t i e); unfold beamGridRay at w; rw [hp] at w; exact ⟨P.birthScaleJ j s (z i) d,(P.viewJ_scale j ξ s (z i) d).trans (congrArg (z i • ·) w)⟩
 classical
 obtain ⟨a₁,t₁⟩ := P.birthSumJ j ξ s _ _ _ hx; obtain ⟨a₀,t₀⟩:= P.beam_grid_pose_view j x B s z₀ hp.ge v.le; unfold beamGridRay at t₀; rw [hp] at t₀
 let R:= (∑ i∈ I,z i • Y i); have he:C X=C R:=by
    unfold R; rw [map_sum]; simp_rw [map_smul]; exact (t₀.symm.trans (P.identical_F j ξ s a₀ a₁ Z)).trans t₁
 have hv: X=R:=sub_eq_zero.mp (norm_eq_zero.mp (Eq.trans (P.truck_norm j ξ (P.vtile s z₀) (X-R)).symm (show ‖C (X-R)‖=0 by rw [map_sub,he,sub_self,norm_zero])))
 rw [P.raw_twice j x B (show B.realWidth P j≤q from le_refl _) h]; change E _ X=_; rw [hv]; unfold R; rw [map_sum]; simp_rw [map_smul]; exact sum_congr rfl fun i e=> congrArg (z i • ·) (P.raw_twice j x (A i) (f i e) h).symm

lemma pivot_exact (R:ι→ℝ)(l:List Axis)(r:ℝ)(d:bell Υ s (h j) ≤ r):
    P.beamRaw j x ((P.canvas A I h s u t f (fun i=>(R i:ℂ))).pivot P l) r=∑ i∈ I,(R i:ℂ) • P.beamRaw j x ((A i).pivot P l) r:=by
 let B:=P.canvas A I h s u t f (fun i=>(R i:ℂ)); let i'(i:ι):=(A i).pivot P l; have he: (B.pivot P l).realWidth P j=bell Υ s (h j):= B.pivot_w j P l -- order
 refine P.canvas_exact j x i' I s (fun i v=> by rw [show (i' i).s=(A i).s from (A i).pivot_s P l]; exact t i v) _ _ (P.reflectorSum A I h s u t f ..) (B.pivot_s P l) (fun i v=>?_) _ (le_trans (le_of_eq he) d)
 unfold i'; change _≤(B.pivot P l).realWidth P j; rw [Apron.pivot_w, he]; exact (P.zoom_check j s (h j) (A i) (t i v)).mp (f i v j)

lemma canvas_gain (ξ':P.Spectrum0 j) : P.singleState j s ξ' (P.canvas A I h s u t f z).F=∑ i∈ I,z i * P.singleState j (A i).s ξ' (A i).F:=by
 change P.singleState j s ξ' (∑ i∈I, z i • (A i).full P s)=_; rw [map_sum]; simp_rw [map_smul,smul_eq_mul]; refine sum_congr rfl fun i e=>?_ ; exact congrArg (z i * ·) (P.hereAndThere j ξ' (A i).s s (t i e) (A i).F)
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.pivot_exact
