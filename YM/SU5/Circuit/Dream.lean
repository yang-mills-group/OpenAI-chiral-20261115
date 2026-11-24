import YM.SU5.Circuit.Honey
set_option autoImplicit false
set_option maxHeartbeats 480000
set_option synthInstance.maxSize 28000
set_option linter.unusedSectionVars false
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
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Prototype
open Spine Lamour Bridge.Celeste Glimpse Morn Spine.RadiusF Ballad
open CF.Velvet CF.Pannier.Chancel Altitude
/-- Nonzero UV gauge-only detector. -/
abbrev goldF:PlaqAxes:= ⟨(0,1),by decide⟩
def bluePin(i:ℕ): Cover:= (i+1) • Lattice.step 3
def tinyBill (i:ℕ):ℝ:= i+1
def clearBill(i:ℕ):ℝ:= tinyBill i^9
lemma tinyB_pos (i:ℕ):0<tinyBill i:=by unfold tinyBill; positivity
lemma clearB_pos (i:ℕ):0<clearBill i:= pow_pos (tinyB_pos _) _
local notation "X"=> YM.basis 3
lemma royal_spectrum:0 < ‖spectrumColor goldF goldF SU.group X‖:=by
 let G:= SU.group; haveI: Nontrivial G.Color:= Thera.yet_one.nontrivial_color
 have hf:0<G.lieDim:= by rw [Gauge.lieDim, ← G.colorIso.finrank_eq]; exact Module.finrank_pos
 apply norm_pos_iff.mpr
 have hx:X ≠0:=norm_pos_iff.mp (by rw [basis_norm]; exact one_pos)
 have he : Maxwell.bareCurl 0 1 0 1 X=4*Maxwell.normal := by
    rw [Maxwell.bareCurl,Pi.sub_apply,Maxwell.Bare.opp_grad hx,Maxwell.Bare.opp_grad hx]; simp only [↓reduceIte,Maxwell.second_Green hx]; norm_num [show (0:Axis)≠3 from by decide,show (1:Axis)≠3 from by decide]; ring
 have hh:(Fintype.card G.ColorIndex:ℂ)≠0:=by change (Fintype.card (Fin G.lieDim):ℂ) ≠0; rw [Fintype.card_fin]; exact_mod_cast hf.ne'
 have hv: ((4*Maxwell.normal:ℝ):ℂ) ≠ 0:= by exact_mod_cast (mul_pos (by norm_num : (0:ℝ)<4) Maxwell.normal_pos).ne'
 change 2*(Fintype.card G.ColorIndex:ℂ)*((Maxwell.bareCurl 0 1 0 1 X:ℝ):ℂ)^2≠ 0; rw [he]; exact mul_ne_zero (mul_ne_zero (by norm_num) hh) (pow_ne_zero _ hv)
lemma beam_dates (i:ℕ): Disjoint (platePin goldF (bluePin i)) (platePin goldF 0):=by
 have he (x y:Cover)(h:x∈platePin goldF y):x 3 = y 3:=by
    simp [platePin,Lattice.square, Lattice.visits] at h; rcases h with h|h|h|h|h<;> rw [h]<;> first| rfl| norm_num [goldF,show (3:Axis)≠0 from by decide,show (3:Axis)≠1 from by decide]
 apply Finset.disjoint_left.mpr; intro k x y; have h:= he k (bluePin i) x; have ht:= he k 0 y; rw [ht] at h; simp [bluePin] at h; omega
-- on unselected & physical all axes. Exact registration & same cutoffs.
lemma shining (L M D:ℝ)(Y:Supplier)(hx:0<M)(u:0<D) (z:ℕ→ℕ): ∃ (P:Spine)(K:P.Register), uniform P K Y L M ∧ ∃ (r:ℕ→ℕ), z≤r ∧
 ∃ (c:ℕ→ℕ), Launch P c r ∧ P.Captive goldF goldF bluePin 0 clearB_pos c tinyBill X (fun i f=>P.E (c i) f.val) ∧ roughUV P c r keyV ∧ ∃ (α t₁:ℝ),0<α∧ 0<t₁∧t₁<D ∧ ∃ R: Glimpse.Voyage P.par.block P.calibration.ℓ 4 α (RadiusF.next P.calibration.ℓ),
     ∀ᶠ i:ℕ in atTop, ∃ x:P.Spectrum0 3, P.party 3 K x ∧ (∀ j:Axis,P.Captive goldF goldF bluePin 0 clearB_pos c tinyBill X (fun i f=>P.singleState j (c i) (P.otherSpectrum 3 j x) f)) ∧ readyUV P c r x keyV ∧ P.funds i (P.otherSpectrum 3 3 x) R t₁ ∧
       ∀ z:SU.Slot, P.Intact K i R.toGaze x z t₁∧ P.Royal i ((P.otherSpectrum 3 3) x) R (family z) t₁ ∧ P.Passage x c r K z ∧ P.Bands x (family z) c r:=by
 have h:Tendsto tinyBill atTop atTop:=tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x:=(1:ℝ)))
 refine satin_gauge goldF goldF bluePin 0 tinyB_pos h ?_ (norm_pos_iff.mp (basis_norm (3:Axis) ▸ one_pos)) clearB_pos ?_ L M D Y hx u z
 · refine tendsto_const_nhds.congr fun k=>?_; rw [Pi.zero_apply,sub_zero]; ext i; rw [basis_eq]; change _=((bluePin k i:ℤ):ℝ)/_; by_cases p:i= (3:Axis)<;>simp [bluePin,tinyBill,p]; field_simp
 apply (tendsto_inv_atTop_zero.comp h).congr; intro i; have he:= tinyB_pos i; change _⁻¹=_^8/_^9; field_simp
end Prototype
#check @Prototype.shining
#print axioms Prototype.shining
#check @Prototype.royal_spectrum
#print axioms Prototype.royal_spectrum
#check @Prototype.beam_dates
#print axioms Prototype.beam_dates
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
