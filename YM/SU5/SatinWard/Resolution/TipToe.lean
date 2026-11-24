import YM.SU5.SatinWard.Resolution.Pagoda
import YM.SU5.SatinWard.Resolution.BraidX
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 700000
set_option maxRecDepth 3200
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
variable {P:Spine}{K:P.Register}{b C:ℝ}{t σ}{W:ℕ→ HorizonLens→ HorizonLens→ℝ}{β:ℕ→ℝ}
variable (T: CouncilGrant P K b C t σ W β)(H:PublicKernel P σ W)(F D: PlaqAxes)
open BProof Pressure
open _root_.YM.Gleam.Luster.Almanac Grade
open Papal.SkyTax
namespace Regulator
local notation "Ω" s:max=> hat P.par.R.L P.par.x s
open CasaF.Signboard CF.Tap SignSlot ShapeLab Emu
open LampD Quire LitCurrent AuroraX
namespace LampRead
attribute [local irreducible] bandWidthD
-- rough prices first.
open Next.Rank Next.Rank.Spindle _root_.YM.Regis.Circuit.SpringDay.Spring
variable (i:juniorKid)(j:seniorKid)
local notation "Uh"=> tradeW ((i.1):SpinIdx) ((j.1):SpinIdx)
local notation "ph"=>CF.Papyrus.Franc.SatinForce.Flash ((i.1):SpinIdx) ((j.1):SpinIdx)
include H
lemma ensembleOne : ∃ C:ℝ,0≤C ∧ ∀ x:Cover,‖costSong x i j‖≤C:=by
 obtain ⟨G,hg,t⟩:= sharpSpin H i.1 j.1 3 0 (by norm_num); let Xf(x:Cover):=‖Uh x‖; let A:= ∑ x∈ Lattice.box 2,Xf x; refine ⟨A+2*G,add_nonneg (sum_nonneg (fun i _=>norm_nonneg _)) (by positivity),fun x=>?_⟩; suffices hp:Xf x≤ A+2*G by unfold costSong; split; exact hp; rw [norm_zero]; exact (show 0≤Xf x from norm_nonneg _).trans hp
 by_cases u:‖scape x‖ ≤2
 · refine le_trans (b:=A) (single_le_sum (fun i (_:i ∈ Lattice.box 2)=>norm_nonneg _) ?_) (le_add_of_nonneg_right (by positivity)) -- term inference.H. maybe binder Xf x=_.
   have h(f:Axis): |(((x f:ℤ):ℝ))| ≤ 2:= (show _ ≤ ‖shaftX x‖ from norm_le_pi_norm (shaftX x) f).trans ((Stationary.orbit_at ..).trans u); have hv(f:Axis): |x f| ≤ (2:ℕ):=by exact_mod_cast h f
   apply box_test.mpr; exact ⟨fun i=> (abs_le.mp (hv i)).1, fun i=>(abs_le.mp (hv i)).2⟩
 let R:= ‖scape x‖/2; let F:= patchF x R; have hr:1≤R:= by unfold R; linarith only [u]; -- indentation issue
 have hZ:‖F‖=2:=by unfold F patchF; rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity),show ‖scape x‖=R*2 from (by unfold R; ring), ←mul_assoc,inv_mul_cancel₀ ((zero_lt_one.trans_le hr).ne'),one_mul]
 obtain ⟨hq,Q⟩:= t R hr (zero_le_one.trans hr) x F hZ.ge (by linarith only [hZ]) (by rw [sub_self,norm_zero,zero_div]); let L:= (R:ℂ)^3*Uh x; have he : Xf x ≤ ‖L‖:=by unfold L; rw [norm_mul, norm_pow, Complex.norm_real,Real.norm_of_nonneg (zero_le_one.trans hr)]; exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ hr)
 refine he.trans ((norm_le_norm_sub_add L (ph F)).trans (le_trans (add_le_add Q hq) ?_)); have h0: 0≤A:= sum_nonneg fun i _=>norm_nonneg _; linarith only [div_le_self (zero_le_one.trans hg) hr,h0]
omit H
-- recognition.Rsp; precision prices at any supplied κR>=Ctor .2.B Basis length.T.We bound all offsets jointly (same constants)
structure SightEra (R Q:ℝ)(k:ℕ)(x y:Cover)(d:Gaia):Prop where
 limit : 8 ≤ Q
 eligible : (k+1:ℝ)*Q ≤ R
 lens : patchF (x-y) R=d
 lower :3 ≤ ‖d‖
 upper :‖d‖≤48
variable {R Q:ℝ}{k:ℕ}{x y: Cover}{d:Gaia} (S':SightEra R Q k x y d)
include S'
lemma rhone : 1 ≤ R ∧ Q ≤ R:=by have he:= S'.eligible; have hh:= S'.limit; constructor<;> nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) k) (by linarith:0≤Q)]
lemma tokenBudget (z:landSheet k): ‖patchF (x+z.val-y) R-d‖ ≤ 4/Q:=by
 let a:=z.val; let t:= disM k; let g:=patchF (x-y) R; have ht:¬ k=(k+1:ℕ):=by omega
 rw [show patchF (x+z.val-y) R= g+R⁻¹ • scape a from ?_,show g=d from S'.lens,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (zero_le_one.trans (rhone S').1))]; swap; · unfold g patchF a; rw [← smul_add,←scape_add,show x-y+z.val=x+z.val-y from by abel]
 have he:‖shaftX a‖ ≤ 2*k:=by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 (fun i=>?_); change |(↑(a i):ℝ)| ≤ _; obtain ⟨p,q⟩:=box_test.mp z.property; push_cast at p q; exact_mod_cast (show |a i|≤ 2*(k:ℤ) from abs_le.mpr ⟨by specialize p i; omega,q i⟩)
 have hz:= Onyx.moor_z (shaftX a); change ‖scape a‖≤ _ at hz; have hp: ‖scape a‖≤ 4*(k:ℝ):=by linarith only [he,hz]
 have q':=rhone S'; have hr:0≤Q:=by linarith only [S'.limit]
 rw [mul_comm,← div_eq_mul_inv, div_le_div_iff₀ (by linarith only [q'.1]) (by linarith only [S'.limit])]; nlinarith only [mul_le_mul_of_nonneg_right hp hr,S'.eligible,hr]
omit S' in
lemma scape_neg (v:Cover) : scape (-v) = -scape v:=by ext i; change (↑(-v i):ℝ) = -(↑(v i):ℝ); push_cast; rfl
lemma flipOrder : SightEra R Q k y x (-d):=⟨S'.limit,S'.eligible,by rw [← S'.lens,show y-x= -(x-y) from (by abel)]; unfold patchF; rw [scape_neg, smul_neg],by rw [norm_neg]; exact S'.lower,by rw [norm_neg]; exact S'.upper⟩
private lemma back_charge (z:landSheet k) : ‖patchF (y-(x+z.val)) R- -d‖ ≤4/Q:=by
 rw [show y-(x+z.val)=-(x+z.val-y) from by abel, patchF, scape_neg, smul_neg, neg_sub_neg, norm_sub_rev]; exact tokenBudget S' z
omit S'
include H
private lemma glideSpin : ∃ A:ℝ,0 ≤ A ∧ ∀ (R Q:ℝ)(x:Cover)(d:Gaia),1 ≤ R→8 ≤ Q→ Q ≤ R→ 3 ≤ ‖d‖ → ‖d‖ ≤48→ ‖patchF x R-d‖ ≤ 4/Q → Disp Q A ((R:ℂ)^3 *costSong x i j) (fieldKid d i j):=by
 obtain ⟨A,f,g⟩:= sharpSpin H i.1 j.1 50 0 (by norm_num); obtain ⟨B,t,h,u⟩:=cradle (Q:=50) i.1 j.1; let Z:= A+4*B; have hp:1 ≤ Z:=by unfold Z; linarith
 refine ⟨Z,zero_le_one.trans hp,fun R Q x d w w1 w2 w3 w4 y=>?_⟩
 have hB:0<Q:=by linarith only [w1]
 unfold costSong fieldKid; split_ifs; swap; · rw [mul_zero]; exact (Disp.zero Q).mono (zero_le_one.trans hp) hB.le
 let F:=patchF x R; let G:=(R:ℂ)^3 * Uh x; have hx:4/Q ≤ 1:= (div_le_one hB).2 (by linarith); have ht:2≤ ‖F‖ ∧ ‖F‖ ≤ 49:= by have he:=abs_le.mp ((abs_norm_sub_norm_le F d).trans (y.trans hx)); constructor<;>linarith only [he.1,he.2,w3,w4]
 obtain ⟨hz,e⟩:= g R w (zero_le_one.trans w) x F ht.1 (ht.2.trans (by norm_num)) (by rw [sub_self,norm_zero,zero_div]); have hv:F∈ plinth 50:=(peak_iff ..).2 (by constructor<;>linarith only [ht.1,ht.2]); have hw: d ∈ plinth 50:=(peak_iff ..).2 (by constructor<;>linarith only [w3,w4])
 have hd:‖ph F-ph d‖≤ 4*B/Q := (u _ hv _ hw).trans ((mul_le_mul_of_nonneg_left y (zero_le_one.trans t)).trans_eq (by ring)); change Disp _ _ G (ph d); exact ⟨(zero_le_one.trans hp), (h _ hw).trans (by unfold Z; linarith), (norm_sub_le_norm_sub_add_norm_sub G (ph F) (ph d)).trans ((add_le_add (e.trans (div_le_div_of_nonneg_left (zero_le_one.trans f) hB w2)) hd).trans_eq (add_div A (4*B) Q).symm)⟩
lemma packed_cross : ∃ B:ℝ,0≤ B∧∀ (i j:principalKid){R Q:ℝ}{k:ℕ}{x y: Cover}{d:Gaia} (Z:SightEra R Q k x y d)(u v:landSheet k),
      Disp Q B ((R:ℂ)^6*(costSong (y-(x+u.val)) j.2 i.1*(-costSong (x+v.val-y) i.2 j.1))) (kindDU d i j):=by
 choose a w h using (fun i:juniorKid×seniorKid=> glideSpin H i.1 i.2); let A:=∑ i:juniorKid×seniorKid, a i; have e:0≤ A:= sum_nonneg fun i _=>w i; have hx(i:juniorKid×seniorKid):a i≤ A:=single_le_sum (fun i _=>w i) (mem_univ i); refine ⟨3*A*A,by positivity,?_⟩; intro i j R Q k x y d p u v
 let τ₁:=(j.2,i.1); let τ₂:=(i.2,j.1); let yA:=rhone p; have u0:1 ≤ Q:=by linarith only [p.limit]
 let V:= (((h τ₁ _ _ _ _ yA.1 p.limit yA.2 (flipOrder p).lower (flipOrder p).upper (back_charge p u)).mono (hx _) (zero_le_one.trans u0)).times ((h τ₂ _ _ _ _ yA.1 p.limit yA.2 p.lower p.upper (tokenBudget p v)).mono (hx _) (zero_le_one.trans u0)) u0).increase (-1); rw [norm_neg,norm_one,one_mul] at V; let A₁:=fieldKid d j.2 i.1; rw [show fieldKid (-d) τ₁.1 τ₁.2= -A₁ from mirrorX _ _ (norm_pos_iff.mp (by linarith only [p.lower])),neg_one_mul,neg_one_mul,neg_mul,neg_neg] at V; refine Eq.subst (motive:=fun x'=>Disp Q (3*A*A) x' (kindDU d i j)) ?_ V; unfold τ₁ τ₂; dsimp only; ring
#print axioms packed_cross
end LampRead
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
