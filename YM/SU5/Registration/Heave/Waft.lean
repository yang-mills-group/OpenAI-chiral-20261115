import YM.SU5.Registration.Heave.Corona
set_option autoImplicit false
set_option maxHeartbeats 380000
noncomputable section
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection

open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
     MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
     Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
     ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
     Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn

open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel

open SatinNucleus Six

/-!
# Using the march to pay wafer errors

Seam coordinates in this actual recipe are not strictly wide enough a priori to
spend the Meringue comparison (`LaceLayer`, `StillFront`). So require an extension
of `HandleWith` in the purchase. Nothing changes in **parameterized** parts,
or in buying the stock estimates, even n-facing comparison. But controlling the
ratio of the two widths BEFORE the seam error calculation makes it possible to
spend `StillFront` at this varying positive time, after choosing the n. It's not an assertion
on all possible Snap sequences. The criterion to consume once the n is chosen
is placed on the actual pointPad widths of the actors as usual.
-/
namespace Spine
open SatinJets
variable (P:Spine)(x:P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "H"=>P.ColorHil 3 ξ
local notation "F"=>P.physicalEnergy 3 ξ
variable (c r:ℕ→ℕ)(Y:ℕ→ P.Apron) (n:ℕ→ℕ)
local notation "M" s:max d:max=> whenly (timeMesh P.par) s d

abbrev bid_panel (i:ℕ)(k:Lead.Clan)(s m:ℕ): ℝ:= (let V:= (Y i).allowance P 3; ((1:ℝ)+‖(Y i).engine P 3 (P.advocate 3 x 3)‖)*‖P.printGaps 3 (P.advocate 3 x 3) k s m V V‖)
structure Guest :Prop where
 covers (i:ℕ)(k:Lead.Clan): (P.thinMat k (c (n i)) (r (n i))).allowance P 3 ≤ (Y i).allowance P 3
 expenses (i:ℕ)(k:Lead.Clan): P.bid_panel x Y i k (c (n i)) (r (n i)) ≤ P.macroStep i
variable {K:P.Register}{J:P.Ellis 3 x}(T:P.Experiment K c r x J)
private lemma handle_fresh (W:ℕ→ℕ→Prop) (p:∀ i,∀ᶠ j:ℕ in atTop,W i j):∃ n:ℕ→ℕ,StrictMono n ∧ ∀ i,W i (n i):=by
 -- copy `SatinThinFusionSales` choose_handle
 choose h u using fun i=> eventually_atTop.1 (p i)
 let g:ℕ→ℕ := Nat.rec (h 0) (fun i v=>max (h (i+1)) (v+1))
 exact ⟨g,strictMono_nat_of_lt_succ fun i=> (Nat.lt_succ_self _).trans_le (le_max_right (h (i+1)) (g i+1)),fun i=> u i (g i) (by cases i; exact le_refl _; exact le_max_left ..)⟩
include T
lemma seam_grant (h:P.Wafting c r) : ∃ n:ℕ→ℕ, P.HandleWith x c r Y n ∧ P.Guest x c r Y n:= by
 -- Reuse old seam bound on vacuum, now get operator estimates from StillFront.
 let w(i:ℕ):= (Y i).realWidth P 3
 let f(i:ℕ):= (Y i).engine P 3 (P.advocate 3 x 3)
 let A (i j:ℕ)(k:Lead.Clan): H:= f i ((F).E ((w i).toNNReal) (P.shard x k (c j) (r j)))
 let T' (i:ℕ)(k:Lead.Clan): H:= (purePrice k:ℂ) • f i (P.colorZero 3 ξ)
 let W(i j:ℕ):= ∀ k:Lead.Clan,‖A i j k-T' i k‖ ≤ P.macroStep i
 have hp(i:ℕ):∀ᶠ j:ℕ in atTop, W i j:= by
    apply eventually_all.mpr; intro k
    let v:=(w i).toNNReal; have hv:0<v:= Real.toNNReal_pos.mpr ((Y i).real_width_pos P 3)
    have he: Tendsto (fun j:ℕ=> A i j k) atTop (𝓝 (T' i k)):=by
       have he:Tendsto (fun j=> A i j k) atTop (𝓝 ((f i) ((purePrice k:ℂ) • P.colorZero 3 ξ))):=((f i).continuous.tendsto _).comp (thin_front_shard_tendsto k T (fun _=>v) (thin_compare_dew T hv _ (Eventually.of_forall fun _=>le_refl v)))
       rw [map_smul] at he; exact he
    exact ((tendsto_iff_norm_sub_tendsto_zero.1 he).eventually (ge_mem_nhds (P.macroStep_pos i)))
 let y(i):=(Y i).allowance P 3
 let V(i:ℕ):ℝ:= P.macroStep i/(1+‖f i‖)
 obtain ⟨n,q,g⟩:= handle_fresh _ (fun i => (T.launch.smaller.tendsto_atTop.eventually (eventually_ge_atTop (Y i).s)).and ((T.launch.eager.tendsto_atTop.eventually (eventually_gt_atTop P.calibration.ℓ)).and ((hp i).and (h _ (show 0<V i from div_pos (P.macroStep_pos i) (by positivity)) _ ((Y i).width_p P 3)))))
 refine ⟨n,⟨q,fun i=>(g i).1,fun i=>(g i).2.1,fun i k=> (g i).2.2.1 k⟩,⟨fun i k=>( (g i).2.2.2 3 k).1.le,fun i k=>?_⟩⟩
 have ht:= ((g i).2.2.2 3 k).2 _ _ le_rfl le_rfl ξ
 change ‖P.printGaps 3 ξ k (c (n i)) (r (n i)) (y i) (y i)‖≤ P.macroStep i/(1+‖f i‖) at ht
 change (1+‖f i‖)*_≤ _
 rw [mul_comm]; exact (le_div_iff₀ (show 0<1+‖f i‖ from by positivity)).mp ht
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.Guest
#print axioms Spine.seam_grant
