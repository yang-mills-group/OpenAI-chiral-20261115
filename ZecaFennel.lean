import SatinThinFusionSales
import ZecaLatticeFieldEstimates
import ZecaCrust
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 350000
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
open MacroGrid SatinNucleus SatinJets
variable (P:Spine)(Z:Lead.Clan)(x:P.Spectrum0 3)
local notation "K" => P.calibration
local notation "T" => timeMesh P.par
local notation "ξ"=> P.advocate 3 x 3
local notation "S"=> P.physicalEnergy 3 ξ
local notation "Ξ"=> P.wealth 3 ξ
local notation "R"=> P.seasons 3 ξ
local notation "ζ" i:max=> (purePrice i:ℂ)
local notation "H"=> P.ColorHil 3 ξ
local notation "G"=> P.ManyF 3 ξ
local notation "ω"=> P.colorZero 3 ξ
local notation "E"=> (S).E
local notation "L"=> Lead.Clan
local notation "V!"=> (∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))
variable (c r:ℕ→ℕ)(Y:ℕ→ P.Apron) (n:ℕ→ℕ)
local notation "Q" k:max j:max=> P.stitchApron k (Y j) (c (n j)) (r (n j))
local notation "w" i:max=> (Y i).realWidth P 3
local notation "e" i:max=> (Y i).engine P 3 ξ

/-- pay operator error in addition to ket error. -/
def Sown : Prop:= ∀ i,∀ k:Lead.Clan, ∀ a b:ℝ,
 (Q k i).realWidth P 3 ≤ a → (Q k i).realWidth P 3 ≤ b →
 ‖P.ruby 3 ξ (Q k i) 0 a b -
   ζ k • P.ruby 3 ξ (Y i) 0 (a+w i) (b-w i)‖ ≤ P.macroStep i

private lemma chooseH {W:ℕ→ℕ→Prop} (p:∀ i,∀ᶠ j:ℕ in atTop,W i j):∃ n:ℕ→ℕ,StrictMono n ∧ ∀ i,W i (n i):=by
 choose h u using fun i=> eventually_atTop.1 (p i)
 let g:ℕ→ℕ := Nat.rec (h 0) (fun i v=>max (h (i+1)) (v+1))
 exact ⟨g,strictMono_nat_of_lt_succ fun i=> (Nat.lt_succ_self _).trans_le (le_max_right (h (i+1)) (g i+1)),fun i=> u i (g i) (by cases i; exact le_refl _; exact le_max_left ..)⟩
variable {K':P.Register}{J:P.Ellis 3 x}(B:P.Experiment K' c r x J)
variable (N:P.Snowy c r)
include N B
lemma pollen_sale :∃ n:ℕ→ℕ, P.HandleWith x c r Y n ∧ P.Sown x c r Y n:= by
 let A (i j:ℕ)(k:L): H:= (e i) (E ((w i).toNNReal) (P.shard x k (c j) (r j)))
 let T' (i:ℕ)(k:L): H:= ζ k • (e i) ω
 let W(i j:ℕ):= ∀ k:L,‖A i j k-T' i k‖ ≤ P.macroStep i
 have hp(i:ℕ):∀ᶠ j:ℕ in atTop, W i j:= by
    apply eventually_all.mpr; intro k
    let v:=(w i).toNNReal; have hv:0<v:= Real.toNNReal_pos.mpr ((Y i).real_width_pos P 3)
    have he: Tendsto (fun j:ℕ=> A i j k) atTop (𝓝 (T' i k)):=by
       have he:Tendsto (fun j=> A i j k) atTop (𝓝 ((e i) (ζ k • ω))):=((e i).continuous.tendsto _).comp (thin_front_shard_tendsto k B (fun _=>v) (thin_compare_dew B hv _ (Eventually.of_forall fun _=>le_refl v)))
       rw [map_smul] at he; exact he
    exact ((tendsto_iff_norm_sub_tendsto_zero.1 he).eventually (ge_mem_nhds (P.macroStep_pos i)))
 have ht(i:ℕ):Tendsto (fun j=> ‖e i‖ * keyV j) atTop (𝓝 0):=by simpa using (keyV_go.const_mul ‖e i‖)
 obtain ⟨n,g,q⟩:= chooseH (fun i=> (B.launch.smaller.tendsto_atTop.eventually (eventually_ge_atTop (Y i).s)).and ((B.launch.eager.tendsto_atTop.eventually (eventually_gt_atTop P.calibration.ℓ)).and ((hp i).and (((ht i).eventually_le_const (P.macroStep_pos i)).and
   (keyV_go.eventually_le_const ((Y i).real_width_pos P 3))))))
 refine ⟨n,⟨g,fun i=> (q i).1, fun i=>(q i).2.1, fun i=>(q i).2.2.1⟩,fun i k a b v y=>?_⟩
 obtain ⟨W,h,s,h'⟩:=N (n i)
 have ht₂:= (Y i).zoom_bell P 3 _ (q i).1
 have hs: W ≤ (Y i).zoom P (c (n i)) 3:=by
    have u:=s.trans ((q i).2.2.2.2)
    rw [← ht₂, bell] at u
    rw [Int.cast_natCast] at u
    exact_mod_cast le_of_mul_le_mul_right u (P.macroStep_pos _)
 exact (P.sewing_pay k (ξ) (Y i) h' (h _) hs (q i).1 v y).trans ((q i).2.2.2.1)

omit B N
lemma fennel {F:P.Nib 3 (P.advocate 3 x 3)}
 (p:P.Iguana 3 ξ F Y)
 (q:P.Sown x c r Y n)
 (t:Tendsto (fun i=>(Q Z i).realWidth P 3) atTop (𝓝 0)):
 P.Iguana 3 ξ (fun a b=>ζ Z • F a b) (fun i=>P.stitchApron Z (Y i) (c (n i)) (r (n i))):=by
 refine ⟨NibPay.smul _ p.pay,t,?_⟩
 intro a b u v
 have hx:=p.read u v
       (show Tendsto (fun i=>a+w i) atTop (𝓝 a) by simpa using (p.thin.const_add a))
       (show Tendsto (fun i=>b-w i) atTop (𝓝 b) by simpa using (p.thin.const_sub b))

 apply (hx.smul (ζ Z)).mend P.macroStep_zero
 filter_upwards [t.eventually_le_const u, t.eventually_le_const v] with i g h
 exact q i Z _ _ g h

#print axioms Spine.fennel
#print axioms Spine.pollen_sale
