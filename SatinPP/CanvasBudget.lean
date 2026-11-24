import SatinPP.Climate
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition
variable (P:Spine)(R : P.Register)(j:Axis)
open Papal Regis.Head Gleam
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
open Worth Pays CF.BProof
open Real (log)
open Aria Casting MacroGrid
local notation "W"=>P.calibration
local notation "Q"=>P.par.block
variable (x:P.Spectrum0 3)
local notation "ξ"=>P.advocate 3 x j
local notation "Y"=>P.physicalEnergy j ξ
local notation "L"=>P.par.R.L.val
local notation "Υ"=>timeMesh P.par

variable {A C b B e:ℝ}{g m:ℕ}
local notation "J"=>ℕ×ℕ
local notation "lock"=>P.locket j ξ
local notation "tier"=> P.par.R.L

variable {ι:Type}(Z:ι→P.Apron)(I:Finset ι)(h:Axis→ℕ)(n:ℕ)
variable (u:∀ j,0< h j) (t:∀ i∈I,(Z i).s ≤ n) (f₀:∀ i∈ I,∀ j,(Z i).zoom P n j ≤ h j)
open SatinNucleus
include t in
lemma canvas_lock (D:P.Apron)(z:ι→ℂ)(p:D.F=∑ i∈ I,z i • (Z i).full P n)(hn:D.s=n)
 (a:∀ i∈ I,(Z i).realWidth P j ≤ D.realWidth P j)(r:ℝ)(w:D.realWidth P j ≤ r):
    lock D r r=∑ i∈ I,z i • lock (Z i) r r:=by
 subst n
 let l:=D.u j; let b:=D.realWidth P j
 have v:D.zoom P D.s j ≤ l:=by rw [show D.zoom P D.s j=l from by simp [Apron.zoom,l]]
 have H:P.Stock j ξ D.s (l+l) (P.shifts j l D.F) (lock D b b):=by
    have g:D.full P D.s=D.F:=by unfold Apron.full;rw [Nat.sub_self]; rfl
    rw [←g]; exact P.locket_stock j ξ D _ le_rfl v v
 let M:= ∑ i∈ I,z i • lock (Z i) b b
 have G:P.Stock j ξ D.s (l+l) (P.shifts j l D.F) M:=by
    rw [p,map_sum]; simp only [map_smul]
    apply stock_sum
    intro i hi; have h:=t i hi
    have l₁:(Z i).zoom P D.s j ≤ l:= (P.zoom_check j _ _ _ h).mpr (a i hi)
    exact (P.locket_stock j ξ _ D.s h l₁ l₁).smul _

 rw [P.widen_locket j ξ D (le_refl b) (le_refl b) w w, P.stock_unique j ξ H G]
 unfold M
 rw [map_sum]
 exact sum_congr rfl fun i k=>by
    rw [map_smul]; exact congrArg (z i • ·) (P.widen_locket j ξ (Z i) (a i k) (a i k) w w).symm

lemma pivot_lock (R:ι→ℝ)(l:List Axis)(r:ℝ)(d:bell Υ n (h j) ≤ r):
    lock ((P.canvas Z I h n u t f₀ (fun i=>(R i:ℂ))).pivot P l) r r=
       ∑ i∈ I,(R i:ℂ) • lock ((Z i).pivot P l) r r:=by
 let B:=P.canvas Z I h n u t f₀ (fun i=>(R i:ℂ)); let i'(i:ι):=(Z i).pivot P l
 have he: (B.pivot P l).realWidth P j=bell Υ n (h j):= B.pivot_w j P l
 refine P.canvas_lock j x i' I n (fun i v=> by rw [show (i' i).s=(Z i).s from (Z i).pivot_s P l]; exact t i v) _ _ (P.reflectorSum Z I h n u t f₀ ..) (B.pivot_s P l) (fun i v=>?_) _ (le_trans he.le d)
 unfold i'; change _≤(B.pivot P l).realWidth P j; rw [Apron.pivot_w, he]; exact (P.zoom_check j n (h j) (Z i) (t i v)).mp (f₀ i v j)



variable (s g:ℕ) (V:Coalition) (v:ℕ→ℕ)(a:ℕ→J→ℝ)(d:StrictMono v)
local notation "Yvote" i:max=> P.basePlay x g (v (n+i))
local notation "plate₀"=> (P.pleading x g s n V v (fun i=>a i (g,s)) d)
local notation "ballot" i:max=> ((P.rewardK g s * a (n+i) (g,s):ℝ):ℂ)
lemma pleading_lock (p:ℝ)(l:List Axis)(h:P.roomy*P.macroStep (v n)≤p):
 lock ((plate₀).pivot P l) p p =
    ∑ i∈ V.voters, (((V.w i:ℝ):ℂ)) • (ballot i • lock ((Yvote i).pivot P l) p p):=by
 simp only [smul_smul,←Complex.ofReal_mul]
 exact P.pivot_lock j x (fun i=>Yvote i) V.voters _ _ _ _ _
   (fun i=> (V.w i:ℝ)*(P.rewardK g s * a (n+i) (g,s))) l p ((P.base_wg x j g n V v).le.trans h)


/-- Singular price programme at thermal clearance. Eventual, not
punctual at a width depending on i. Seats of **exact** electorates.
Common B in all calendars, all mirror series, all e. -/
structure LocketFifth(P:Spine)(x:P.Spectrum0 3)(Ye:ℕ→ P.Apron)(B:ℝ):Prop where
 pos:0<B
 price(j:Axis)(l:List Axis)(p:ℝ)(t:0<p)(h:p≤1):
    ∀ᶠ i in atTop,(Ye i).realWidth P j < p ∧
     ‖P.locket j (P.advocate 3 x j) ((Ye i).pivot P l) p p‖ ≤ fifth B p

include R in
lemma fifth_cinema (T:P.Climate C)(w:g<s)(E:ScoutAnthem P x A C g s b v a)(q:ℕ→ Coalition):
    ∃ B,LocketFifth P x (P.cinema x g s v a q d) B:=by
 have hl:Tendsto (fun n=> (P.roomy:ℝ)*P.macroStep (v n)) atTop (𝓝 0):=by
    simpa only [mul_zero,Function.comp_apply] using (P.macroStep_zero.comp d.tendsto_atTop).const_mul (P.roomy:ℝ)
 obtain ⟨B,b,F⟩:=P.fifth_votes R x T g s w E
 refine ⟨B,b,?_⟩
 intro j l p hp y
 filter_upwards [eventually_forall_ge_atTop.mpr (F p hp y j l), hl.eventually (gt_mem_nhds hp)] with n h hw
 let V:=q n
 refine ⟨(P.pleading_w x j g s n V v d (fun i=>a i (g,s))).trans_lt hw,?_⟩

 unfold cinema
 rw [P.pleading_lock j x _ s g V v a d p l hw.le]
 apply (norm_sum_le ..).trans
 have he:(∑ i∈ V.voters,V.w i * fifth B p)= fifth B p:=by rw [←Finset.sum_mul,V.pledges,one_mul]
 refine le_trans ?_ he.le
 refine sum_le_sum fun i k=> ?_
 rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (V.signed i k)]
 exact mul_le_mul_of_nonneg_left (h _ (by exact Nat.le_add_right n i)) (V.signed i k)

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.fifth_cinema

