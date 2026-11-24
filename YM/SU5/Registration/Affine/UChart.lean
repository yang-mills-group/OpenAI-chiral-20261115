import YM.SU5.Registration.Affine.Rated
import YM.SU5.Registration.Affine.Collateral
/-!
  # The Euclidean, late-consultation fields over our M4 map
  Unprojected ColorHil -> G uses coherence of this same elected character. G
  has powers w.r.t. actual physical clock, not arbitrary GNS Hilbert built per axis.
  Work with WPermit estimates on ANY stamped family with coefficients at its
  native printed height. Use to compute Schwinger prices and ordered transfer.
  Projection in pricing sharp readings from G is only qualified where authorized
  (`Ellis` & all-coordinate separations etc.).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 400000
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
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set
open SatinRegistration
namespace Spine
variable (P:Spine)
-- geometry ANY axes
local notation "Χ"=>P.Spectrum0
local notation "Θ"=>P.advocate 3
local notation "E₀"=>P.ColorHil
local notation "H₀"=>P.ManyF
local notation "qz"=>P.wealth
local notation "S₀"=>P.seasons
variable (x:P.Spectrum0 3)(a:Axis)
local notation "ξ"=>Θ x a
local notation "S"=>(P.seasons a (P.advocate 3 x a))
local notation "H"=>(P.ColorHil a (P.advocate 3 x a))
local notation "G"=>(P.ManyF a (P.advocate 3 x a))
local notation "pc"=>P.cartage a (P.advocate 3 x a)
local notation "T₀"=> (S).E
local notation "Ω"=> P.heaven a ξ
local notation "T"=> timeMesh P.par
open Swatch
local notation "τ" p:max=> Real.toNNReal (p:ℝ)
local notation "GOp" x:max=> (P.ManyF a (P.advocate 3 x a)).Op
local notation "Θ'" x:max=> P.seasons a (P.advocate 3 x a)
local notation "Φ"=>P.Spectrum0 3
/-! # Real pose stability of all-character prices, on generic configurations.

 Want generic all-axis separation for this step. A displacement along one coordinate
 can be paid that way by heat evolution at the Outer interior cuts in THAT axis.
 Use different permutations for each axis. Genuine cap estimate, even on varying
 height and pose, then max over spectrum. This part applies to every program with
 just the uniform (all-characters) bound & geometry on the purchased stencils.
-/
variable {I:Type*}(K:P.Register)(L:List I) (p:I→Vantage)(A:I→P.Swatch)
variable (f g:I→ℝ)(t:Dressing a L p f g)
variable {σ:ℕ→I→ℕ}(v:∀ i∈ L,Tendsto (fun k=>σ k i) atTop atTop)(u:∀ i∈ L,(A i).Finishes)
variable {q q':ℕ→I→Vantage}(p0:∀ i∈ L,Tendsto (fun k=> q k i) atTop (𝓝 (p i)))(p1:∀ i∈ L,Tendsto (fun k=>q' k i) atTop (𝓝 (p i)))
local notation "Gσ" n:max=> fun i=> (A i).fieldA (σ n i)
local notation "c₀" k:max i:max=> P.cane k a
local notation "L!" k:max p:max=> P.Ancestral k a L A p
local notation "Λσ" p:max=> fun (i:ℕ)(k:P.Spectrum0 3)=>P.Ancestral k a L A (p i) (σ i)
-- extensibility. pick common bound C uses `∀ poses v` already.
include t u
lemma reach_cost (h:∀ i∈ L,P.ThresholdPrice a (A i)): ∃ C≥(0:ℝ), ∀ i∈ L,∀ (q:ℕ→Vantage)(σ:ℕ→ℕ), Tendsto q atTop (𝓝 (p i)) → Tendsto σ atTop atTop → AllBills (fun x=> GOp x) atTop (fun j x=> (A i).scoop P x a (f i) (g i) (q j) (σ j)) C:=by
 classical
 -- induce over L (loosen t for future) via finset_sup' nonempty optional; pick at least empty 0
 choose! C hz hv using (fun i=> fun k:i∈L=> P.threshold_scoop a (A i) (h i k) (u i k) (f i) (g i) (p:=p i) (t.1 i k).1 (t.1 i k).2)
 let Z:= L.toFinset; let a₀:= ∑ i∈ Z,C i
 have ht:0≤a₀:=sum_nonneg fun i e=>hz i (List.mem_toFinset.mp e)
 exact ⟨a₀,ht,fun i x q σ p d=>(hv i x q σ p d).mono fun j h k=>(h k).trans (single_le_sum (fun i c=> hz i (List.mem_toFinset.mp c)) (List.mem_toFinset.mpr x))⟩
include v p0 p1
lemma time_progress (h:∀ i∈ L,P.ThresholdPrice a (A i))(x:∀ i∈ L,∀ᶠ k in atTop,∀ j:Axis,j≠a→ q k i j = q' k i j): Agrees (b:=fun x:P.Spectrum0 3=>GOp x) atTop (fun i k=> P.RawOp k a L A (q i) f g (σ i)) (fun i k=> P.RawOp k a L A (q' i) f g (σ i)):=by
 obtain ⟨B,pb,hb⟩:= P.reach_cost a L p A f g t u h
 refine Agrees.word L (fun k=>P.stoves_paidOne k a) _ _ ?_ (fun i c=> P.move_time_ok a (A i) (h i c) (u i c) _ _ (t.1 i c).1 (t.1 i c).2 (v i c) (p0 i c) (p1 i c) (x i c)) -- tune notation case g
 exact fun i c=> ⟨B,pb,hb i c (fun j=> q j i) (fun k=>σ k i) (p0 i c) (v i c)⟩
omit p1 in
lemma wearing : Agrees (b:=fun _=>ℂ) atTop (fun n x=> P.Ancestral x a L A (q n) (σ n)) (fun n x=> P.RawPrice x a L A (q n) f g (σ n)):= SatinRegistration.of_eq ((P.classical_late a L p A f g atTop v p0 t u).mono fun i g₁=> funext fun x=> (P.raw_classical x a L A f g _ _ g₁).symm) -- `.. g` invalid syntax ! tune
omit t
lemma time_cover (h:LightsCross a L p)(z:∀ i∈ L,P.ThresholdPrice a (A i))(y:∀ i∈ L,∀ᶠ k in atTop,∀ b:Axis,b≠a→ q k i b=q' k i b): Agrees (b:=fun _=>ℂ) atTop (fun n x=> P.Ancestral x a L A (q n) (σ n)) (fun n x=>P.Ancestral x a L A (q' n) (σ n)) := by
 classical
 obtain ⟨f,g,h⟩:= sews a L p h
 have he:= P.time_progress a L p A f g h v u p0 p1 z y
 exact (P.wearing a L p A f g h v u p0).trans ((he.verify (fun x=> P.heaven a (P.advocate 3 x a)) (fun k=>P.stone_norm a (Θ k a))).trans ((P.wearing a L p A f g h v u p1).symm))
omit p1 in
lemma wear_perm (z:List I) (Z:L.Perm z) (b:Axis)(P':LightsCross a L p)(k:LightsCross b z p)(K:P.Register): ((Λσ q):ℕ→Φ→ℂ)=ᶠ[atTop] (fun n x=>P.Ancestral x b z A (q n) (σ n)):=by
 filter_upwards [P.power_finishes a L p A u v p0 P',P.power_finishes b z p A (fun i y=>u i (Z.mem_iff.mpr y)) (fun i y=>v i (Z.mem_iff.mpr y)) (fun i y=>p0 i (Z.mem_iff.mpr y)) k] with i σ₀ q₀
 funext x; unfold Ancestral; exact congrArg₂ HMul.hMul (Z.map _|>.prod_eq) (P.unanimous 3 x _ L (q i) a b z σ₀ q₀ Z (Classical.choice (P.ellisP 3 x K)))
-- all axes. interpolation list of one-axis coordinate updates.
include K
lemma throughout (a0:LightsCross a L p)(b0:StarCluster L p)(P':∀ i∈L,∀ b:Axis,P.ThresholdPrice b (A i)): Agrees (b:=fun _=>ℂ) atTop (fun n x=> P.Ancestral x a L A (q n) (σ n)) (fun n x=>P.Ancestral x a L A (q' n) (σ n)) := by
 classical
 let Q(M:List Axis)(n:ℕ)(i:I):Vantage:=fun j=> if j∈M then q' n i j else q n i j
 have h(M:List Axis)(i:I)(x':i∈L): Tendsto (fun k=> Q M k i) atTop (𝓝 (p i)):=tendsto_pi_nhds.mpr (fun j=> by unfold Q; by_cases h:j∈ M; simpa [h] using tendsto_pi_nhds.mp (p1 i x') j; simpa [h] using tendsto_pi_nhds.mp (p0 i x') j)
 have hx(M:List Axis): Agrees (b:=fun _=>ℂ) atTop (Λσ q) (Λσ (Q M)):=by
    induction M with
    | nil=> rw [show Q []=q from (by unfold Q; simp only [List.not_mem_nil, ↓reduceIte])]; exact Agrees.refl _
    | cons b m ih=>
       obtain ⟨z,Z,hz⟩:= b0 b; let T₁:= fun i e=>u i (Z.mem_iff.mpr e); let M':= Q m; let O(k:List Axis)(n:ℕ)(x):=P.Ancestral x b z A (Q k n) (σ n)
       refine ih.trans ((SatinRegistration.of_eq (P.wear_perm a L p A v u (h m) z Z b a0 hz K)).trans ((?_ : Agrees atTop (O m) (O (b::m))).trans (SatinRegistration.of_eq ((P.wear_perm a L p A v u (h (b::m)) z Z b a0 hz K).symm)))) -- Order K tune. include from omit K wrong if never incl? remove omit K
       exact P.time_cover b z p A (fun i e=>v i (Z.mem_iff.mpr e)) T₁ (fun i e=>h m i (Z.mem_iff.mpr e)) (fun i e=>h _ i (Z.mem_iff.mpr e)) hz (fun i e=>P' i (Z.mem_iff.mpr e) b) (fun i _=>Eventually.of_forall fun k j u=> by unfold Q; simp [u])
 rw [← show Q Vacancy.ordinate=q' from (by unfold Q; simp only [Vacancy.ordinates, ↓reduceIte])]; exact hx _ -- tune spaces
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.throughout
#print axioms Spine.time_progress
#print axioms Spine.reach_cost
