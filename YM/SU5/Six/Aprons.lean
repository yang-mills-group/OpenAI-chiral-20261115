import YM.SU5.Aria.Grotto
import YM.SU5.Six.KeepCharge
import YM.SU5.Six.MirrorCharge
set_option maxHeartbeats 200000
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
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
open Aria Set
open Cheer (Narrow)

/-!
# Six gauge-matter probe bodies, as in the construction notes

`ProbeWidth` uses the full footprint budget in fermion-spacing units.
RealWidth is implemented by full ticks. (Names lowerCamelCase.)
-/
open Six
variable (P:Spine)(W:Lead.Clan)(s n:ℕ)
local notation "K"=>P.calibration
local notation "ℓ"=> P.calibration.ℓ
local notation "T"=> timeMesh P.par
abbrev sidesPerTick (P:Spine):ℕ:=16*P.par.block.val
lemma sides_pos : 0<P.sidesPerTick :=Nat.mul_pos (by decide) P.par.block.property
lemma sides_ruler : (P.sidesPerTick:ℤ)= ruler P.par.block:=by unfold sidesPerTick ruler; push_cast; rfl
-- increment of approx rho/2. Real ceilings after length in S was fixed.
def laterPulse : ℕ:= ⌈(n:ℝ) / P.sidesPerTick⌉₊
lemma pulse_pos (p:0<n) : 0<P.laterPulse n:= by
  have h : 0 < P.sidesPerTick := P.sides_pos
  unfold laterPulse; positivity

def probeRoof : ℕ:= 2*(ℓ+2*n)+1+P.sidesPerTick*P.laterPulse n+ℓ
def probeClock : Axis→ℕ:= Function.update (fun _=>ℓ+1) 3 (1+⌈(P.probeRoof n:ℝ)/P.sidesPerTick⌉₊)
def probeWidth (j:Axis):ℝ:= bell T s (P.probeClock n j)
lemma clock_positive (j:Axis): 0<P.probeClock n j:=by
  by_cases h:j=3 <;> simp [probeClock,h]
lemma clock_roof : (P.probeRoof n:ℤ)≤ ruler P.par.block*(P.probeClock n 3:ℤ):= by
  rw [←sides_ruler]
  unfold probeClock; rw [Function.update_self]
  have hp:= P.sides_pos
  let a:=P.probeRoof n; let N:=P.sidesPerTick; let M:= (1+⌈(a:ℝ)/N⌉₊:ℕ)
  have he : (a:ℝ) ≤ (N:ℝ)*M := by
    rw [mul_comm]
    apply (div_le_iff₀ (show 0<(N:ℝ) by exact_mod_cast hp)).1
    exact (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_add_left _ _)
  change ↑a ≤ (N:ℤ)*↑M
  exact_mod_cast he

def frontMat := P.stockS W (P.flash n)
def backMat : P.Test:= P.shifts 3 (P.laterPulse n) (P.frontMat W n)
abbrev measureStencil (n:ℕ):= (P.flash n).patio ∪ plow K 3 (P.laterPulse n) (P.flash n).patio
lemma front_real : P.frontMat W n∈enclave K:=P.celebrity (Lamour.Bridge.Celeste.flourish (P.flash n) W)
lemma back_real : P.backMat W n∈enclave K:= P.shifts_keep 3 _ (P.front_real W n)
lemma front_charge :
    (P.frontMat W n).val ∈ DressedPair K W.2 {nodeC (P.flash n).birth} {nodeC (P.flash n).death} (P.flash n).patio := by
  let A:=P.flash n
  have he: Papal.household K (A.groundWord W)= Lead.sing n A.wave • ∑ i∈Window.colors W,∑ j∈Window.colors W,Papal.household K (coilC A i j * trailC A i j):=by rw [Lamour.Bridge.Celeste.banner_sum]; unfold Papal.household; funext m; simp_rw [Pi.smul_apply,Finset.sum_apply]
  change Papal.household K (A.groundWord W) ∈ _
  rw [he]; apply Submodule.smul_mem
  refine Submodule.sum_mem _ fun i p=> Submodule.sum_mem _ fun j q=> ?_
  let S:=({nodeC A.birth}:Finset Cover); let L:= ({nodeC A.death}:Finset Cover)
  have hw:= Lamour.Bridge.Celeste.coil_paid A i j
  have hc: Coeff true A.patio (coilFlag A i j∘Prod.fst):=⟨fun p=>by contradiction,hw.env,hw.locus⟩
  have hl:removal K A.death (dnSpin A.slot) j∈ SinglePocket K W.2 L false:=pocket_removal K W.2 L
    (Finset.mem_singleton_self _) (congrArg Prod.snd (Finset.mem_filter.mp q).2) (dn_half _)
  have hr: creation K A.birth (upSpin A.slot) i ∈ SinglePocket K W.2 S true:=pocket_creation K W.2 S
    (Finset.mem_singleton_self _) (congrArg Prod.snd (Finset.mem_filter.mp p).2) (up_half _)
  rw [Lamour.Bridge.Celeste.stanza_book]
  exact Submodule.subset_span (show _∈_ from ⟨_,hc,_,Submodule.subset_span (show _∈ _ from ⟨_,hl,_,hr,rfl⟩),rfl⟩)
-- identification of family calls with source explicitly. sign of `sing n false` confirm!
lemma front_read (m:Side)(X:Fields ((K).c m)) : (P.frontMat W n).val m X=
    Lead.sing n false • ∑ i∈Window.colors W,∑ j∈Window.colors W, (Lamour.Bridge.Celeste.coilFlag (P.flash n) i j (onC ((K).c m) X.1)) • (Fock.remove (basisC ((K).c m) (P.flash n).death 2 j)*create (basisC ((K).c m) (P.flash n).birth 0 i)):=rfl
lemma body_ok : P.frontMat W n-P.backMat W n∈ bay K (P.measureStencil n) true := by
  apply Subalgebra.sub_mem
  · exact tallerBay K _ _ subset_union_left (P.visibility ..)
  exact tallerBay K _ _ subset_union_right (P.shifts_support 3 _ _ (P.visibility ..))
lemma birth_stencil (z:Cover)(p:z∈P.measureStencil n) : 0+(ℓ:ℤ)≤z (3:Axis):=by
  let x:= ruler P.par.block
  rcases Finset.mem_union.mp p with v|v
  · exact P.flash_here n _ v
  obtain ⟨w,u,rfl⟩:=plow_stays K _ _ _ v; rw [SlabMark.moves,if_pos rfl]
  exact (P.flash_here n w u).trans (le_add_of_nonneg_right (mul_nonneg (ruler_gene _).le (by positivity)))
lemma shelters (j:Axis) : Between K j (-ruler P.par.block* (P.probeClock n j:ℤ)) (ruler P.par.block*(P.probeClock n j:ℤ)) (P.measureStencil n):= by
  let U:= ruler P.par.block
  let a:=P.laterPulse n
  intro z t
  by_cases h:j=3
  · subst j; refine ⟨le_trans ?_ (P.birth_stencil n z t),?_⟩
    · gcongr; exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (ruler_gene _).le) (by positivity)
    have hg(x:Cover)(p:x∈ (P.flash n).patio): x 3 ≤ (2:ℤ)*(ℓ+2*n)+1:= by -- ℓ+2*n has ambiguous cast. target ℤ
      obtain ⟨t,w,rfl⟩:= Cube.range_leg _ (posDir 3) (2*n) x (List.mem_toFinset.mp p)
      simp [flash,kernel0,nodeC]; omega
    have hz:(P.probeRoof n:ℤ)= (2:ℤ)*(ℓ+2*n)+1+ U*a+ℓ:=by dsimp only [U,a]; rw [← sides_ruler]; unfold probeRoof; push_cast; rfl
    apply le_trans _ (P.clock_roof n); rw [hz]; have hP:0≤U*(a:ℤ):= mul_nonneg (ruler_gene _).le (by positivity)
    rcases mem_union.mp t with t|t; · linarith [hg z t]
    obtain ⟨y,e,rfl⟩:=plow_stays K 3 _ (P.flash n).patio t; rw [SlabMark.moves,if_pos rfl]; change (y 3+(U)*(a:ℤ))+_ ≤ _; linarith only [hg y e]
  have he:z j=1:=by
    rcases Finset.mem_union.mp t with t|t; · exact P.flash_fixed j n z t h
    obtain ⟨y,e,rfl⟩:=plow_stays K 3 _ (P.flash n).patio t; rw [SlabMark.moves,if_neg h]; exact P.flash_fixed j n y e h
  have H': ((ℓ+1:ℕ):ℤ) ≤ ruler P.par.block*((ℓ+1:ℕ):ℤ):= le_mul_of_one_le_left (by positivity) (ruler_gene _)
  rw [he,neg_mul,show P.probeClock n j=ℓ+1 from Function.update_of_ne h ..]; omega

def experimentBody : P.Apron where
 s:=s
 u:=P.probeClock n
 pos:=P.clock_positive n
 F:=P.frontMat W n - P.backMat W n
 S:=P.measureStencil n
 realM:= Subalgebra.sub_mem _ (P.front_real W n) (P.back_real W n)
 bay:= P.body_ok ..
 shelter:= P.shelters n
lemma body_birth : P.birthF 3 s (P.experimentBody W s n).F :=
  P.criteria 3 s (P.body_ok W n) (P.birth_stencil n) (P.experimentBody W s n).realM

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
