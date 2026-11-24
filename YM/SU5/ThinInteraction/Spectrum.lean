import YM.SU5.ThinInteraction.Payment
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2500
noncomputable section
namespace YM.SatinThin
open Set Filter MeasureTheory Spectral Six TopologicalSpace
open scoped Topology NNReal ENNReal
variable (μ: Measure E4) [IsFiniteMeasure μ]
open Classical

/-- Physical unit cube, arch uses sup-norm boxes. -/
def squareTile (k : Fin 3→ℤ) : Set E4:={p:E4| ∀ i:Fin 3, YM.spatial p i ∈ Ico ((k i:ℤ):ℝ) ((k i:ℤ)+1:ℝ) }
lemma tile_meas (k : Fin 3→ℤ) : MeasurableSet (squareTile k):= by
  simp only [squareTile,Set.setOf_forall]; refine MeasurableSet.iInter (fun i => ?_); exact (show Measurable (fun p:E4=>YM.spatial p i) from by fun_prop) measurableSet_Ico
omit [IsFiniteMeasure μ] in
lemma some_piece (A : Set E4) (h : μ A ≠ 0) : ∃ k, μ (A∩ squareTile k) ≠ 0:= by
  by_contra! H
  apply h; refine measure_mono_null (t:=⋃ k,A∩squareTile k) (fun x hx=>?_) (measure_iUnion_null H)
  exact Set.mem_iUnion.mpr ⟨fun i=> ⌊YM.spatial x i⌋,hx,fun i=>⟨Int.floor_le _,Int.lt_floor_add_one _⟩⟩
lemma chooseScale (I : Set ℝ) (ρ : ℝ) (t : μ (by_time (cents I ρ)) ≠ 0) (u : ∀ x∈cents I ρ, 2 < x):
    ∃ m:ℕ, 0 < m ∧ ∃ k:Fin 3→ℤ, let A:=by_time (band I ρ m); 0 < μ.real (A∩squareTile k) ∧
      ∀ l:Fin 3→ℤ, μ.real (A∩squareTile l)≤2*(μ.real (A∩squareTile k)) := by
  have he : ∃ m:ℕ, 0 < m ∧ μ (by_time (band I ρ m)) ≠ 0:= by
    by_contra! h
    apply t; let J:=(fun i:{m:ℕ//0 < m} => by_time (band I ρ i.val)); refine measure_mono_null (t:=⋃ i,J i) (fun x hu=>?_) (measure_iUnion_null (fun i=>h i i.property))
    let y:= YM.time x; let n:= ⌊y-1⌋₊; have ht:2<y:=u y hu
    refine Set.mem_iUnion.mpr ⟨⟨n,Nat.floor_pos.mpr (by linarith)⟩,hu,?_⟩
    change (n:ℝ)+1 ≤ y ∧ y ≤ (n:ℝ)+2
    have hb:(n:ℝ)≤y-1:= Nat.floor_le (by linarith); have he:y-1<(n:ℝ)+1:= Nat.lt_floor_add_one _; constructor <;> linarith
  obtain ⟨m,v,k'⟩:= he; let A:= by_time (band I ρ m)
  obtain ⟨z,p⟩:= some_piece μ _ k'; let f (i:Fin 3→ℤ):= μ.real (A∩squareTile i); let R:= sSup (range f)
  have ht (i:Fin 3→ℤ): f i ≤ R := le_csSup ⟨μ.real Set.univ, by rintro _ ⟨i,rfl⟩; exact measureReal_mono (Set.subset_univ _)⟩ (mem_range_self (i:=i) (f:=f))
  have hr : 0 < R:= (ENNReal.toReal_pos p (measure_ne_top _ _)).trans_le (ht z)
  obtain ⟨_,⟨k,rfl⟩,hc⟩:= exists_lt_of_lt_csSup (range_nonempty f) (half_lt_self hr)
  exact ⟨m,v,k,(half_pos hr).trans hc,fun l=> show f l ≤ 2 * f k from by linarith only [ht l,hc]⟩
end YM.SatinThin
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Spine
open YM.SatinThin
namespace Thinning
open Set Aria
variable {P:Spine} {c r: ℕ → ℕ} {x:P.Spectrum0 3}
local notation "S" => P.seasons 3 (P.otherSpectrum 3 3 x)
local notation "Ξ" => (S).ℚmeasure
local notation "H" => P.ManyF 3 (P.otherSpectrum 3 3 x)
def alk (s n:ℕ) (x:P.Spectrum0 3) (Z:Lead.Clan) (opp:Bool) : P.ManyF 3 (P.otherSpectrum 3 3 x):=
  flashY x (if opp then P.RTest Z s n else P.FTest Z s n) 3
local notation "μ" Z:max s:max n:max => (Ξ).diagonal (alk s n x Z false)
-- useful lemmas
section
variable {I: Set ℝ} (hu : IsOpen I) (hv : I.Nonempty) (hp : ∀ y∈I, 0<y)
include hu hv hp
lemma land (B: P.Transmission x c r) (Y:Launch P c r) :
    ∀ᶠ i:ℕ in atTop, ∀ Z, (μ Z (c i) (r i)) (by_time (cents I (P.dew (c i) (r i))))≠0 := by
  classical
  have ho : IsOpen (by_time I) := hu.preimage Mink.clock_cont
  obtain ⟨y,hy⟩ := hv
  let p:= YM.position 0 y
  have hx : (Mink.inside∩by_time I).Nonempty:=⟨p, by
    constructor
    · change ‖YM.spatial p‖<YM.time p; simpa [p] using hp _ hy
    simpa [by_time,p] using hy⟩
  obtain ⟨d,k,e⟩:= B.window _ ho hx
  filter_upwards [e] with i hc
  intro Z
  let s:= c i; let n:= r i; let ρ:= P.dew s n; let A:= by_time (cents I ρ)
  have hg : MeasurableSet A:= bymeas (cents_meas I hu.measurableSet ρ)
  have ha (w:E4)(hu:w∈A): 0<YM.time w :=
    pos_of_mul_pos_right (a:=ρ) (hp _ hu) (P.dew_pos s (Y.unitSize i)).le
  have ht:A=Cheer.press ρ (by_time I):=by
    ext z; change (ρ*YM.time z∈I) ↔ YM.time (ρ • z)∈I; rw [Mink.clock_mul]
  have hy: (Ξ).region A (P.birthCloud x Z s n) ≠ 0:=by rw [ht]; exact (coercion_li (H) _ d k hc).ne_zero Z
  let f:=P.birthCloud x Z s n
  let Q:=(S).E (P.probeWidth s n 3).toNNReal
  have hz: alk s n x Z false = Q (f - (S).E (P.increment s n) f) :=
    Eq.trans (P.centerEntry x s n Z) (congrArg (fun x:(H) => Q x) (P.filtered_explicit x s n Z))
  have H' := leave_zero S (P.probeWidth s n 3).toNNReal (P.increment s n) (P.increment_pos s n (Y.unitSize i)) A hg ha f hy
  intro e
  exact H' ((congrArg (fun x:(H) => (Ξ).region A x) hz).symm.trans (((Ξ).null_pair hg (alk s n x Z false)).1 e))
omit hu hv hp
end
section bank
variable (x)(s n:ℕ)(a:ℝ)
-- take I=(a,a+1)
abbrev ledger := cents (Ioo a (a+1)) (P.dew s n) -- include P
local notation "B" => Ioo a (a+1)
variable (Z:Lead.Clan)
-- Lean binder order
structure Portfolio where
  m : ℕ
  clock : 0 < m
  k : Fin 3 → ℤ
  positive : 0 < (μ Z s n).real (by_time (YM.SatinThin.band (Set.Ioo a (a+1)) (P.dew s n) m)∩ squareTile k)
  big (l:Fin 3 → ℤ) : let A := by_time (YM.SatinThin.band (Set.Ioo a (a+1)) (P.dew s n) m);
    (μ Z s n).real (A∩ squareTile l)≤2*(μ Z s n).real (A∩ squareTile k)
#check @Portfolio
lemma availability (Y:Launch P c r)(u:P.Transmission x c r)(p:0<a) :
     ∀ᶠ i:ℕ in atTop, ∀ Z, Nonempty (Portfolio x (c i) (r i) a Z) := by
  have hρ:= P.proper_dew c r Y
  have ht : ∀ z∈Set.Ioo a (a+1),0<z:=fun _ h=>p.trans h.1
  filter_upwards [land (I:=Set.Ioo a (a+1)) isOpen_Ioo (Set.nonempty_Ioo.mpr (lt_add_one _)) ht u Y, hρ.eventually (gt_mem_nhds (half_pos p))] with i h e
  intro Z; let s:= c i; let n:= r i; let μ' := (μ Z s n); let ρ:=P.dew s n
  have hc:∀ x∈ cents B ρ, (2:ℝ)<x := by
    intro x hx; have he : a < ρ*x := hx.1; have hh : ρ < a/2:= e; have hk : 0<ρ:=P.dew_pos s (Y.unitSize i); nlinarith only [he,hh,hk]
  obtain ⟨m,b,k,v,w⟩:= chooseScale μ' (Ioo a (a+1)) ρ (h Z) hc
  exact ⟨m,b,k,v,w⟩
-- h time real in the Shop
abbrev ShopP (P:Spine)(s n:ℕ) := Shop (marks (timeMesh P.par) : Set ℝ) (P.probeWidth s n 3)
abbrev twiceP (P:Spine)(s n:ℕ):ℝ≥0 := (2*P.probeWidth s n 3).toNNReal
namespace Portfolio
-- caution dot binder order
variable {s n x a Z} (p:Portfolio x s n a Z)
noncomputable def energy : Set ℝ := YM.SatinThin.band (Set.Ioo a (a+1)) (P.dew s n) p.m
lemma energy_meas : MeasurableSet p.energy := band_meas (Set.Ioo a (a+1)) measurableSet_Ioo _ _
abbrev purchases : Set E4:= by_time p.energy
lemma purchases_meas : MeasurableSet p.purchases:= bymeas p.energy_meas
noncomputable def amp : ℝ:= (Real.sqrt ((μ Z s n).real (p.purchases ∩ squareTile p.k)))⁻¹
lemma ample : 0<p.amp:= inv_pos.mpr (Real.sqrt_pos.mpr p.positive)
noncomputable def intended : H := enjoy S p.energy p.amp (twiceP P s n) false (alk s n x Z false)
lemma appointment (δ:ℝ) (h:0<δ) : ∃ c:ShopP P s n→₀ℝ,
    let Q:= (P.seasons 3 (P.otherSpectrum 3 3 x)); ‖p.intended - focusing Q false c (alk s n x Z false)‖<δ ∧
      ‖focusing Q true c (alk s n x Z true)‖<δ := by
  have hA : Set.Subset p.energy (Set.Ioi 0) := YM.SatinThin.band_pos (A:=Set.Ioo a (a+1)) (ρ:=P.dew s n) (m:=p.m)
  have hh:= enjoy_both («H» := P.ManyF 3 (P.otherSpectrum 3 3 x)) (h:=P.probeWidth s n 3) (T:=(marks (timeMesh P.par) : Set ℝ)) S p.energy p.energy_meas p.amp (twiceP P s n) (alk s n x Z) hA (daylight (timeMesh P.par)) (P.width_here s n 3) δ h
  let l:ShopP P s n→₀ℝ:=hh.choose; let u:=hh.choose_spec
  refine ⟨l,u false,?_⟩
  let w:= focusing S true l (alk s n x Z true)
  have he: ‖(0:(H).Op) (alk s n x Z true)-w‖<δ:= u true
  simpa only [_root_.zero_apply,zero_sub,norm_neg] using he
end Portfolio
end bank
#print axioms availability
#print axioms Portfolio.appointment
end Thinning
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
