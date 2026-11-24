import YM.SU5.FiniteGaugeData.Dally.Archon
import YM.SU5.FiniteGaugeData.Mist.Zinnia
/-!
 # Ward estimator, freight.
 -/
noncomputable section
open Metric Filter Function WithLp Set
open scoped Topology NNReal ENNReal InnerProductSpace
set_option autoImplicit false
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Galleon.Dai
open _root_.YM Dally Gem Leal Leal.Breve Celeritas Land Mist OS OS.Semigroup Flute Apso Mink
variable {K : Axis → Hilbert} (W : ∀ i : Axis, OS.Semigroup (K i) i)
    {ι : Type} (G : Canopy (K timeAxis) ι) (ω : ∀ i, (K i).space) (A : Tribe G)
variable {n : ℕ} (u : Fin n → ι) (w : Palette G u)
variable (b : SpaceAxis) (x : Points n) (t s : ℝ)
attribute [local instance] ostensible
local notation "ₜ" => timeAxis
open Lattice Hills
variable (L : Side)
def stampable (n : ℕ) : Set (Points n) := {x | ∃ g : Fin n × Axis → VistaQ L, (fun i => (g i:ℝ)) = (fun i : Fin n × Axis => x i.1 i.2)}
lemma grid (n : ℕ)(p : 1 < L.val) : Dense (stampable L n) := by
  let f := fun (x : Fin n × Axis → VistaQ L) (v : Fin n × Axis) => (x v : ℝ)
  let U : Points n ≃L[ℝ] (Fin n × Axis → ℝ) := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => E4)).trans Fuchsia.linen.symm
  have d : DenseRange f := DenseRange.piMap (fun _=> (indicate L p).dense)
  exact (d.preimage U.toHomeomorph.isOpenMap)
abbrev gate (i:ℕ) := spinT L i 1
lemma hatch (i:ℕ) : 0 < gate L i := by unfold gate spinT; have := tea_pos L i; positivity
lemma hurl (p : 1<L.val) : Tendsto (gate L) atTop (𝓝 0) := by
  have H : 1 < (L.val:ℝ) := by exact_mod_cast p
  apply Filter.Tendsto.congr _ (tendsto_pow_atTop_nhds_zero_of_lt_one
    (r := (L.val:ℝ)⁻¹) (by positivity) (by bound))
  intro n; simp [gate, spinT,one_div]
-- micro-birth using TRUE ONE-TICK'. Register the sensor probes (POINT positions) all on each high enough common tick epoch. (Cask parts still may require nonintegral `past` as above; these snap separately.)
variable (j : ℕ)
abbrev registry (p : Fin n → Axis →ℤ) := points fun i=> toLp 2 fun a=> spinT L j (p i a)
def flight (q : Fin n → Axis→ℤ)(i : Fin n)(a : Axis) := q + Pi.single i (step a : Cover)
lemma flight_now (p : Fin n → Axis →ℤ) (i:Fin n)(a:Axis): registry L j (flight p i a)=Leak (registry L j p) i a (gate L j):= by
  apply PiLp.ext; intro k; apply PiLp.ext; intro b
  by_cases w:i=k
  · subst k; by_cases h : a=b
    · subst b; simp [Leak, registry, flight, step, gate, slot_add]
    simp [Leak, registry, flight, step, gate, slot_add,Ne.symm h]
  simp [Leak,registry,flight,step,slot_add,w,Ne.symm w]
lemma advert (p : x ∈ stampable L n) :
    ∀ᶠ k in atTop,∃ y : Fin n→Axis→ℤ, x=registry L k y := by
  obtain ⟨g,e⟩ := p
  filter_upwards [eventually_all.mpr fun i=> frequentT L (g i)] with k h
  choose t c using h
  refine ⟨fun i j=> t (i,j), PiLp.ext fun i=> PiLp.ext fun j=>?_⟩
  change x i j= spinT L k _
  exact (congrFun e (i,j)).symm.trans (congrArg (fun v:VistaQ L => (v : ℝ)) (c (i,j)).symm)

section
variable {D : Type} [DecidableEq D] (L' : List D) (m : D→ℕ)
private lemma loader (j:D) (p : j∉L') : ∀ᶠ d in Raster L' m, d j=m j := by
  induction L' generalizing m with
  | nil => simp [Raster]
  | cons i L ih =>
    rw [Raster,eventually_bind]; refine Eventually.of_forall fun q => (ih _ ?_).mono fun d t=> ?_
    · exact fun e=> p (List.mem_cons_of_mem _ e)
    exact t.trans (update_of_ne (fun e=>p (List.mem_cons.mpr (Or.inl e))) q m) -- order
lemma lashing (j:D)(p : j∈ L')(t:L'.Nodup) : Tendsto (fun i=> i j) (Raster L' m) atTop := by
  induction L' generalizing m with
  | nil=> simp at p
  | cons i L ih =>
    refine tendsto_def.mpr fun S h=> ?_
    rw [← Filter.eventually_mem_set, Raster, eventually_bind]
    rcases List.mem_cons.mp p with p|p
    · subst j; filter_upwards [h] with u U
      filter_upwards [loader L (update m i u) i (List.nodup_cons.mp t).1] with d v
      change d i∈ S; simpa only [v,update_self]
    exact Eventually.of_forall fun u => tendsto_def.mp (ih (update m i u) p (List.nodup_cons.mp t).2) S h
end
lemma rateSmall {D : Type} (T : D→ Shrine K) (E : Fleet W G A T) (θ:ℝ) (p : 0 < θ) :
    ∀ᶠ v in Raster (Each n) 0, ∀ (j : Job n)(i : Fin n)(a:Axis), ((T (assembly W G A u w b t T E v j i)).t a:ℝ) < θ := by
  refine eventually_all.mpr fun j => eventually_all.mpr fun i=> eventually_all.mpr fun a=> ?_
  let K' := race G u w b t j i
  have u : Tendsto (fun k=> ((T (E.book K' k)).t a:ℝ)) atTop (𝓝 0) :=
    NNReal.continuous_coe.continuousAt.tendsto.comp ((E.back K').grows a)
  exact (u.comp (lashing (Each n) 0 i (List.mem_finRange i) (List.nodup_finRange _))).eventually (gt_mem_nhds p)
#print axioms rateSmall
#print axioms grid
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Galleon.Dai
