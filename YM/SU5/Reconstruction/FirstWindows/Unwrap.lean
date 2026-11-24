import YM.SU5.Reconstruction.FirstWindows.Polynomial
import YM.SU5.Reconstruction.FirstWindows.Compact
/-!
# Polymer spacetime footprint through the ONE finite path

Strengthen the physical localization statements to the actual finite transfers
at ALL later observable levels (even moving with the UV cutoff). Since spacing
is changing as well, check uniformly through any depth that there is no accidental
coincidence or alias: any pair of sites in the advancing physical support retains
its true displacement as the minimum centered representative. This geometric
statement does **not** let one interchange limits with continuum smearing!
No uniform-in-height statement about numerical quality of advancing via the common
limit `spreadTo`. On the finite path one uses instead `breathing`, with support
proved here and constant reading on a fixed polynomial. -/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 5000
set_option maxHeartbeats 300000
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
open SlabMark Fock Analysis Vale Lifted Tapestry.Altitude Tapestry.Exhibition
variable {U : Set RSpace}
variable (s : ℕ) (S : Finset Cover)
local notation "a" t:max => gaugeMesh Λ t
local notation "N" n:max t:max => Journey.side Y n t
local notation "B" n:max => volumeAround Λ l n S

section geometry

lemma period_width (n t : ℕ) : (a (s+t))*((More (N n (s+t))).val:ℝ) =
    (a s)*((More (N n s)).val:ℝ) := by
  change _ * ((((N n (s+t)).val*2:ℕ):ℝ)) = _*((((N n s).val*2:ℕ):ℝ))
  rw [SlabMark.refine_side]
  have h : 0 < (Λ.R.L.val:ℝ) := by exact_mod_cast Λ.R.L.property
  unfold gaugeMesh; push_cast; rw [pow_add]; field_simp

include H

/-- UNIFORM through all refinements of a physical stencil. No periodic aliases
on these finite partners once the elected period is sufficiently large. -/
theorem unwrapped : ∀ᶠ n in atTop, ∀ t : ℕ, PhaseChoice.FullDistances
    (volumeAround Λ l t S) (N n (s+t)) := by
  obtain ⟨c,hc,w⟩ := PhaseChoice.canBound Λ l s S
  have g : Tendsto (fun n => ((N n s).val:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (SlabMark.goes Y H s)
  filter_upwards [g.eventually_gt_atTop ((2*c)/(a s))] with n q t u p v z
  let m := N n (s+t)
  have hs : 2*c < ((N n s).val:ℝ)*(a s) := (div_lt_iff₀ (gaugeMesh_pos Λ s)).1 q
  have hw : 4*c < (a (s+t))*((More (N n (s+t))).val:ℝ) := by
    rw [period_width]
    change 4*c < _*(((N n s).val*2:ℕ):ℝ)
    rw [Nat.cast_mul,Nat.cast_ofNat]; linarith
  have ha := gaugeMesh_pos Λ (s+t)
  refine Lattice.lift_eq_iff.mpr ⟨by rw [map_sub],fun j => ?_⟩
  have h (x : Cover) (p : x ∈ B t) : |gaugePosition Λ (s+t) x j| ≤ c := by
    rw [←location_eq]; exact (w.persists t|>.contains p) j
  obtain ⟨x₁,x₂⟩ := abs_le.mp (h u p)
  obtain ⟨y₁,y₂⟩ := abs_le.mp (h v z)
  unfold gaugePosition at x₁ x₂ y₁ y₂
  constructor
  · apply show ((-((More m).val:ℝ)) < 2*((v j:ℝ)-u j)) →
        -((More m).val:ℤ) < 2*(v j-u j) from fun h=>by exact_mod_cast h
    apply lt_of_mul_lt_mul_right _ ha.le
    dsimp only [m]; nlinarith only [hw,y₁,x₂]
  apply show (2*((v j:ℝ)-u j) ≤ ((More m).val:ℝ)) →
    2*(v j-u j) ≤ ((More m).val:ℤ) from fun h=>by exact_mod_cast h
  apply le_of_mul_le_mul_right _ ha
  dsimp only [m]; nlinarith only [hw,y₂,x₁]

omit H

lemma distinct_wrap {m : Side} {S : Finset Cover} (p : PhaseChoice.FullDistances S m) :
    Set.InjOn (wrap (More m)) (S : Set Cover) := by
  intro x hx y hy h; have he := p _ hx _ hy; rw [h,sub_self] at he
  exact (sub_eq_zero.mp (he.symm.trans (by simp))).symm

end geometry

section budget

local notation "E₀" t:max => keep Λ l t (tent Y H) true (PhaseChoice.handstamp U)
local notation "X" => Cloud (Dome K)
local notation "YP" t:max m:max k:max => Tapestry.Pay Y t m k
local notation "𝓣" m:max k:max => tidalDressing Y H m k

lemma pure_coverage (f : ℕ → Dome (tent Y H)) (p : ∀ t, f t ∈ E₀ t) :
    ∃ S, PhaseChoice.SupportedPhysically Λ l s S U ∧ ∀ m k, Tapestry.Pay Y s m k →
      AtSupport false (Satin.region S (Journey.side Y m s)) (attire (Decking.finish (𝓣 m k) s f)) := by
  induction s with
  | zero =>
    obtain ⟨S,q,h⟩ := (show f 0 ∈ keep Λ l 0 K true (PhaseChoice.handstamp U) from p 0)
    exact ⟨S,h,fun i k _ => exhibited Y H 0 i S ((Tapestry.locates ..).1 q)⟩
  | succ n ih =>
    obtain ⟨S,q,w⟩ := ih
    obtain ⟨T,v,h⟩ := (show f (n+1) ∈ keep Λ l (n+1) K true (PhaseChoice.handstamp U) from p (n+1))
    let R := wingspan Λ l S
    refine ⟨R∪T, Tapestry.unionPrinted Λ l (n+1) R T _ q.step h,fun i k p=> ?_⟩
    have t := ascendSupport Y n i k S p (w i k ⟨p.1,Nat.le_of_lt p.2⟩)
    have z := exhibited Y H (n+1) i T ((Tapestry.locates ..).1 v)
    rw [show attire (Decking.finish (𝓣 i k) (n+1) f) =
      ascender Y n i k (attire (Decking.finish (𝓣 i k) n f)) * exhibit Y H (n+1) i (f (n+1)).val from
      funext fun x => tidal_rise Y H n i k f x]
    exact (t.mono (Finset.image_subset_image (show followBox (Λ:=Λ) (l:=l) S ⊆ R∪T from Finset.subset_union_left))).mulM (z.mono (Finset.image_subset_image Finset.subset_union_right))

local notation "gate₀" => (Set.univ : Set ℕ)∩ Set.Iic s

theorem covers_now (f : Altitude.Cloud (Dome K))
    (p : f ∈ jetty Λ l (tent Y H) true (PhaseChoice.handstamp U) ((Set.univ : Set ℕ)∩ Set.Iic s)) :
    ∃ S, PhaseChoice.SupportedPhysically Λ l s S U ∧
      ∀ i k, (YP s i k) → AtSupport false (Satin.region S (Journey.side Y i s))
        (attire (breathing Y H s i k f)) := by
  let M(x : X) := ∃ S, PhaseChoice.SupportedPhysically Λ l s S U ∧
    ∀ i k, (YP s i k)→ AtSupport false (Satin.region S (N i s)) (attire (breathing Y H s i k x))
  apply Altitude.boarded
    (P:={f| Officer gate₀ (fun t=>keep Λ l t K true (PhaseChoice.handstamp U)) f})
    (M:=M) ?_ ?_ ?_ ?_ p
  · intro f (h : Officer gate₀ (fun t=> E₀ t) f); obtain ⟨S,q,t⟩ := pure_coverage Y H s f h.observes
    refine ⟨S,q,fun i k p => ?_⟩
    change AtSupport _ _ (attire (breathing _ _ _ _ _ (pureShot K f)))
    rw [breathing_pure Y H s i k f (h.visible gate₀ _ Set.inter_subset_right)]; exact t i k p
  · refine ⟨∅, fun _ h=> Finset.notMem_empty _ h |>.elim,fun i k _=>?_⟩
    rw [map_zero,attire_none]; exact AtSupport.zeroM
  · rintro x y _ _ ⟨S,p,v⟩ ⟨T,q,w⟩
    refine ⟨S∪T,Tapestry.unionPrinted _ _ _ _ _ _ p q,fun i k p=>?_⟩
    rw [map_add,attire_add]
    exact ((v i k p).mono (Finset.image_subset_image Finset.subset_union_left)).addM
      ((w i k p).mono (Finset.image_subset_image Finset.subset_union_right))
  rintro c x _ ⟨S,p,v⟩; refine ⟨S,p,fun i k p=>?_⟩
  rw [map_smul,attire_scale]; exact (v i k p).smulM c

-- coherence on represented questions; `joins` for ANY later stage pair. Here no CFC/norm limits.
theorem hike_coverage {f : X} (p : f ∈ shorter (Dome (tent Y H)) s) (i k t : ℕ)
    (z : Tapestry.Pay Y (s+t) i k)
    (q : AtSupport false (Satin.region S (side Y i s)) (attire (breathing Y H s i k f))) :
    AtSupport false (Satin.region (B t) (side Y i (s+t))) (attire (breathing Y H (s+t) i k f)) := by
  induction t with
  | zero => exact q
  | succ t ih =>
    have e : f∈ shorter (Dome K) (s+t) := Altitude.climbs _ (by omega) p
    have h : s+(t+1)=s+t+1 := by omega
    rw [h] at z ⊢
    have b := ascendSupport Y (s+t) i k (B t) z (ih ⟨z.1,Nat.le_of_lt z.2⟩)
    unfold breathing
    rw [Decking.joins (𝓣 i k) _ f (auxiliaryPad K) e]
    change AtSupport false _ (attire (music Y (s+t) i k _))
    rw [music,flowing]; exact b

end budget
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
