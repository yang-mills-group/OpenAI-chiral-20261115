import VerifiedSatinSelectedSectors

/-!
# All finer resolutions really fit -- physical cells, not fixed lattice sets

This file uses units in `location`: 1 unit = one fermion spacing of level zero.
The geometry is *Euclidean* only. Bounds concern support statements as in
`circum` and `AtSupport`; `tips` adds the site at the positive end of links
out of the supported box. No convergence statement with varying test claimed.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 300000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.One
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification Tapestry PhaseChoice

/-- union of actual printed shields, in matter-spacing units -/
def cells (Λ : Preparation) (l s : ℕ) (S : Finset Cover) : Set RSpace :=
  {p | ∃ i ∈ S, ∃ q ∈ Tapestry.shield Λ l s i, (fun j => q j / 2) = p}

theorem supported_iff_cells {Λ : Preparation} {l s : ℕ} {S : Finset Cover} {V : Set RSpace} :
    SupportedPhysically Λ l s S V ↔ cells Λ l s S ⊆ V := by
  constructor
  · rintro h _ ⟨x, hx, u, hu, rfl⟩
    exact h _ hx hu
  intro h x hx u hu
  exact h ⟨x, hx, u, hu, rfl⟩

theorem supported_cells (Λ : Preparation) (l s : ℕ) (S : Finset Cover) :
    SupportedPhysically Λ l s S (cells Λ l s S) := supported_iff_cells.mpr Set.Subset.rfl

theorem finer_inside (Λ : Preparation) (l s : ℕ) (S : Finset Cover) (n : ℕ) :
    cells Λ l (s+n) (volumeAround Λ l n S) ⊆ cells Λ l s S :=
  supported_iff_cells.mp ((supported_cells Λ l s S).persists n)

theorem same_measurement (Λ : Preparation) (s : ℕ) (x : Cover) :
    location Λ s x = Selected.gaugePosition Λ s x := by
  funext i
  unfold location Selected.gaugePosition Selected.gaugeMesh Tapestry.markZ precisionAt
  ring

theorem inner_cell {Λ : Preparation} {l s : ℕ} {S : Finset Cover} {p : RSpace}
    (h : p ∈ cells Λ l s S) : ∃ x ∈ S, ∀ i,
    |p i - Selected.gaugePosition Λ s x i| ≤ reserve Λ l * Selected.gaugeMesh Λ s := by
  obtain ⟨x, hx, q, hq, rfl⟩ := h
  refine ⟨x,hx,fun i => ?_⟩
  let a := precisionAt Λ s
  have ha : 0 < a := positiveScale Λ s
  have hi : |a * q i - (x i:ℝ)| ≤ (reserve Λ l:ℝ) := hq i
  have he : Selected.gaugeMesh Λ s= 1/(2*a) := rfl
  rw [Selected.gaugePosition, he]
  change |q i / 2 - (x i:ℝ)*(1/(2*a))| ≤ _
  rw [show q i/2 - (x i:ℝ)*(1/(2*a)) = (a*q i-x i)/(2*a) from by field_simp,
     abs_div,abs_of_pos (show 0 < 2*a by positivity), ←mul_div_assoc,mul_one]
  exact div_le_div_of_nonneg_right hi (by positivity)

theorem cells_apart {Λ : Preparation} {l s : ℕ} {X Y : Finset Cover} {a : ℝ} {i : Axis}
    (h : Selected.PhysicalHush (Λ:=Λ) (l:=l) s i X Y a) {p q : RSpace}
    (u : p ∈ cells Λ l s X) (v : q ∈ cells Λ l s Y) : p i + a ≤ q i := by
  obtain ⟨x,hx,g⟩ := inner_cell u
  obtain ⟨y,hy,f⟩ := inner_cell v
  have he := h.2 0 x hx y hy
  simp only [Nat.add_zero] at he
  have hp := le_of_abs_le (g i)
  have hq := neg_le_of_abs_le (f i)
  linarith

theorem cells_disjoint {Λ : Preparation} {l s : ℕ} {X Y : Finset Cover} {a : ℝ} {i : Axis}
    (h : Selected.PhysicalHush (Λ:=Λ) (l:=l) s i X Y a) :
    Disjoint (cells Λ l s X) (cells Λ l s Y) := by
  apply Set.disjoint_left.mpr
  intro x hx hx'
  have g := cells_apart h hx hx'
  linarith [h.1]

theorem compact_cells (Λ : Preparation) (l s : ℕ) (S : Finset Cover) :
    IsCompact (cells Λ l s S) := by
  let f (q : RSpace) (i : Axis) := q i / 2
  rw [show cells Λ l s S=⋃ x∈ S,f '' Tapestry.shield Λ l s x from by
        ext p; simp [cells,f]]
  apply S.finite_toSet.isCompact_biUnion
  intro x _
  apply IsCompact.image _ (show Continuous f from by unfold f; fun_prop)
  let a := precisionAt Λ s
  have ha : 0 < a := positiveScale Λ s
  let r : ℝ := reserve Λ l
  rw [show Tapestry.shield Λ l s x=Set.pi Set.univ (fun i : Axis => Set.Icc ((x i-r)/a) ((x i+r)/a)) from ?_]
  · exact isCompact_univ_pi fun _=> isCompact_Icc
  ext u
  change (∀ i:Axis, |a * u i - (x i:ℝ)|≤r) ↔ _
  rw [Set.mem_univ_pi]
  apply forall_congr'
  intro i
  rw [abs_le,Set.mem_Icc,div_le_iff₀ ha,le_div_iff₀ ha,mul_comm a]
  constructor <;> rintro ⟨b,c⟩ <;> constructor <;> linarith

lemma support_subset {Λ : Preparation} {l s : ℕ} {S : Finset Cover} {V W : Set RSpace}
    (p : SupportedPhysically Λ l s S V) (h : V ⊆ W) : SupportedPhysically Λ l s S W :=
  supported_iff_cells.mpr ((supported_iff_cells.mp p).trans h)

lemma member_bound {Λ : Preparation} {l s : ℕ} {S : Finset Cover} {x : Cover} {A : ℝ}
    (p : SupportedPhysically Λ l s S (cabin A)) (h : x∈ S) (j : Axis) :
    |(x j:ℝ)| ≤ 2*A*precisionAt Λ s := by
  let a:=precisionAt Λ s
  have ha: 0 < a := positiveScale Λ s
  have hz := SupportedPhysically.contains p h
  have hv : |(x j:ℝ)/a/2| ≤ A := hz j
  rw [abs_div,abs_div,abs_of_pos ha,abs_of_pos (by norm_num : (0:ℝ)<2),
    div_le_iff₀ (by norm_num : (0:ℝ)<2),div_le_iff₀ ha] at hv
  rw [mul_comm 2]
  exact hv

lemma tip_bound {Λ : Preparation} {l s : ℕ} {S : Finset Cover} {x : Cover} {A : ℝ}
    (p : SupportedPhysically Λ l s S (cabin A)) (h : x ∈ tips S) (j : Axis) :
    |(x j:ℝ)| ≤ 2*A*precisionAt Λ s+1 := by
  rcases Finset.mem_union.mp h with e|e
  · exact (member_bound p e j).trans (by linarith)
  obtain ⟨y,hy,t⟩:=Finset.mem_biUnion.mp e
  obtain ⟨k,_,rfl⟩:=Finset.mem_image.mp t
  simp only [Pi.add_apply, Int.cast_add]
  exact (_root_.abs_add_le ..).trans (add_le_add (member_bound p hy j) (by
    rw [Lattice.step_apply]; split <;> norm_num))

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
variable (H : Real.exp 1 ≤ Λ.x)

theorem no_alias (i : ℕ) (A : ℝ) (room : 4*A + 2 < (Journey.side Y i 0).val)
    (s : ℕ) (S : Finset Cover) (p : SupportedPhysically Λ l s S (cabin A)) :
    FullDistances (tips S) (Journey.side Y i s) := by
  let d:=precisionAt Λ s
  have hd : 0 < d := positiveScale Λ s
  have ha : 1 ≤ d := one_le_pow₀ (by exact_mod_cast (Λ.R.L.property : 1 ≤ Λ.R.L.val))
  let n:=Journey.side Y i s
  have he : (n.val:ℝ) = d*(Journey.side Y i 0).val:= by
    have hx := refine_side Y i 0 s
    rw [zero_add] at hx
    unfold n; rw [hx,Nat.cast_mul,Nat.cast_pow]
  intro x hx y hy
  rw [←map_sub, Lattice.lift_eq_iff]
  refine ⟨rfl,fun j=>?_⟩
  have ht : |(x j:ℝ)| ≤ 2*A*d+1:= tip_bound p hx j
  have hu : |(y j:ℝ)| ≤ 2*A*d+1:= tip_bound p hy j
  replace room:=mul_lt_mul_of_pos_left room hd
  have h : -((n.val:ℕ):ℝ) < (y j:ℝ)-x j ∧ (y j:ℝ)-x j< n.val:= by
    rw [he]
    obtain ⟨hx,hw⟩:=abs_le.mp ht; obtain ⟨hy,hz⟩:=abs_le.mp hu
    constructor <;> linarith only [hx,hw,hy,hz,ha,room]
  have hh : -(n.val:ℤ)<y j-x j ∧ y j-x j< n.val := by exact_mod_cast h
  change -((n.val * 2 : ℕ):ℤ)< 2 * (y j-x j) ∧ 2 * (y j-x j) ≤ ((n.val * 2 : ℕ):ℤ)
  omega

include H
/-- The size gate only cares about the *physical* region. It works on all
Ward supports as the cutoff is removed, including carried supports. There is
no UV threshold to pay for this geometrical fact. -/
lemma fits_volume (A : ℝ) : ∀ᶠ i : ℕ in atTop, ∀ (s : ℕ) (S : Finset Cover),
    SupportedPhysically Λ l s S (cabin A) → FullDistances (tips S) (Journey.side Y i s) := by
  have he : Tendsto (fun i:ℕ=> ((Journey.side Y i 0).val:ℝ)) atTop atTop:=
    tendsto_natCast_atTop_atTop.comp (goes Y H 0)
  filter_upwards [he.eventually (eventually_gt_atTop (4*A+2))] with i hi
  exact fun s S p=> no_alias Y i A hi s S p

omit H
lemma supports_union {Λ : Preparation} {l s : ℕ} {S T : Finset Cover} {V : Set RSpace}
    (p : SupportedPhysically Λ l s S V) (h : SupportedPhysically Λ l s T V) :
    SupportedPhysically Λ l s (S∪T) V := unionPrinted Λ l s S T _ p h

lemma distances_mono {S T : Finset Cover} {N : Side} (p : T ⊆ S) (h : FullDistances S N) :
    FullDistances T N := fun x hx y hy=> h x (p hx) y (p hy)

lemma distances_injective {S : Finset Cover} {N : Side} (p : FullDistances S N) :
    Hosp S N := by
  refine ⟨fun x a y b h=>?_⟩
  have he:=p x a y b
  rw [←h] at he
  have ht:=p x a x a
  rw [sub_self x] at ht
  exact (sub_eq_zero.mp (he.symm.trans ht)).symm

/-- Therefore the two detached parts cost even the exact separation gate used
by the transfer, on the physical torus, uniformly at all finer levels. -/
lemma also_separation {Λ : Preparation} {l : ℕ} {P Q : Finset Cover}
    (h : Detached Λ l P Q) {n : Side} (p : FullDistances (P∪Q) n) :
    ∀ x∈ Satin.region P n, ∀ y∈ Satin.region Q n,
      2*(Advance.nearZero (aliasLaw Λ)+Journey.distanceLaw l)<Lattice.separation x y:= by
  intro x hx y hy
  obtain ⟨x,a,rfl⟩:= Finset.mem_image.mp hx
  obtain ⟨y,b,rfl⟩:= Finset.mem_image.mp hy
  by_contra! k
  apply (Detached.act Λ l h) x a y b
  have he := p y (Finset.mem_union_right _ b) x (Finset.mem_union_left _ a)
  rw [←he,Lattice.box_test]
  have hg (j:Axis):= le_trans (component_le (wrap (More n) x - wrap (More n) y) j) k
  constructor <;> intro i <;> specialize hg i <;> omega

end YM.CF.Buffered.Afterglow.Tower.One
