import Quarry.Trunk
import YM.SU5.Exchange.Stack.Manor
-- source API of agreement
import YM.CF.Buffered.Mark
-- pingS is decided by first-Pane inspection
import YM.CF.Chaff.Pulse

/-! # The real masked kernels of the (128) experiment, first Pane

Not a smooth Mark claim. Use full, discontinuous threshold cut. Use of arbitrary Ids
in the formula is licensed pointwise; even before discarding possible tag ties, support
& Loom equality for these short coupons. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet
open Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel
open Buffered
attribute [local instance] boreKSpace boreXN

variable {N : Side} {p : BudgetPoint} {K : Scree.Loom N} {X : SOp N} {o : Seat N}
variable {Y : Support (More N)} {a b d t : ℝ} {k q : ℕ}
local notation "Ω" => Single N

/-- Test on links the actual Loom expression for this truncated kernel, but only
when mask lights. No tag in the experiment. For all regulator worlds see `hatKernel_draw`. -/
def hatKernel (p : BudgetPoint) (K : Scree.Loom N) (Y : Sa N) (X : SOp N) :
    Pane N → Op (Single N) :=
  {v : Pane N | pingS p.threshold Y v}.indicator
    (fun v => X (profile (K (v, Classical.arbitrary _))))

/-- Relation that the matrix acts only on matter/spin/slot modes of this support. -/
def ClippedAt (Y : Sa N) (X : Op (Single N)) : Prop :=
  cutM (modesIn N Y) * X * cutM (modesIn N Y) = X

theorem within_inspect (Y : Sa N) : Y ⊆ inspected Y := subset_union_left

theorem kernelTape_mem (V : Sa N) (Y : Finset (Seat N))
    (u : o ∈ V) (h : V.card < k) (g : Grove (terr _) V) (q : ℕ)
    (hq : halo (k + q) {o} ⊆ Y) : halo q V ⊆ Y := by
  intro j l; obtain ⟨i, m, n⟩ := halo_spec.mp l
  have hi : separation o i < k := (g.lim _ u _ m).trans h
  exact hq (halo_spec.mpr ⟨o, mem_singleton_self _, (separation_triangle o i j).trans (by omega)⟩)

/-- Use strict ping clearance for every halo-spending link of the kernel; no threshold
assumption on more distant links. -/
theorem readableAt (H : Roof N t d q K) (ht : p.threshold ≤ t) (i : Orbit N)
    (V : Support (More N)) (g : halo q V ⊆ Y) (h : pingS p.threshold Y i.1) :
    Agrees V (K i) i.1 := by
  intro j x y; apply H.lamp
  have he : pingS t Y i.1 := fun b u => (h b u).trans_le ht
  refine Disjoint.mono_right ?_ (show Disjoint (flags t i.1) Y from (show Disjoint Y _ from ping_le he).symm)
  exact (Corona.halo_mono (show q ≤ q from le_rfl) (insert_subset x (singleton_subset_iff.mpr y))).trans g

theorem tape_clear {S : Sa N} {F : Raw (↥(Openc (More N) d)) (Single N)}
    (L : Suite (badge _) (bail N d) (bail N d) S 0 F) (x) : F x = 0 := by
  ext i j
  exact norm_le_zero_iff.mp ((L.expo i j).bounded x)

variable (A : Trunk o X k a b d)
variable (L : Roof N t d q K) (hp : p.threshold ≤ t) (hd : 0 < d)
    (size : halo (k+q) {o} ⊆ Y)

include A L hp hd size in
theorem Trunk.maskLink (x y : Orbit N) (v : pingS p.threshold Y x.1)
    (w : pingS p.threshold Y y.1) (h : Agrees Y x.1 y.1) :
    X (profile (K x)) = X (profile (K y)) := by
  obtain ⟨F,C,P,H,_,T⟩ := A.home
  rw [show X (profile (K x)) = _ from T (roller hd L x), show X (profile (K y)) = _ from T (roller hd L y)]
  apply sum_congr rfl; intro i _
  by_cases s : C i ≠ 0
  · obtain ⟨l,h'⟩ := H i s
    have ht : halo q i ⊆ Y := kernelTape_mem i Y l h' (f_then (P i) s) _ size
    have hz : Agrees i x.1 y.1 := agrees_mono h (Finset.coe_subset.mpr ((halo_subset q _).trans ht))
    apply pact_p hd L (P i); intro j t t'
    exact (readableAt L hp x i ht v j t t').trans
      ((hz j t t').trans (readableAt L hp y i ht w j t t').symm)
  have V : C i = 0 := not_not.mp s
  rw [tape_clear (F:=F i) (S:=i) (V ▸ P i) _, tape_clear (F:=F i) (S:=i) (V ▸ P i) _]

include A L hp hd size
lemma hatKernel_pass (x : Orbit N) (v : pingS p.threshold Y x.1) :
    hatKernel p K Y X x.1 = X (profile (K x)) := by
  rw [hatKernel, Set.indicator_of_mem (show _ ∈ _ from v)]
  exact A.maskLink L hp hd size (x.1, _) x v v (fun _ _ _ => rfl)
omit A L hp hd size
theorem hatKernel_closed (v : Pane N) (g : ¬pingS p.threshold Y v) :
    hatKernel p K Y X v = 0 := Set.indicator_of_notMem g _
include A L hp hd size
theorem hatKernel_draw (x : Orbit N) :
    hatKernel p K Y X x.1 = (pingMask p Y).indicator (fun y => X (profile (K y))) x := by
  by_cases f : pingS p.threshold Y x.1
  · exact (hatKernel_pass A L hp hd size x f).trans (Set.indicator_of_mem (show x ∈ pingMask p Y from f) (fun y => X (profile (K y)))).symm
  rw [hatKernel_closed x.1 f, Set.indicator_of_notMem (show x ∉ _ from f)]

theorem hatKernel_reads : LocalOn (↑(inspected Y)) (hatKernel p K Y X) := by
  intro i j g; have h := Chaff.fenceW Y g p.threshold
  by_cases w : pingS p.threshold Y i
  · unfold hatKernel
    rw [Set.indicator_of_mem (show _ ∈ _ from w), Set.indicator_of_mem (show _ ∈ _ from h.1 w)]
    exact A.maskLink L hp hd size (i,_) (j,_) w (h.1 w)
      (agrees_mono g (Finset.coe_subset.mpr (within_inspect Y)))
  rw [hatKernel_closed i w, hatKernel_closed j (mt h.mpr w)]

omit hp size
include A L hd
theorem Trunk.lampGauge (i : Orbit N) (g : Seat N → SU.E) :
    X (profile (K (Lattice.gauge g i.1, threadG g i.2))) =
      twist (tradew N g) (X (profile (K i))) := by
  obtain ⟨F, C, P, _, _, T⟩ := A.home
  let r := roller hd L i
  rw [show X (profile (K (Lattice.gauge g i.1, threadG g i.2))) = _ from T (roller hd L (Lattice.gauge g i.1, threadG g i.2)),
      show X (profile (K i)) = _ from T r, map_sum]
  apply sum_congr rfl; intro j _
  rw [roll_g hd L g i, Inter.frame (P j).toTicket.frame, twist_formula]
  rfl

include hp size
theorem hatKernel_gauge (i : Pane N) (g : Seat N → SU.E) :
    hatKernel p K Y X (Lattice.gauge g i) = twist (tradew N g) (hatKernel p K Y X i) := by
  let u : Orbit N := (i, Classical.arbitrary _)
  have e := pingB (e:=p.threshold) (X:=Y) i g
  by_cases H : pingS p.threshold Y i
  · rw [show hatKernel p K Y X i = _ from hatKernel_pass A L hp hd size u H,
        show hatKernel p K Y X _ = _ from hatKernel_pass A L hp hd size
          (Lattice.gauge g u.1, threadG g u.2) (e.mpr H)]
    exact A.lampGauge L hd u g
  rw [hatKernel_closed i H, hatKernel_closed (Lattice.gauge g i) (mt e.mp H), map_zero]

omit hp size
include A L hd
theorem Trunk.modes (i : Orbit N) {S : Sa N} (size : halo k {o} ⊆ S) :
    ClippedAt S (X (profile (K i))) := by
  unfold ClippedAt
  obtain ⟨F, C, P, H, _, T⟩ := A.home
  let W := roller hd L i
  rw [show X (profile (K i)) = _ from T W, mul_sum, sum_mul]
  apply sum_congr rfl; intro U _
  ext s t
  rw [cutM, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases p : F U W s t = 0
  · rw [p]; simp
  have hx : C U s t ≠ 0 := ne_of_gt ((norm_pos_iff.mpr p).trans_le ((P U).expo s t |>.bounded W))
  have h₀ : C U ≠ 0 := fun z => hx (by rw [z]; rfl)
  obtain ⟨_, u, v⟩ := ((P U).expo s t).triggered hx
  obtain ⟨j,k'⟩ := H U h₀
  have hi : U ⊆ S := fun x l => size (halo_spec.mpr
    ⟨o, mem_singleton_self _, show separation o x ≤ k from (((f_then (P U) h₀).lim _ j _ l).trans k').le⟩)
  rw [if_pos ((modes_at ..).2 (hi u)), if_pos ((modes_at ..).2 (hi v)), one_mul, mul_one]

include hp size
theorem hatKernel_clips (i : Pane N) {S : Sa N} (h : halo k {o} ⊆ S) :
    ClippedAt S (hatKernel p K Y X i) := by
  unfold hatKernel
  by_cases p' : pingS p.threshold Y i
  · rw [Set.indicator_of_mem (show _ ∈ _ from p')]
    exact A.modes L hd (i, _) h
  rw [Set.indicator_of_notMem (show _ ∉ _ from p')]
  simp only [ClippedAt, mul_zero, zero_mul]

omit hp size
include A L hd
theorem hatKernel_boundOp (h : 0 ≤ a) (u : Pane N) : ‖hatKernel p K Y X u‖ ≤ b := by
  by_cases w : pingS p.threshold Y u
  · unfold hatKernel; rw [Set.indicator_of_mem (show _ ∈ _ from w)]
    exact norm_U A.pay h (roller hd L (u, _))
  rw [hatKernel_closed u w, norm_zero]; exact soakCostNN A.pay

theorem hatKernel_borel (h : 0 ≤ a) : Envelope (hatKernel p K Y X) := by
  refine ⟨?_, b, hatKernel_boundOp A L hd h⟩
  obtain ⟨F,C,P,H,U,T⟩ := A.home
  let r (v : Pane N) := roller hd L (v, Classical.arbitrary _)
  have V : Measurable r := (roll_m hd L).comp (measurable_id.prodMk measurable_const)
  apply Measurable.indicator _ ping_o.measurableSet
  change Measurable (fun v => X (r v).val)
  simp_rw [T]
  exact Finset.measurable_fun_sum _ (fun i _ => (P i).toTicket.cont.measurable.comp V)
end YM.CF.Swell
