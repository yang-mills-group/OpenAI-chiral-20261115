import Anomaly.TrunkShift
import YM.CF.Sour.Rate
import YM.CF.Chaff.Pulse
import YM.CF.Buffered.Mark
import YM.CF.Buffered.Probes
import YM.SU5.Exchange.Pilot.Marquet
/-!
Use the pieces of the actual data under `Roof`, at the strict physical mask
(including inspection support, not trying to pay derivatives across the
boundary of the mask). No auxiliary tag or second configuration in this
instrument. It agrees at ALL orbit valuations with the masked consultation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Swell
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Skye Jet Scroll Finset
open RG MeasureTheory Salt Metric Drapes Tulip Lat Branch Cube Tenant Rill
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Moto Oath Font Haro Spire Dial
variable {N : Side}
local notation "Ω" => Single N
attribute [local instance] Rill.boreKSpace Rill.boreXN
-- agree on the project's measurable space on FC where actually spent
open Buffered

theorem footprintGeodesic {S : Support (More N)} {o : Seat N} {k : ℕ}
    (h : Grove (terr (More N)) S) (p : o∈S) (t : S.card ≤ k) :
    S⊆halo k {o} := by
  exact fun y q => halo_spec.mpr ⟨_,mem_singleton_self _,(h.lim o p y q).le.trans t⟩

theorem Soak.siteCost {o : Seat N} {X : SOp N} {a b d : ℝ} (t : Soak o X a b d)
    (ha : 0 ≤ a) (x : Openc (More N) d) :
    (∑ i : Ω, ∑ j : Ω, ‖X x.val i j‖) ≤ b := by
  obtain ⟨F,C,p,_,v,g⟩ := t
  rw [g]
  simp_rw [Matrix.sum_apply]
  refine le_trans (sum_le_sum (fun i _=> sum_le_sum (fun j _=> (norm_sum_le ..).trans (sum_le_sum (fun S (_:S∈(univ:Finset (Sa N)))=> ((p S).expo i j|>.bounded x).trans
    (le_mul_of_one_le_left ((p S).nonn i j) (rent_one ha S))))))) ?_
  simp_rw [sum_comm (f:=fun j (S:Sa N)=> rent a S * C S _ j)]; rw [sum_comm]; simpa only [ledgerV,mul_sum] using v

lemma maskAware {b : BudgetPoint} {r k : ℕ} {t d a v : ℝ} {K : Scree.Loom N}
    {F : SOp N} {o : Seat N} (h : Roof N t d r K) (l : 0<d) (g : Trunk o F k a v d)
    (p : b.threshold ≤ t) (w : k+r+10 ≤ b.B)
    (x y : Orbit N) (hx : pingS b.threshold (halo b.B {o}) x.1)
    (hy : pingS b.threshold (halo b.B {o}) y.1) (u : Agrees (halo k {o}) x.1 y.1) :
    F (profile (K x)) = F (profile (K y)) := by
  let D : Vow.Aura N := ⟨halo b.B {o},o,halo_subset b.B _ (mem_singleton_self o)⟩
  obtain ⟨T,C,f,z,_,s⟩ := g.home
  rw [show F (profile (K x))=_ from s (roller l h x),show F (profile (K y))=_ from s (roller l h y)]
  apply sum_congr rfl; intro S _
  by_cases Q : C S = 0
  · have hz (U : Openc (More N) d) : T S U=0 := by
      ext i j; exact norm_le_zero_iff.mp (((f S).expo i j |>.bounded U).trans_eq (by rw [Q]; rfl))
    rw [hz,hz]
  have hg := footprintGeodesic (f_then (f S) Q) (z S Q).1 (z S Q).2.le
  have hf : halo (r+10) S ⊆ D.val := by
    intro i hi; obtain ⟨q,t,V⟩ := halo_spec.mp hi
    obtain ⟨_,u,e⟩ := halo_spec.mp (hg t)
    exact halo_spec.mpr ⟨_,u,(separation_triangle _ q _).trans (by omega)⟩
  have H (X : Orbit N) (u : pingS b.threshold (halo b.B {o}) X.1) :
      Agrees S (K X) X.1 := by
    have hh : X.1 ∈ σX b D ∅ := ⟨by rw [sdiff_empty]; exact u,empty_subset _⟩
    exact fun i hi _ => fern h p S hf X.1 hh i hi rfl X.2
  exact pact_p l h (f S) x y fun i hi ht=> ((H x hx) i hi ht).trans
    ((u i (hg hi) (hg ht)).trans ((H y hy) i hi ht).symm)

lemma trunkSupport {d a v : ℝ} {F : SOp N} {o : Seat N} {k:ℕ}
    (g : Trunk o F k a v d) (x : Openc (More N) d) :
    let L := cutM (modesIn N (halo k {o}))
    L * F x.val * L = F x.val := by
  obtain ⟨T,C,h,z,t,s⟩ := g.home
  rw [s]
  dsimp only
  rw [mul_sum,sum_mul]
  apply sum_congr rfl
  intro S _
  ext i j
  rw [cutM,Matrix.mul_diagonal,Matrix.diagonal_mul]; simp only [modes_at]
  by_cases hp : C S i j=0
  · rw [show T S x i j=0 from norm_le_zero_iff.mp (((h S).expo i j|>.bounded x).trans_eq hp),mul_zero,zero_mul]
  have hC : C S≠0 := by intro u; rw [u] at hp; exact hp rfl
  have hg := ((h S).expo i j).triggered hp
  have H := footprintGeodesic hg.1 (z S hC).1 (z S hC).2.le
  rw [if_pos (H (show node i.1.1 ∈ S from hg.2.1)), if_pos (H (show node j.1.1 ∈ S from hg.2.2)), mul_one,one_mul]

lemma Trunk.rev {d a v : ℝ} {F : SOp N} {o : Seat N} {k r:ℕ} {t:ℝ} {K:Scree.Loom N}
    (g : Trunk o F k a v d) (h : Roof N t d r K) (l : 0<d) (y : Orbit N) (C : Seat N → SU.E) :
    F (profile (K (Lattice.gauge C y.1, threadG C y.2)))= twist (tradew N C) (F (profile (K y))) := by
  obtain ⟨T,Z,v0,_,_,p⟩ := g.home
  rw [show F (profile (K y)) = _ from p (roller l h y),
    show F (profile (K (Lattice.gauge C y.1, threadG C y.2)))= _ from p (roller l h _),map_sum]
  apply sum_congr rfl; intro i _
  rw [roll_g, (v0 i).toTicket.frame.frame]
  rfl

/-- Rooted shuttered matrix: at the *actual* tagless probe (we still pay
some supports on the support grammar with its tag index). -/
def pinMatrix (b : BudgetPoint) (K : Scree.Loom N) (o : Seat N) (F : SOp N) : Pane N → Op Ω :=
  Set.indicator {U : Pane N|pingS b.threshold (halo b.B {o}) U} (fun U : Pane N=> F (profile (K (U,Classical.arbitrary _))))

variable {b : BudgetPoint} {r k : ℕ} {t d a v : ℝ} {K : Scree.Loom N} {F : SOp N} {o : Seat N}
    (h : Roof N t d r K) (l : 0<d) (g : Trunk o F k a v d) (p : b.threshold ≤ t) (w : k+r+10 ≤ b.B)
include h l g p w

lemma pinMatrix_active (x : Orbit N) (u : pingS b.threshold (halo b.B {o}) x.1) :
    pinMatrix b K o F x.1 = F (profile (K x)) := by
  rw [pinMatrix,Set.indicator_of_mem (show x.1∈_ from u)]
  exact maskAware h l g p w (x.1,_) x u u fun _ _ _=>rfl

lemma pinMatrix_eval (x : Orbit N) : pinMatrix b K o F x.1=
    (pingMask b (halo b.B {o})).indicator (fun x:Orbit N=> F (profile (K x))) x := by
  by_cases t:x∈pingMask b (halo b.B {o})
  · rw [Set.indicator_of_mem t]; exact pinMatrix_active h l g p w x t
  rw [Set.indicator_of_notMem t,pinMatrix]
  exact Set.indicator_of_notMem (show x.1 ∉ {U : Pane N | pingS b.threshold (halo b.B {o}) U} from t) _

lemma pinMatrix_support (x : Orbit N) :
    let L := cutM (modesIn N (halo k {o}))
    L * pinMatrix b K o F x.1 * L = pinMatrix b K o F x.1 := by
  intro L
  rw [pinMatrix_eval h l g p w]
  by_cases t:x∈ pingMask b (halo b.B {o})
  · rw [Set.indicator_of_mem t]; exact trunkSupport g (roller l h x)
  rw [Set.indicator_of_notMem t,mul_zero,zero_mul]

lemma pinMatrix_gauge (x : Orbit N) (C : Seat N→ SU.E) :
    pinMatrix b K o F (Lattice.gauge C x.1) = twist (tradew N C) (pinMatrix b K o F x.1) := by
  let X : Orbit N := (Lattice.gauge C x.1, threadG C x.2)
  by_cases q:x∈pingMask b (halo b.B {o})
  · rw [show Lattice.gauge C x.1=X.1 from rfl, pinMatrix_active h l g p w X ((pingB x.1 C).mpr q),pinMatrix_active h l g p w x q]; exact g.rev h l x C
  change pinMatrix b K o F X.1 = twist (tradew N C) (pinMatrix b K o F x.1)
  have hu:X∉ pingMask b (halo b.B {o}) := mt (pingB x.1 C).mp q
  rw [pinMatrix_eval h l g p w X,pinMatrix_eval h l g p w x, Set.indicator_of_notMem q,Set.indicator_of_notMem hu,map_zero]

lemma pinMatrix_local : LocalOn (inspected (halo b.B {o})) (pinMatrix b K o F) := by
  intro x y H
  let X : Orbit N := (x,Classical.arbitrary _)
  let Y : Orbit N := (y,Classical.arbitrary _)
  have hv := Chaff.fenceW _ H b.threshold
  change pinMatrix b K o F X.1=pinMatrix b K o F Y.1
  rw [pinMatrix_eval h l g p w,pinMatrix_eval h l g p w]
  by_cases Q:X∈pingMask b (halo b.B {o})
  · have hz:Y∈pingMask b (halo b.B {o}) := hv.mp Q
    rw [Set.indicator_of_mem Q,Set.indicator_of_mem hz]; apply maskAware h l g p w X Y Q hz
    have he:halo k {o} ⊆ inspected (halo b.B {o}) := (Corona.halo_mono (show k≤ b.B by omega) le_rfl).trans subset_union_left
    exact agrees_mono H (Finset.coe_subset.mpr he)
  rw [Set.indicator_of_notMem Q,Set.indicator_of_notMem (show Y∉_ from mt hv.mpr Q)]

lemma pinMatrix_price (x : Orbit N) (ha : 0 ≤ a) : (∑ i:Ω,∑ j:Ω, ‖pinMatrix b K o F x.1 i j‖) ≤ v := by
  rw [pinMatrix_eval h l g p w x]
  by_cases u:x∈pingMask b (halo b.B {o})
  · rw [Set.indicator_of_mem u]; exact Soak.siteCost g.pay ha (roller l h x)
  rw [Set.indicator_of_notMem u]; simpa using soakCostNN g.pay

lemma pinMatrix_env (ha : 0 ≤ a) : Envelope (pinMatrix b K o F) := by
  have eV(x:Pane N):= pinMatrix_price h l g p w (x,Classical.arbitrary _) ha
  refine ⟨?_,v,?_⟩
  · obtain ⟨T,C,f,_,_,H⟩ := g.home
    unfold pinMatrix
    have hs (x:Pane N) : F (profile (K (x,Classical.arbitrary _))) = ∑ i:Sa N,T i (roller l h (x,Classical.arbitrary _)) := H (roller l h (x, Classical.arbitrary _))
    simp_rw [hs]
    apply Measurable.indicator _ ping_o.measurableSet
    apply Finset.measurable_fun_sum; intro i pi
    exact (((f i).toTicket.cont).measurable.comp (roll_m l h)).comp (measurable_id.prodMk measurable_const)
  intro x
  let X:= pinMatrix b K o F x
  let Z(i j:Ω):= ‖X i j‖
  have hx: (∑ i:Ω,∑ j:Ω,Z i j) ≤ v:= eV x
  refine schur Z X v (soakCostNN g.pay) (fun _ _=> le_rfl) ?_ ?_
  · exact fun i=> (single_le_sum (f:=fun i:Ω=>∑ j:Ω,Z i j) (fun i _=> sum_nonneg (fun _ _=> norm_nonneg _)) (mem_univ i)).trans hx
  rw [sum_comm] at hx
  exact fun j=> (single_le_sum (f:=fun j:Ω=>∑ i:Ω,Z i j) (fun i _=> sum_nonneg (fun _ _=> norm_nonneg _)) (mem_univ j)).trans hx
end YM.CF.Swell
