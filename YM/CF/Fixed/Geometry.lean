import YM.CF.Scroll.Verge
import YM.Wilson.Symmetry

/-!
Geometry convention for local probes on the FiniteGaugeData theory. `i` can in particular be
`YM.timeAxis`; cut through **gauge sites** with i-coordinate 0. `x` and `U`
denote, respectively, a site on the fermion torus and a config on the doubled
gauge torus. See `Reflect/{Edges,Center}` for related geometry for the different,
auxiliary, RP regulator. Here we work with the same anticut as `Ups`.
-/

set_option autoImplicit false
noncomputable section

namespace YM.CF.Fixed
open Function Fock NormedSpace SU Lat Lattice Cube Finset Scroll MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
attribute [local instance] opCStarAlgebra

variable (N : Side) (i : Axis)

/-- Gauge reflection about the i-coordinate-origin plane on the doubled torus. -/
abbrev reflConfig (U : Bkg (More N)) := pull (Signed.mirror i) 0 U

abbrev reflShape : Shape := ⟨Signed.mirror i, 0⟩

/-- Pull on the matter torus, including the shift due to reflection of the node.
Indices on higher UV levels have the same convention. -/
abbrev partnerSite (x : Site N) := Shape.mills (reflShape i) N x

/-- The mask argument of local nets is a finite set of vertices on the gauge lattice. -/
def reflRegion (X : Support (More N)) : Support (More N) := X.image ((Signed.mirror i).act)

lemma square_mirror : Signed.mirror i * Signed.mirror i = 1 := by
  nth_rw 1 [← Signed.mirror_inv i]
  exact inv_mul_cancel _

lemma square_reflConfig (U : Bkg (More N)) :
    reflConfig N i (reflConfig N i U)=U := by
  rw [reflConfig,reflConfig,pull_pull,square_mirror]
  simp [affine]

lemma mem_reflRegion (X : Support (More N)) (x : Site (More N)) :
    x ∈ reflRegion N i X ↔ (Signed.mirror i).act x ∈ X := by
  have ht (x : Site (More N)) : (Signed.mirror i).act ((Signed.mirror i).act x)=x :=
    (Signed.mirror i).act_inv _
  rw [reflRegion,mem_image]
  constructor
  · rintro ⟨x,hx,rfl⟩; rwa [ht]
  · intro h
    exact ⟨_,h,ht x⟩

lemma node_partner (x : Site N) : node (partnerSite N i x)=(Signed.mirror i).act (node x) := by
  simpa only [partnerSite, Shape.anon, reflShape, smul_zero, map_zero, affine, add_zero] using
    Shape.nodex (reflShape i) x

-- On the cover: time coordinate n -> -1 - n; this calculation also determines
-- the sign of the lift to antiperiodic fermions.
lemma mirror_flee (x : Cover) :
    (reflShape i).flee x = (Signed.mirror i).act x - step i := by
  have he := Shape.mote (reflShape i) x
  apply nsmul_right_injective (M:=Cover) (show (2:ℕ)≠0 by decide)
  have ht : (Signed.mirror i).act (1:Cover) = 1-2 • step i := by
    ext j
    by_cases hj:i=j <;> simp [Signed.mirror, Signed.act, hj, Eq.comm (a:=j) (b:=i)]
  unfold Shape.motion reflShape at he
  simp only [Signed.act_add, two_smul, ht, smul_zero, add_zero] at he
  change (2:ℕ) • _ = (2:ℕ) • _
  unfold reflShape; rw [nsmul_sub]; linear_combination (norm:=abel) -he

lemma square_partnerSite (x : Site N) : partnerSite N i (partnerSite N i x)=x := by
  apply Tenant.needle
  rw [node_partner, node_partner]
  exact (Signed.mirror i).act_inv _

lemma reflConfig_cont : Continuous (reflConfig N i) := Wilson.continuous_pull ..

lemma reflConfig_preserves : MeasurePreserving (reflConfig N i) (Wilson.prior SU.group (More N))
    (Wilson.prior SU.group (More N)):= Wilson.prior_pull ..

abbrev reflectedGauge (g : Site (More N) → SU.E) : Site (More N) → SU.E :=
  fun x => g ((Signed.mirror i).act x)

lemma reflConfig_gauge (g : Site (More N) → SU.E) (U : Bkg (More N)) :
    reflConfig N i (Lattice.gauge g U) = Lattice.gauge (reflectedGauge N i g) (reflConfig N i U) := by
  funext e
  let s:=Signed.mirror i
  change ((posDir e.2).rotate s).read (Lattice.gauge g U) _ = _
  rw [Lattice.Step.gauge_read]
  unfold Lattice.gauge reflectedGauge reflConfig affine Lattice.pull
  rw [add_zero, Lattice.Step.vec_rotate, Lattice.Step.vec_pos, Signed.act_add]
  simp only [affine,add_zero]; rfl

-- Proof as for `YM.Push.Local.agrees_pull`. Transport **all endpoints**; no
-- single-anchor assumption.
lemma reflConfig_agrees (U V : Bkg (More N)) (X : Support (More N))
    (h : Agrees (reflRegion N i X) U V) :
    Agrees X (reflConfig N i U) (reflConfig N i V) := by
  intro e a b
  let s := Signed.mirror i
  let x := s.act e.1
  let R:= reflRegion N i X
  have ha : x ∈ R := mem_image_of_mem _ a
  have hb : x + ((posDir e.2).rotate s).vec ∈ R := by
    rw [Lattice.Step.vec_rotate,Lattice.Step.vec_pos]
    unfold x; rw [← s.act_add]
    exact mem_image_of_mem _ b
  change ((posDir e.2).rotate s).read _ _ = ((posDir e.2).rotate s).read _ _
  cases hQ : ((posDir e.2).rotate s) with | mk j g =>
  rw [hQ] at hb
  simp only [affine,add_zero]
  cases g
  · exact h (x,j) ha hb
  have he : x-step j ∈ R := by simpa only [show (⟨j,true⟩: Lattice.Step) = negDir j from rfl,
      Lattice.Step.vec_neg,sub_eq_add_neg] using hb
  exact congr_arg Inv.inv (h (x - step j,j) he (by change (x-step j+step j) ∈ R; rwa [sub_add_cancel]))

end YM.CF.Fixed
