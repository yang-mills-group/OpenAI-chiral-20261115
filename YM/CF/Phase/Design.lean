import YM.CF.Cubes.Time
import YM.CF.Fock.Track

/-! Parameters fixed *before* volume and gauge background. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Phase
open Cube Lat Lattice SU Fock Finset
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace Topology
attribute [local instance] opCStarAlgebra

def goal := compressible.choose
lemma goal_pos : 0<goal := compressible.choose_spec.1
def Room (B : Side) (e : ℝ) : Prop := 0≤e ∧ 256*e ≤ 1/60 ∧ enoughV B e (goal/2)
lemma all_room : ∃ o : ℕ, ∀ (B : Side), o≤B.val → ∃ e:ℝ, 0<e ∧ ∀ k:ℝ, 0≤k → k≤e → Room B k := by
  obtain ⟨o,H⟩ := scalable (goal/2) (half_pos goal_pos)
  refine ⟨o,?_⟩; intro B h; obtain ⟨e,g,h⟩ := H B h; refine ⟨min e (1/15360),lt_min g (by norm_num),?_⟩
  intro k hx hk; refine ⟨hx,?_,h k (hk.trans (min_le_left ..))⟩; have he := hk.trans (min_le_right ..); linarith

abbrev Part (m B : Side) := Site (CSide m B)
abbrev Skin (m B : Side) := Bkg (Domain m B)
abbrev Mind (m B : Side) := Model (CSide m B)
variable {m B : Side}

def grain (m B : Side) (U : Skin m B) (s : ArrayF m) (q : Sq) := paintV m B U s q ∘ node (N:=CSide m B)
def lens (m B : Side) (cut : Part m B) (U : Skin m B) : Op (Mind m B) := occP cut (links U)
def bow (m B : Side) (U : Skin m B) (s : ArrayF m) (q : Sq) := Cfield (grain m B U s q)
abbrev Zone := Finset Row
def zone (r : Zone) := {q : Sq| prob q ∧ ∀ i∉r, q i=0}
section
variable (c : Part m B) {e : ℝ} {U : Skin m B}
variable (b : Room B e) (h : Guard U e)
lemma plaq_lens (b : Room B e) (h : Guard U e) : PlaqBound matter (links U) (1/60) :=
  ((h.children b.1).shrink b.2.1).2
include b h
lemma lensP : IsStarProjection (lens m B c U) := occProj _ _ (plaq_lens b h)
omit h in
lemma lens_cont : ContinuousOn (fun U:Skin m B=>lens m B c U) {U | Guard U e} :=
  (projector_cont matter c matter_cont).comp (links_cont (N:=CSide m B)).continuousOn (fun _ g=>plaq_lens b g) -- remove h
lemma lens_g (g : Site (Domain m B) → E) : lens m B c (gauge g U)=twist (conjG matter (g ∘ node)) (lens m B c U) := by
  unfold lens occP; rw [links_g, twist_projection matter (g ∘ node) (links U) c (plaq_lens b h)] -- specify N
variable {s : ArrayF m} {r : Zone} {q : Sq} (V : Verified m B margin U s r) (x : q∈zone r)
include V x
lemma grain_unit : ∀ y, ‖grain m B U s q y‖=1 := fun j => paint_unit (U:=U) x.1 b.1 h V x.2 b.2.2 (node j)
lemma grain_j : (links U,grain m B U s q) ∈ Joint _ goal :=
  ⟨plaq_lens b h,grain_unit b h V x, by
    have he := Guard.descend (paint_slow x.1 b.1 h V x.2 b.2.2); rw [show 2*(goal/2)=goal by ring] at he; exact he⟩
def Valid (P C : Op (Mind m B)) : Prop := C ∈ unitary _ ∧ Cᵀ= -C ∧ ‖P*C-C*cc P‖≤1/3
lemma bow_val : Valid (m:=m) (B:=B) (lens m B c U) (bow m B U s q) := by
  have j := grain_j b h V x
  have hq := grain_unit b h V x
  refine ⟨C_unit _ hq,C_skew _ hq,?_⟩
  exact compressible.choose_spec.2 _ c _ _ j.1 hq j.2.2
lemma bow_ok : ‖(stage (lens m B c U) (bow m B U s q))⁻¹‖≤2 ∧
    IsUnit (stage (lens m B c U) (bow m B U s q)) := by
  let P := lens m B c U
  let C := bow m B U s q
  obtain ⟨p,e,q⟩ := bow_val c b h V x
  have ht : ‖stage P C-C‖≤1/3 := by rw [stage_gap (lensP c b h)]; exact q
  exact (inv_close_le (A:=stage P C) ⟨C,p⟩ ht).symm
lemma bow_full : filled (lens m B c U) (bow m B U s q)≠0 := by
  let P := lens m B c U
  let C := bow m B U s q
  obtain ⟨p,e,q⟩ := bow_val c b h V x
  exact nonemptyFill P C (lensP c b h) e (nonsingSmall (P:=P) ⟨C,p⟩ (q.trans_lt (by norm_num)))
lemma bow_at : ContinuousAt (fun t : Skin m B × ArrayF m × Sq=> bow m B t.1 t.2.1 t.2.2) (U,s,q) := by
  let f := fun t : Skin m B×ArrayF m×Sq=> grain m B t.1 t.2.1 t.2.2
  have hf := paintV_at x.1 b.1 h V x.2 b.2.2
  have ht : ContinuousAt f (U,s,q) := continuousAt_pi.mpr fun i=>continuousAt_pi.mp hf (node i)
  change ContinuousAt (Cfield ∘ f) _
  exact C_cont.continuousAt.comp ht
omit b h V x in
lemma bow_g (g : Site (Domain m B) → E) : bow m B (gauge g U) (onF g s) q=congrC (conjG matter (g ∘ node)) (bow m B U s q) := by
  unfold bow grain; rw [paint_g]; exact C_gauge ..
end
end YM.CF.Phase
