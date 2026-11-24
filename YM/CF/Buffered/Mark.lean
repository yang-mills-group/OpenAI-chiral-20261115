import YM.CF.Buffered.Band
import YM.CF.Volume.Carrier

/-! # Chiral marks

Use the collected exterior algebra (`Fine`) as in the proof of gaugeM: no
config dependent presentation or monomial degrees need follow a mark up the
scales. The two fields are the links and the reconstructed links. Quantify
over them separately (when one evaluates, the reconstruction will be the
**same draw** for all insertions; at top they coincide on nonzero weight).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Buffered
open Function Fock NormedSpace SU Lat Lattice Finset Cube Spire MeasureTheory Branch Reflect Window Wilson Rush Peaks Scroll
open Phase Skye Pastry Tulip Dial Paige Push.SectorMeasure Scree RG
open Reed (Fine think)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
-- avoid `Op` diamond
attribute [local instance] opCStarAlgebra
section
variable {I : Type*} [LinearOrder I] [Fintype I] {s t : Finset I} {b : Bool}
lemma fine_neg {P : FC I} (p : Fine s t b P) : Fine s t b (-P) := by simpa using p.scale (-1)
lemma fine_rsmul (c : ℝ) {P : FC I} (p : Fine s t b P) : Fine s t b (c • P) := by simpa using p.scale c
lemma fine_integral {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ] {f : X → FC I} (p : ∀ᵐ x ∂μ, Fine s t b (f x)) : Fine s t b (∫ x, f x ∂μ) := by
  by_cases h : Integrable f μ
  · let Q : Submodule ℂ (FC I) :=
      { carrier := {A | Fine s t b A}
        zero_mem' := Fine.empty _
        smul_mem' := fun c x (p : Fine _ _ _ x) => p.scale c
        add_mem' := fun {x y} p q => Fine.add p q }
    let T := Q.restrictScalars ℝ
    exact T.convex.integral_mem T.closed_of_finiteDimensional (show ∀ᵐ x ∂μ, f x ∈ T from p) h
  rw [integral_undef h]; apply Fine.empty

-- Matter support expressed on kets with signed frames.
abbrev withinM (s : Finset I) (x : Ket I) := acts (cutM s) x = x
lemma within_test (s : Finset I) (x : Ket I) : withinM s x ↔ ∀ i, i ∉ s → x.ofLp i = 0 := by
  constructor
  · intro h i g; nth_rw 1 [← h]; rw [cut_apply,if_neg g]
  intro h; apply PiLp.ext; intro i; rw [cut_apply]; split; rfl; next v=> exact (h i v).symm
lemma within_basis (s : Finset I) (i : I) (h : i ∈ s) : withinM s (basisKet i) := by unfold withinM; rw [cut_basis,if_pos h]
lemma within_univ (x : Ket I) : withinM univ x := (within_test ..).mpr (by simp)
lemma within_compl {x : Ket I} : withinM sᶜ x ↔ acts (cutM s) x = 0 := by rw [withinM,dim_cut,act_sub,act_one]; simp
lemma fine_create (x : Ket I) (h : withinM s x) (v : withinM t x) : Fine s t true (create x) := by
  rw [create_def]; refine Fine.sumF _ _ fun i _=> ?_; by_cases p : i ∈ s; swap
  · rw [(within_test ..).mp h i p,zero_smul]; exact .empty _
  by_cases q : i ∈ t; swap
  · rw [(within_test ..).mp v i q,zero_smul]; exact .empty _
  rw [← show (think s).term i=put i from if_pos p]; exact (Fine.seed i q).scale _
lemma fine_remove (x : Ket I) (h : withinM sᶜ x) (v : withinM t x) : Fine s t true (Fock.remove x) := by
  rw [remove_def]; refine Fine.sumF _ _ fun i _=> ?_; by_cases p : i ∈ sᶜ; swap
  · rw [(within_test ..).mp h i p,star_zero,zero_smul]; exact .empty _
  by_cases q : i ∈ t; swap
  · rw [(within_test ..).mp v i q,star_zero,zero_smul]; exact .empty _
  exact (show Fine s t true (takeF i) from by
    have w :=Fine.seed (s:=s) i q; rw [show (think s).term i= -takeF i from if_neg (mem_compl.mp p)] at w; simpa using fine_neg w).scale _
end
variable {n : Side}
abbrev Fields (n : Side) := Pane n × Pane n
abbrev Mark (n : Side) := Fields n → FC (Single n)
def toMark (P : Evaluation n) : Mark n := fun V=> P V.1
def reflFields (i : Axis) (s : ℤ) (V : Fields n) : Fields n := Prod.map (fling i s n) (fling i s n) V
def reflMark (i : Axis) (s : ℤ) (P : Mark n) : Mark n := fun y=> theta (carR i s n) (P (reflFields i s y))
lemma reflEval (i : Axis) (s : ℤ) (P : Evaluation n) : toMark (Buffered.refl i s P) = reflMark i s (toMark P) := rfl
lemma reflFields_inv (i : Axis) (s : ℤ) : Involutive (reflFields (n:=n) i s) := fun _=> Prod.ext (fling_invol i s _) (fling_invol i s _)
lemma reflMark_cont (i : Axis) (s : ℤ) (P : Mark n) (h : Continuous P) : Continuous (reflMark i s P) :=
  (theta_cont _).comp (h.comp (Continuous.prodMap (fling_cont ..) (fling_cont ..)))
structure AtSupport (b : Bool) (S : Support (More n)) (P : Mark n) : Prop where
  env : Envelope P
  dep (x y : Fields n) : Agrees S x.1 y.1 → Agrees S x.2 y.2 → P x=P y
  allV (x : Fields n) : Fine (Tset n) (modesIn n S) b (P x)
namespace AtSupport
variable {b c : Bool} {S T : Support (More n)} {P Q : Mark n}
theorem mono (p : AtSupport b S P) (h : S ⊆ T) : AtSupport b T P :=
  ⟨p.env,fun _ _ u v=> p.dep _ _ (agrees_mono u h) (agrees_mono v h), fun x => Window.fine_enlarge (modes_monotone h) (p.allV x)⟩
lemma oneM (S : Support (More n)) : AtSupport false S 1 := ⟨Girt.rite_c _,fun _ _ _ _ => rfl, fun _=>Fine.one⟩
lemma mulM (p : AtSupport b S P) (q : AtSupport c S Q) : AtSupport (b.xor c) S (P*Q) := ⟨env_mult p.env q.env,fun _ _ u v=>congrArg₂ (α:=FC (Single n)) (β:=FC (Single n)) (·*·) (p.dep _ _ u v) (q.dep _ _ u v), fun i=> (p.allV i).grow (q.allV i)⟩
lemma addM (p : AtSupport b S P) (q : AtSupport b S Q) : AtSupport b S (P+Q) := ⟨Girt.kitE P Q (·+·) (by fun_prop) p.env q.env,fun _ _ u v=>congrArg₂ (α:=FC (Single n)) (β:=FC (Single n)) (·+·) (p.dep _ _ u v) (q.dep _ _ u v), fun i=> (p.allV i).add (q.allV i)⟩
lemma smulM (p : AtSupport b S P) (z : ℂ) : AtSupport b S (z • P) := ⟨Girt.kitE (fun _ : Fields n=>z) P (fun a b=> a • b) (by fun_prop) (Girt.rite_c _) p.env, fun _ _ u v=>congrArg (fun t:FC (Single n)=> z • t) (p.dep _ _ u v), fun i=> (p.allV i).scale _⟩
lemma zeroM : AtSupport b S (0 : Mark n) := ⟨Girt.rite_c _,fun _ _ _ _=> rfl, fun _=> Fine.empty _⟩
lemma refl (i : Axis) (s : ℤ) (p : AtSupport b S P) : AtSupport b (S.image ((plane i s).anon n)) (reflMark i s P) :=
  ⟨Girt.pole_w (fun V=> P (reflFields i s V)) (theta (carR i s n)) (theta_cont (carR i s n)) (Env.along p.env (Continuous.measurable (Continuous.prodMap (fling_cont (n:=n) i s) (fling_cont (n:=n) i s)))), fun x y u v => congrArg (theta (carR i s n)) (p.dep (reflFields i s x) (reflFields i s y) (fling_local i s _ u) (fling_local i s _ v)), fun _ => refl_fine i s _ _ _ (p.allV _)⟩
lemma refl_refl (i : Axis) (s : ℤ) (p : AtSupport b S P) : reflMark i s (reflMark i s P) = P := by
  funext x; simp only [reflMark,reflFields_inv i s x]; exact theta_twice _ (carR_square ..) (p.allV _).sector
lemma fromEval (F : Evaluation n) (p : Envelope F) (t : Lattice.LocalOn S F) (f : ∀ x,Fine (Tset n) (modesIn n S) b (F x)) : AtSupport b S (toMark F) := ⟨Env.along p measurable_fst, fun _ _ u _ => t _ _ u, fun _=> f _⟩
end AtSupport
end YM.CF.Buffered
