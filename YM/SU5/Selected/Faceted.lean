import VerifiedSatinGroundInteraction
import YM.SU5.FiniteGaugeData.Signal.Polling
import YM.SU5.Selected.Generations
/-! # Faceted -- retaining interaction on true curved test locations in this selection

Curvature at *chosen fixed observing level*. Arbitrarily small but fixed threshold once chosen.
No changing recipe during estimates for finer presentations.
Do not need a different-history curvature price or its assumptions (e.g. `Signal.Parachute` concerns
other history records). We will reuse `Showcasing.displacement`: pure finite Side city fact (no
history assumptions), in this extension of its DCT application. Use saturating *continuous* not smooth weight.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6500
set_option maxHeartbeats 400000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Selected
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock Vacancy
open Buffered.Reliance Buffered.Reliance.ShortWave
open CF.Pannier.Chancel
variable {k n : ℕ} {J : Calibration} {s : ℕ} (b : Fin k → Cover)
  (L : Finset (Face ℤ)) (S T : Finset Cover) (t : ℝ)
local notation "γ" v:max f:max => SU.group.chord (faceValue v f)
def claywash (g : Finset (Face ℤ)) (t : ℝ) (V : LinksC) : ℝ :=
  ∏ i∈g, max 0 (min 1 ((γ V i-t)/t))
lemma claywash_cont : Continuous (claywash L t) := by
  apply continuous_finsetProd
  intro i _; exact continuous_const.max (continuous_const.min (((SU.group.continuous_chord.comp (continuous_travel _ _)).sub continuous_const).div_const _))
lemma clay_nonneg (x : LinksC) : 0≤ claywash L t x := by unfold claywash; exact Finset.prod_nonneg fun i _=> le_max_left ..
lemma clay_inside (x : LinksC) : claywash L t x ≤1 := by
  unfold claywash; refine Finset.prod_le_one ?_ ?_
  · exact fun i _=> le_max_left ..
  exact fun i _=> max_le zero_le_one (min_le_left ..)
lemma clay_absent (x : LinksC) {p : Face ℤ} (h : p∈ L) (q : 0 < t) (v : SU.group.chord (faceValue x p) ≤ t) : claywash L t x=0 := by
  apply Finset.prod_eq_zero h
  have he := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr v) q.le
  exact max_eq_left ((min_le_right ..).trans he)
lemma clay_some (x : LinksC) (q : 0<t) (r : ∀ i∈L,2*t ≤ SU.group.chord (faceValue x i)) : claywash L t x=1 := by
  unfold claywash; apply Finset.prod_eq_one; intro i hi
  have ht : 1≤ (SU.group.chord (faceValue x i)-t)/t:= by rw [le_div_iff₀ q]; linarith only [r i hi]
  rw [min_eq_left ht,max_eq_right zero_le_one]
lemma clay_agrees (p : restsOn L S) : ∀ (x y : LinksC), Agrees S x y→claywash L t x=claywash L t y:= by
  intro x y v; unfold claywash; apply Finset.prod_congr rfl; intro i w
  rw [show faceValue x i=faceValue y i from ?_]; apply travel_local i.1 (square i.2.val.1 i.2.val.2) x y
  exact fun k v' t=> v k (p i w (List.mem_toFinset.mpr v')) (p i w (List.mem_toFinset.mpr t))
def tintMark (J : Calibration) : Family J := Buffered.scalar J ((Complex.ofReal ∘ claywash L t) ∘ Prod.fst)
lemma tint_price (J : Calibration) (p : restsOn L S) : InTest J false S false (tintMark L t J) :=
  InTest.seed (Coeff.fromC _ _ (Complex.continuous_ofReal.comp (claywash_cont L t)) (fun i j h=> congrArg Complex.ofReal (clay_agrees L S t p i j h)))
lemma tint_here (J : Calibration) (m : Side) (x : Fields (J.c m)) : tintMark L t J m x=(↑(claywash L t (onC _ x.1)):ℂ) • (1:FC _) := rfl
lemma tint_sing (J : Calibration) : CovCover J (tintMark L t J):=by
  intro n u x; change tintMark L t J n _=twist _ _; rw [tint_here,tint_here]; change ((claywash L t (onC _ (Lattice.gauge u x.1)):ℂ) • (1:FC _)) = _; simp_rw [claywash,tile_face,face_gauge,Gauge.chord_conj]
  rw [twist_scalar,map_one]
variable {b T} {m : Side} {W : Window.Family} {f : Family J}
lemma fil_larger (p : S⊆ T) : Filigree J W b S ≤ Filigree J W b T:=by
  have he {u}: Lode J u b S ≤ Lode J u b T:=Submodule.span_mono (fun x v=>by
     obtain ⟨i,j,k,v⟩:= v; exact ⟨i,j,k,rows p v⟩)
  refine Submodule.span_mono (fun x v=>?_); obtain ⟨x,w,h,t,u⟩:=v; exact ⟨x,w,he h,t.mono p,u⟩
where
 rows {f : Family J} {L u} (p : S⊆ T) (l : CRow J u b S L f) : CRow J u b T L f:=by
  induction l with
  | gave=> exact .gave
  | pair i j c d f g u v a b h t x l ih=>exact .pair i j c d f g u v a b (p h) (p t) x ih
  | zip=>exact .zip
  | glaze _ _ ih=>exact .glaze _ ih
  | fuse _ _ a b=>exact .fuse a b
lemma fil_tinted (p : restsOn L S) (x : f∈ Filigree J W b S) : tintMark L t J*f∈ Filigree J W b S:=by
  have q:=clay_agrees L S t p; let X := Filigree J W b S
  induction x using Submodule.span_induction with
  | mem x u=>
     obtain ⟨x,z,r,e,rfl⟩:= u; obtain ⟨f,h,rfl⟩:= e.narrow rfl
     let g := Complex.ofReal ∘ claywash L t; let d := g*f
     refine Submodule.subset_span ?_; refine ⟨x,d ∘ Prod.fst,r,Coeff.fromC _ _ ((Complex.continuous_ofReal.comp (claywash_cont L t)).mul h) ?_,?_⟩
     · intro a b v; exact congrArg₂ (·*·) (congrArg Complex.ofReal (q a b v)) (e.locus (a,1) (b,1) v (fun _ _ _=>rfl))
     funext n i; let F : LinksC:= onC _ i.1; change (g F • (1:FC (Single (J.c n)))) * ((f F • (1:FC (Single (J.c n)))) * x n i)=((g F*f F) • 1) * x n i; rw [Algebra.smul_mul_assoc,Algebra.smul_mul_assoc,one_mul,one_mul,Algebra.smul_mul_assoc,one_mul,smul_smul]
  | zero=> rw [mul_zero]; exact Submodule.zero_mem X
  | add x y _ _ ih ih' => rw [mul_add]; exact Submodule.add_mem X ih ih'
  | smul a y _ v=> rw [Algebra.mul_smul_comm]; exact Submodule.smul_mem X a v

-- all tilted faces. use static across all epochs in Cover. use axes 1,2 for all positions even on 0 plane.
def facet (x : Cover) : Face ℤ := (nodeC x,⟨(1,2),by decide⟩)
def buzzbox (x : Cover) : Finset Cover := List.toFinset (visits (nodeC x) (square 1 2))
variable (b)
abbrev grindset : Finset (Face ℤ) := Finset.univ.image (facet ∘ b)
abbrev grindscape := S ∪ Finset.univ.biUnion (buzzbox ∘ b)
lemma grind_rest : restsOn (grindset b) (grindscape b S) := by
 intro x p; obtain ⟨i,_,rfl⟩:= Finset.mem_image.mp p; exact Finset.Subset.trans (Finset.subset_biUnion_of_mem (buzzbox ∘ b) (Finset.mem_univ i)) subset_union_right
lemma grind_between {x y : ℤ} (h : Between J 0 x y S) (g : ∀ i, nodeC (b i)∈ S) : Between J 0 x y (grindscape b S):=by
 intro i p; rcases mem_union.mp p with p|p
 · exact h i p
 obtain ⟨j,v,k⟩:=mem_biUnion.mp p; suffices e:i 0=nodeC (b j) 0 by rw [e]; exact h _ (g _)
 change i∈ buzzbox _ at k; unfold buzzbox at k; simp [visits,square] at k; rcases k with (k|k|k|k|k); all_goals subst i; norm_num [step_apply, show (0:Axis)≠1 by decide, show (0:Axis)≠2 by decide]
end YM.CF.Buffered.Afterglow.Tower.Selected
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.tint_price
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.fil_tinted
