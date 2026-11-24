import YM.CF.Buffered.Subst
import YM.CF.Buffered.Forest

/-! # Support after substitution including dependencies from the true links

Gauge-M constants: take manuscript's r₁ *at least* 100 L(1+R)
on the fixed scale system, R the Laurent radius. This pays our entire first
stage, including Seine. Can use sharper fees nearZero and beforePad here. -/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
set_option maxHeartbeats 450000
noncomputable section
namespace YM.CF.Buffered.Advance
open Function Fock NormedSpace SU Lat Lattice Spire Cube Finset MeasureTheory Branch Reflect Window Wilson Rush Peaks Scroll
open Phase Skye Pastry Tulip Dial Paige Push.SectorMeasure Scree Vault Fir Peaks Drapes Tap Precision Tree Next.SectorChange Stencil
open Reed (Fine think)
open scoped Topology BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N P : Side} (G : Ratio N P) (j : ℕ) (Q : Op Slot) (M : Male) (ho : Odd G.count.val)
local notation "NC" => (More N)
local notation "L" => G.count.val
-- Support rescaled by the **gauge** ratio then extended by ONE-LEVEL fine distance.
def padded (G : Ratio N P) (S : Support (More N)) (R : ℕ) : Support (More P) := halo R (S.image (ratio G).embed)
variable (S : Support (More N))
lemma within_fee {v : Ket (Single N)} (h : withinM (modesIn N S) v) (b : Bool) : withinM (modesIn N S) (acts (feeL b N Q) v) := by
  let A := cutM (modesIn N S); let W:=plankP N Q
  have hx : Commute A W := by
    unfold Commute SemiconjBy
    ext ⟨⟨x,a⟩,k⟩ ⟨⟨y,c⟩,l⟩; by_cases p:x=y
    · subst y; by_cases h:node x∈ S <;> simp [A,cutM,Matrix.mul_diagonal,Matrix.diagonal_mul,h]
    have he : W ((x,a),k) ((y,c),l)=0 := by change jump (Equiv.refl (Site N)) (fun _=>(Aop - _) ⊗ₖ Q) (x,a,k) (y,c,l)=_; simp only [jump_apply, Equiv.refl_apply, if_neg p]
    simp [he,A,cutM,Matrix.mul_diagonal,Matrix.diagonal_mul]
  letI : NormedAlgebra ℚ (Op (Single N)) := NormedAlgebra.restrictScalars ℚ ℂ _
  have ht:Commute A (feeL b N Q) := by cases b; exact hx.neg_right.exp_right; exact hx.exp_right
  change acts A _= _; rw [←act_mul,ht.eq,act_mul,h]
local notation "I" => Iota G
local notation "φ" => patchQ G
lemma patched_vertex {v : Ket (Single N)} (h : withinM (modesIn N S) v) (k : I) (e : (coat φ v).ofLp k ≠ 0) : Peaks.touch G false k.1∈ S.image (ratio G).embed := by
  obtain ⟨i,-,rfl⟩:= show ∃ i ∈ Finset.univ, φ i=k from mem_map.mp (by by_contra t; exact e (basin φ v k t))
  apply mem_image.mpr; refine ⟨node i.1.1,(modes_at ..).mp ?_,rfl⟩
  by_contra p; rw [←seamK,trails,(within_test ..).mp h i p] at e; exact e rfl
variable {R : ℕ} (p : Stencil.LaurentRadius j G.count R)
local notation "R₀" => clothRadius G.count R
include p ho
lemma mode_support {z : Nom N P} {v : Ket (Single N)} (h : withinM (modesIn N S) v) (b : Bool) : withinM (modesIn P (padded G S R₀)) (byMode G j Q M z b v) := by
  apply (within_test ..).mpr; let m:=coat φ (acts (feeL b N Q) v)
  intro k hk; obtain ⟨i,rfl⟩:= (switchG G).surjective k
  simp only [byMode_eq,seamK,Equiv.toEmbedding_apply, Equiv.symm_apply_apply, act_at]; change ∑ l : I, _ = 0
  refine sum_eq_zero fun l _=>?_ ; by_cases e:m.ofLp l=0; exact mul_eq_zero_of_right _ e
  have hh:= patched_vertex G S (within_fee Q S h b) l e
  apply mul_eq_zero_of_left; refine cloth_support G j p ho M i l z ?_
  by_contra! hy; exact hk ((modes_at ..).mpr (show node (switchG G i).1.1∈ padded G S R₀ from halo_spec.mpr ⟨touch G false l.1,hh, show separation _ (node (switchG G i).1.1) ≤ R₀ from hy⟩))
lemma mode_agrees {x y : Nom N P} {v : Ket (Single N)} (h : withinM (modesIn N S) v) (b : Bool)
    (u : Agrees (padded G S R₀) x.1 y.1) : byMode G j Q M x b v=byMode G j Q M y b v := by
  rw [byMode_eq,byMode_eq]; apply congrArg _; let m:=coat φ (acts (feeL b N Q) v)
  apply PiLp.ext; intro k; rw [act_at,act_at]; refine sum_congr rfl fun l _=> ?_; by_cases e:m.ofLp l=0
  · change _ * m.ofLp l= _ * m.ofLp l; rw [e]; simp
  have h := patched_vertex G S (within_fee Q S h b) l e
  dsimp only; rw [cloth_local G j p ho M k l x y (agrees_mono u (Corona.halo_mono le_rfl (singleton_subset_iff.mpr h)))]

variable (q : Chi) (d : ℝ)
def middle (F : Forest (ratio G)) (W : Fields P) (V : Fields N) : Nom N P := (seine G F q d W.2 V.2,V.2)
def before (A : Mark N) (F : Forest (ratio G)) (W : Fields P) (V : Fields N) := subF G j Q M ho (middle G q d F W V) (A V)
-- extend Env.coupled (Bounds) to operators. (Declare separately to avoid instance search
-- with all the Nom unfolds.)
omit p ho in
private lemma env_var {α B X T : Type*} [MeasurableSpace α] [TopologicalSpace B] [CompactSpace B]
    [SecondCountableTopology B] [MeasurableSpace B] [OpensMeasurableSpace B]
    [MeasurableSpace X] [NormedAddCommGroup X] [BorelSpace X] [SecondCountableTopology X] [ProperSpace X]
    [MeasurableSpace T] [NormedAddCommGroup T] [BorelSpace T]
    {b : α → B} {x : α → X} (y : Measurable b) (h : RG.Envelope x) (f : B × X → T) (p : Continuous f) : RG.Envelope (fun a=> f (b a,x a)) := by
  obtain ⟨C,g⟩:= h.cost
  obtain ⟨K,w⟩:= ((isCompact_univ.prod (ProperSpace.isCompact_closedBall (0:X) C)).image p.norm).bddAbove
  exact ⟨p.measurable.comp (y.prodMk h.meas), K, fun a=> w ⟨(b a,x a),⟨Set.mem_univ _, mem_closedBall_zero_iff.mpr (g _)⟩,rfl⟩⟩
lemma before_env (u : 0<d) (k : 2*d< firstRadius SU.group) (A : Mark N) (v : RG.Envelope A) (F : Forest (ratio G)) : RG.Envelope (uncurry (before G j Q M ho q d A F)) := by
  let X (z : Fields P × Fields N):= middle G q d F z.1 z.2
  let J : Fields P × Fields N → Pane P × Pane N:= fun z=>(z.1.2,z.2.2)
  have hk : Continuous J:= (continuous_snd.comp continuous_fst).prodMk (continuous_snd.comp continuous_snd)
  have he : Continuous X := ((brake G q d F u k).comp hk).prodMk (continuous_snd.comp continuous_snd)
  let x(V : Fields P × Fields N) := A V.2
  let f (V : Nom N P × FC (Single N)):= subF G j Q M ho V.1 V.2
  change RG.Envelope (fun V=> f (X V,x V))
  refine env_var he.measurable ?_ f (sub_cont G j Q M ho p); exact Env.along v measurable_snd
-- inputs needed on the two lattices before taking laws (frame unaffected)
theorem sub_local {b : Bool} {A : FC (Single N)} {x y : Nom N P} (h : Fine (Tset N) (modesIn N S) b A) (k : Agrees (padded G S R₀) x.1 y.1) :
    subF G j Q M ho x A = subF G j Q M ho y A := by
  induction h with
  | one=> rw [sub_one,sub_one]
  | empty=> rw [map_zero,map_zero]
  | scale _ _ ih=> rw [map_smul,map_smul, ih]
  | add _ _ ih it=> rw [map_add,map_add,ih,it]
  | grow a b ih it=> rw [sub_mul _ _ _ _ _ _ a b,sub_mul _ _ _ _ _ _ a b, ih,it]
  | seed i u=>
    have hz := mode_agrees G j Q M ho S p (x:=x) (y:=y) (within_basis _ i u)
    by_cases g' : i∈ Tset N
    · rw [show (think (Tset N)).term i=put i from if_pos g', sub_put _ _ _ _ _ _ _ g', sub_put _ _ _ _ _ _ _ g',hz true k]
    rw [show (think (Tset N)).term i= -takeF i from if_neg g',map_neg,map_neg, sub_take _ _ _ _ _ _ _ g', sub_take _ _ _ _ _ _ _ g',hz false k]
lemma subFine {b : Bool} {A : FC (Single N)} (x : Nom N P) (h : Fine (Tset N) (modesIn N S) b A) : Fine (Tset P) (modesIn P (padded G S R₀)) b (subF G j Q M ho x A) := by
  induction h with
  | one=> rw [sub_one]; exact Fine.one
  | empty=> rw [map_zero]; exact Fine.empty _
  | scale _ _ ih=> rw [map_smul]; exact ih.scale _
  | add _ _ ih it=> rw [map_add]; exact ih.add it
  | grow a b ih it=> rw [sub_mul _ _ _ _ _ _ a b]; exact ih.grow it
  | seed i u=>
    have hz(b : Bool) := mode_support G j Q M ho S p (z:=x) (within_basis _ i u) b
    by_cases g' : i∈ Tset N
    · rw [show (think (Tset N)).term i=put i from if_pos g', sub_put _ _ _ _ _ _ _ g']; exact fine_create _ (carried_up G j Q M ho x true (within_basis _ i g')) (hz true)
    rw [show (think (Tset N)).term i= -takeF i from if_neg g', map_neg,sub_take _ _ _ _ _ _ _ g']; exact fine_neg (fine_remove _ (carried_down G j Q M ho x false (within_basis _ i (mem_compl.mpr g'))) (hz false))
omit p ho
-- integer radii imply our first-stage estimates on both lattices; keep exact formulas.
def nearZero (R : ℕ) := 16 + 8*R + 1
def beforePad (R : ℕ) := 16+8*R+4
lemma parent_zone (R : ℕ) : (padded G S (clothRadius G.count R)).image (ratio G).parent ⊆ halo (nearZero R) S := by
  rintro x hx; obtain ⟨y,hy,rfl⟩:= mem_image.mp hx
  obtain ⟨z,hz,hv⟩:= halo_spec.mp hy; obtain ⟨s,hs,rfl⟩:= mem_image.mp hz
  have hp:= Corona.foreshorten (ratio G) ((ratio G).embed s) y; rw [Ratio.embed_parent] at hp; apply halo_spec.mpr; refine ⟨s,hs,Nat.le_of_mul_le_mul_left (hp.trans ?_) G.count.property⟩;
  unfold nearZero; apply (Nat.add_le_add_right hv L).trans_eq; unfold Stencil.clothRadius; change _+ G.count.val=G.count.val*(16+8*R+1); ring
lemma before_zone (R : ℕ) : halo (4*L) (padded G S (clothRadius G.count R)) ⊆ padded G S (L*beforePad R) := by
  intro x hx; obtain ⟨y,hy,hv⟩:= halo_spec.mp hx; obtain ⟨z,hz,hw⟩:= halo_spec.mp hy; apply halo_spec.mpr; refine ⟨z,hz,(separation_triangle z y x).trans ((Nat.add_le_add hw hv).trans_eq ?_)⟩; unfold beforePad Stencil.clothRadius; ring
include p ho
theorem before_local {b : Bool} {A : Mark N} {x y : Fields N} {X Y : Fields P} {F H : Forest (ratio G)} (a : AtSupport b S A)
    (u : Agrees S x.1 y.1) (v : Agrees (halo (nearZero R) S) x.2 y.2) (w : Agrees (padded G S (L*beforePad R)) X.2 Y.2) (e : sameForest (halo (nearZero R) S) F H) :
    before G j Q M ho q d A F X x=before G j Q M ho q d A H Y y := by
  unfold before; rw [← a.dep x y u (agrees_mono v (halo_subset ..))];
  refine sub_local G j Q M ho S p (a.allV x) ?_
  exact seine_local G ho (agrees_mono w (before_zone G S R)) (agrees_mono v (parent_zone G S R)) (fun i hx => e i (parent_zone G S R hx)) q d
end YM.CF.Buffered.Advance
