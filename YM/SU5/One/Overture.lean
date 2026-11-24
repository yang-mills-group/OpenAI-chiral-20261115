import VerifiedSatinSelectedSectors
/-! # Graded pairing under the true Donor
Adapt `CF.Buffered/ Weight,Trace,Place,Microscopic` & FiniteGaugeData/Journey/Every proofs.
Retaining Tape dependent signs, same transfer, before taking chosen sharp law.
-/
set_option synthInstance.maxSize 28000
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Buffered.Heat
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant Phase Mir Mir.Trip MeasureTheory Finset Reflect
open RP Spark RG WilsonStartup Vale Scroll Spire Nova Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {m B : Side} {c : Phase.Part m B} {e d : ℝ}
local notation "X" => Pack m B
local notation "I" => Xmind m B
local notation "A" => FC (Xmind m B)
local notation "U" => upperP (CSide m B)

structure GradeNorth (rank : Bool) (i : Axis) (f : RP.Test m B) : Prop where
  envelope : Envelope f
  sector (x) : Sector (colony m B i) rank (f x)
  loc x y : NorthOf m B i x y → f x=f y

variable {rank : Bool}
def gradeProduct (rank : Bool) (i : Axis) (f g : RP.Test m B) : RP.Test m B := chord rank • testProduct i f g
lemma gradeProduct_env (rank : Bool) (i : Axis) {f g : RP.Test m B} (h : Envelope f) (k : Envelope g) : Envelope (gradeProduct rank i f g) :=
 Girt.pole_w _ (fun (x : FC (Xmind m B)) => chord rank • x) (by fun_prop) (product_env i h k)
variable (p : Pinning m B) (W : Scroll m B c) (clip : Clip) (β t u : ℝ)
local notation "λ₀" => fun (i : ℕ)=> (i+1:ℝ)⁻¹
lemma grade_sector (i : Axis) (cut : Foot m B) (n : ℕ)
    (f : RP.Test m B) (h : GradeNorth rank i f) (a b : Tape m B (n+1)) (x : X) (e : ℝ) :
    Sector (colony m B i) (rank.xor (parityTape _ a b)) (rightHand i cut u e n f x a b) := by
  have he := sector_exp (RP.letter U (colony m B i) (seedArg e x))
  simpa only [rightHand, Bool.xor_false, Bool.false_xor] using (((h.sector x).mul (hand_sector i cut _ x _ a b)).mul he : Sector (colony m B i) _ (rightHand i cut u e n f x a b))
variable {a₁ a₂ : ℝ} (b : Budget B e d) (H : ScaleK a₁ a₂ W)
include b H
lemma polarGrade (hu : 0 ≤ u) (i : Axis) (cut : Foot m B) (n : ℕ) (f g : RP.Test m B) (hf : GradeNorth rank i f) (hg : GradeNorth rank i g)
    (x y z : Pack m B) : let Q := tiedK m B i x
    slabTerm p W clip β t e (gradeProduct rank i f g) (hotEvol i cut u n) (Q y z) =
      ∑ a : Tape m B (n+1), ∑ k : Tape m B (n+1),
        star (kernelInside p W clip β t u e i cut n f a k (Q z z)) * kernelInside p W clip β t u e i cut n g a k (Q y y) := by
  intro Q
  unfold slabTerm
  rw [scalarWeight_split p H b]
  by_cases k : Q y z ∈ TallyR m B e 0
  · let T := RP.finger m B i; let S := RP.colony m B i; let σ := Q z z; let γ := Q y y
    let F := f σ; let G := g γ
    let P := pairSquare T rank F G
    let r := λ₀ n * u
    let A' := hand i cut r γ (n+1); let B' := hand i cut r σ (n+1)
    have ht : gradeProduct rank i f g (Q y z)= P := by
      unfold gradeProduct P pairSquare
      rw [Pi.smul_apply]; unfold testProduct; rw [show Pbar m B i (Q y z)=Q z y from sew .., hf.loc _ σ (strum ..), hg.loc _ γ (strum ..)]
    have hE : hotEvol i cut u n (Q y z)= ∑ a,∑ b, pairSquare T (parityTape _ a b) (B' a b) (A' a b) := n_layer_expand i cut u _ (by positivity) x y z _
    rw [ht,hE,seed_split b i k]; simp_rw [Finset.mul_sum, Finset.sum_mul, Matrix.sum_apply,Finset.mul_sum]; refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    let z' := halfSeed e i σ; let y' := halfSeed e i γ
    let w := parityTape _ a b
    have hz : Sector S false z' := sector_exp (RP.letter ..)
    have hA : Sector S w (A' a b) := hand_sector ..
    have hB : Sector S w (B' a b) := hand_sector ..
    have hv :
        P * pairSquare T w (B' a b) (A' a b) * pairSquare T false z' y' =
         pairSquare T (rank.xor w) (rightHand i cut u e n f σ a b) (rightHand i cut u e n g γ a b) := by
      unfold P
      rw [square_mul T S (hg.sector γ) hB (movedCol ..), square_mul T S ((hg.sector γ).mul hA) hz (movedCol ..), Bool.xor_false]; rfl
    let V₁ := rightHand i cut u e n f σ a b; let V₂ := rightHand i cut u e n g γ a b
    let h x := halfWeight p W clip β t e i x
    change star (h σ)*h γ * (P * pairSquare T w _ _ * pairSquare T false z' y') U U = star (h σ * V₁ U U) * (h γ * V₂ U U)
    rw [hv, show pairSquare T (rank.xor w) V₁ V₂ U U = star (V₁ U U)*V₂ U U from
      theta_square U T (slide_plus i) S (movedCol ..) V₁ V₂ (rank.xor w) (grade_sector u i cut n f hf a b σ _) (grade_sector u i cut n g hg a b γ _), star_mul']; ring
  dsimp only [kernelInside, halfWeight]
  rcases not_and_or.mp (show ¬ (Q y y∈ TallyR m B e 0 ∧ Q z z ∈ TallyR m B e 0) from fun h => k ((RP.apt ..).2 h)) with l|l
  all_goals dsimp only [Q] at l ⊢; simp_rw [Set.indicator_of_notMem l]; simp
end YM.CF.Buffered.Heat
namespace YM.CF.Buffered.Heat
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology ComplexOrder
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant Phase Mir Mir.Trip MeasureTheory Finset Reflect
open RP Spark RG WilsonStartup Vale Scroll Spire Nova Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {m B : Side} {c : Phase.Part m B} {e d a₁ a₂ : ℝ}
local notation "X" => Pack m B
local notation "I" => Xmind m B
local notation "A" => FC (Xmind m B)
local notation "U₊" => upperP (CSide m B)
local notation "Wμ" => wheel m B

variable (p : Pinning m B) (W : Scroll m B c) (clip : Clip) (β t u : ℝ)
variable (b : Budget B e d) (H : ScaleK a₁ a₂ W) (i : Axis) (cut : Foot m B)
include H b
section
local notation "T" => transfer p W clip β t u e i cut
local notation "κ" => kernelInside p W clip β t u e i cut
local notation "M" => slabTerm p W clip β t e
variable {rank : Bool}
theorem at_layer_grade (hu : 0 ≤ u) (n : ℕ) (f g : RP.Test m B) (hf : GradeNorth rank i f) (hg : GradeNorth rank i g) :
    (∫ x, slabTerm p W clip β t e (gradeProduct rank i f g) (hotEvol i cut u n) x ∂wheel m B) =
      kernelTrace (n+1) (T n g) (kernelStar (n+1) (T n f)) := by
  let N := Tape m B (n+1)
  let a := tiedK m B i
  let F (x) (y) j k := κ n f j k (a x y y)
  let G (x) (y) j k := κ n g j k (a x y y)
  let P (j k : N) x := (∫ y, G x y j k ∂Wμ)*star (∫ y, F x y j k ∂Wμ)
  let Q := M (gradeProduct rank i f g) (hotEvol i cut u n)
  have hp := slabTerm_env p W clip β t b H _ _ (gradeProduct_env rank i hf.envelope hg.envelope) (Env.compact (hotEvol_cont i cut u n))
  have ht(j k:N):Envelope (P j k):=env_mult (marginalK_env p W clip β t u b H i cut g hg.envelope j k)
    (Girt.pole_w _ star continuous_star (marginalK_env p W clip β t u b H i cut f hf.envelope j k))
  have hx (x : X) : (∫ z, Q (RP.quill m B i (x,z)) ∂(Wμ).prod Wμ)= ∑ j : Tape m B (n+1), ∑ k : Tape m B (n+1), P j k x := by
    let A' j k (z:X×X) := G x z.1 j k * star (F x z.2 j k)
    have he (z:X×X) : Q (RP.quill m B i (x,z))=∑ j : Tape m B (n+1), ∑ k : Tape m B (n+1), A' j k z :=
      (polarGrade p W clip β t u b H hu i cut n f g hf hg x z.1 z.2).trans (sum_congr rfl fun j _ => sum_congr rfl fun k _ => mul_comm ..)
    have hA (j k:N): Envelope (A' j k) := by
      have hz : Continuous fun y:X=> tiedK m B i x y y := (zoneA i x).comp (continuous_id.prodMk continuous_id)
      exact env_mult (Env.along (kernelInside_env p W clip β t u b H i cut n g hg.envelope j k) (hz.measurable.comp measurable_fst))
        (Girt.pole_w _ star continuous_star (Env.along (kernelInside_env p W clip β t u b H i cut n f hf.envelope j k) (hz.measurable.comp measurable_snd)))
    simp_rw [he]
    rw [integral_finsetSum]; swap
    · exact fun i _ => Env.integrableX (Env.total _ (hA i)) _
    refine sum_congr rfl fun j _ => ?_; rw [integral_finsetSum]; swap
    · exact fun i _ => Env.integrableX (hA j i) _
    refine sum_congr rfl fun k _ => ?_ ; unfold A' P; rw [integral_prod_mul (fun y=> G x y j k) (fun z => star (F x z j k))]; exact congrArg (_ * ·) (show (∫ z, star (F x z j k) ∂Wμ)=_ from integral_conj (𝕜:=ℂ) (f:=fun z=> F x z j k))
  unfold kernelTrace; rw [heard m B i Q (Env.integrableX hp Wμ)]
  simp_rw [hx]; rw [integral_finsetSum]; swap
  · exact fun i _ => Env.integrableX (Env.total _ (ht i)) _
  refine sum_congr rfl fun j _ => ?_; rw [integral_finsetSum]; swap
  · exact fun i _ => Env.integrableX (ht j i) _
  refine sum_congr rfl fun k _ => ?_
  -- use both seams and their measures
  simp_rw [kernelStar,Prod.swap_swap]
  change ∫ x,P j k x ∂Wμ = ∫ x, P j k (twoSeams i x) ∂(Wμ).prod Wμ
  have hv := show MeasurePreserving (twoSeams i) ((Wμ).prod Wμ) Wμ from binary_w ..
  exact (congrArg (fun ν:Measure X => ∫ x,P j k x ∂ν) hv.map_eq.symm).trans (integral_map hv.measurable.aemeasurable (ht j k).meas.aestronglyMeasurable)

theorem from_layers_grade (hu : 0 ≤ u) (f g : RP.Test m B) (hf : GradeNorth rank i f) (hg : GradeNorth rank i g) :
    Tendsto (fun n => kernelTrace (n+1) (T n g) (kernelStar (n+1) (T n f)))
      atTop (𝓝 (heatNum p W clip β t e u (axisCut m B i cut) (gradeProduct rank i f g))) :=
  (slab_limit p W clip β t u b H i cut _ (gradeProduct_env rank i hf.envelope hg.envelope)).congr
    (fun n => at_layer_grade p W clip β t u b H i cut hu n f g hf hg)

theorem two_slab_grade (hu : 0 ≤ u) (f : RP.Test m B) (hf : GradeNorth rank i f) :
    0 ≤ heatNum p W clip β t e u (axisCut m B i cut) (gradeProduct rank i f f) :=
  ge_of_tendsto' (from_layers_grade p W clip β t u b H i cut hu f f hf hf) fun _ =>
    trace_mul_star _ _ (transfer_env p W clip β t u b H i cut _ hf.envelope)
end
end YM.CF.Buffered.Heat
namespace YM.CF.Buffered.Heat
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Kronecker ComplexOrder
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant Phase Mir Mir.Trip MeasureTheory Finset Reflect
open RP Spark RG WilsonStartup Vale Scroll Spire Nova Push.SectorMeasure Nacre Window Tulip Skye Brace
attribute [local instance] opCStarAlgebra

variable {m B n : Side} {c : Phase.Part m B} {e d a₁ a₂ : ℝ}
local notation "X" => Pack m B
local notation "I" => Xmind m B
local notation "A" => FC (Xmind m B)
local notation "N" => CSide m B
local notation "Wμ" => wheel m B
local notation "β₀" => Brace.northZ m B

variable (i : Axis) (z : ℤ)

variable {rank : Bool}
lemma gradeShift_modes (B : Side) (f : Evaluation n) (w : ℕ)
    (h : ∀ x,Sector (modesIn n (Buffered.band n i (gaugeShift B z) w)) rank (f x)) :
    ∀ x, Sector (modesIn n (Buffered.band n i 0 w)) rank (liftShift i B z f x) := by
  intro x; apply north_sector _ _ _ (h _); apply prep_moves; intro x
  rw [show (gaugeShift B z)=2*(2*(↑B.val:ℤ)*z) from by unfold gaugeShift; ring]; simpa only [coverShift,zero_add] using (band_shift i 0 n (2*(↑B.val:ℤ)*z) w x)
lemma liftShift_smul (B : Side) (r : ℂ) (f : Evaluation n) : liftShift i B z (r • f)=r • liftShift i B z f := by
 funext x; unfold liftShift; change twist _ (r • _) = r • twist _ _; exact twist_scalar ..
variable (p : Pinning m B) (W : Scroll m B c) (clip : Clip) (β t u : ℝ)

lemma rephased_north_grade (f : Evaluation N) (h : Envelope f) (w : LocalOn (Buffered.band N i (gaugeShift B z) 0 : Set _) f)
    (u : ∀ x, Sector (modesIn N (Buffered.band N i (gaugeShift B z) 0)) rank (f x)) : GradeNorth rank i (rephased i z f) := by
  refine ⟨Girt.pole_w _ (toSeam m B i) ((breeze _).comp (cxC _)) (Env.along (liftShift_env i z B f h) measurable_fst),
    fun x=> toSeam_forward i (north_modes_eq i ▸ gradeShift_modes i z B f 0 u x.1) rfl,?_⟩
  intro x y k; unfold rephased; apply congrArg; apply liftShift_local _ z B f 0 w; rw [band_zero]; exact k.gaugeS
lemma rephased_pair_grade (f g : Evaluation N) (h : ∀ x,Sector (modesIn N (Buffered.band N i (gaugeShift B z) 0)) rank (f x)) :
    rephased i z (chord rank • (Buffered.refl i (gaugeShift B z) f * g))=gradeProduct rank i (rephased i z f) (rephased i z g) := by
  funext x; unfold rephased gradeProduct; rw [liftShift_smul,Pi.smul_apply,toSeam_scalar, liftShift_prod,Pi.mul_apply,toSeam_prod,liftShift_refl _ z B f _ _ h]
  unfold Buffered.refl; rw [carR_zero,fling_zero, toSeam_turn i (north_modes_eq i ▸ gradeShift_modes i z B f 0 h _)]
  rfl
section plt
variable (b : Budget B e d) (H : ScaleK a₁ a₂ W)
include H b
local notation "S" => Buffered.band N i (gaugeShift B z) 0
-- whole translated statement, pinning as in Manuscript
lemma displaced_limit_grade (hu : 0 ≤ u) (f g : Evaluation N) (hf : Envelope f) (hg : Envelope g)
    (wf : LocalOn (S:Set _) f) (wg : LocalOn (S:Set _) g)
    (p' : ∀ x,Sector (modesIn N S) rank (f x)) (q' : ∀ x,Sector (modesIn N S) rank (g x)) :
    let T := fun n => transfer p W clip β t u e i β₀ n
    Tendsto (fun n=>kernelTrace (n+1) (T n (rephased i z g)) (kernelStar (n+1) (T n (rephased i z f)))) atTop
      (𝓝 (heatNum p W clip β t e u β₀ (insertTop (chord rank • (Buffered.refl i (gaugeShift B z) f * g))))) := by
  intro T; rw [rephased_eq i z p W, rephased_pair_grade _ z _ _ p']
  exact from_layers_grade p W clip β t u b H i _ hu _ _ (rephased_north_grade i z f hf wf p') (rephased_north_grade i z g hg wg q')

theorem top_nonnegative_grade (hu : 0 ≤ u) (f : Evaluation N) (h : Envelope f) (w : LocalOn (S:Set _) f)
    (w₀ : ∀ x,Sector (modesIn N S) rank (f x)) :
    0 ≤ heatNum p W clip β t e u β₀ (insertTop (chord rank • (Buffered.refl i (gaugeShift B z) f * f))) := by
  rw [rephased_eq i z p W,rephased_pair_grade _ z f f w₀]
  exact two_slab_grade p W clip β t _ b H i β₀ hu _ (rephased_north_grade i z f h w w₀)
end plt
end YM.CF.Buffered.Heat
namespace YM.CF.Buffered.Heat
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Tap Laic Dial Paige Vault Pec Skye Pastry Cascade Phase Brace Scree RG Spark RP Gloss Branch Reflect Window
open Reed (Fine think)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {m B L : Side} {j : ℕ} {ho : Odd L.val} {Y : Pricing j L ho (Thread j)}{e : ℝ}
variable (P : Grasp Y B e) (X : GramM (CSide m B)) (R : Loom (CSide m B)) (p : Pinning m B)
   (W : Scroll m B (Brace.northZ m B)) (clip : Clip) (u : ℝ)
local notation "c₀" => CSide m B
local notation "f₀" => Brace.northZ m B
variable (eyes : Eyes P X R p W clip u) {a D b : ℝ} (k : ScaleK a D W) (v : Budget B e b) {d' b' : ℝ} {n : ℕ} (T : Roof (CSide m B) b' d' n R) (h : X.p.threshold ≤ b') (U : Rue.IsleB SU.group X.p.threshold)
variable {rank : Bool}
lemma both_north_grade (f : Mark (CSide m B)) {i : Axis} {s : ℤ} (h : AtSupport rank (Buffered.band (CSide m B) i s 0) f) :
    Envelope (both f) ∧ LocalOn (Buffered.band c₀ i s 0) (both f) ∧ ∀ x, Sector (modesIn c₀ (Buffered.band c₀ i s 0)) rank (both f x) := ⟨Env.along h.env (measurable_id.prodMk measurable_id), fun _ _ v=> h.dep _ _ v v, fun x=> (h.allV (x,x)).sector⟩
include eyes k v T h U
variable (i : Axis) (s : ℤ) (f g : Mark (CSide m B))
local notation "μ" => gaugeShift B s
local notation "E" => Buffered.band c₀ i (gaugeShift B s) 0
-- trace limit on exactly the top mark obtained, reflection simultaneously peeled
lemma summit_trace_grade (a : AtSupport rank E f) (b : AtSupport rank E g) (hu : 0≤u) :
    let l := fun n => transfer p W clip X.beta X.p.threshold u e i f₀ n
    Tendsto (fun n => kernelTrace (n+1) (l n (rephased i s (both g))) (kernelStar (n+1) (l n (rephased i s (both f))))) atTop
      (𝓝 (markedRead (Reflect.chord rank • (reflMark i μ f * g)) R (denZ X P R))) := by
  intro l; rw [summit_num P X R p W clip u eyes k v T h U]; swap; · exact Girt.pole_w _ (fun (T : FC (Single c₀)) => Reflect.chord rank • T) (by fun_prop) <| env_mult ((a.refl i μ).env) b.env
  obtain ⟨p0,p1,p2⟩:= both_north_grade f a; obtain ⟨q0,q1,q2⟩:= both_north_grade g b
  exact displaced_limit_grade i s p W clip X.beta X.p.threshold u v k hu (both f) (both g) p0 q0 p1 q1 p2 q2
lemma summit_gram_grade (x : AtSupport rank E f) (hu : 0 ≤ u) : 0 ≤ markedRead (Reflect.chord rank • (reflMark i μ f*f)) R (denZ X P R) := by
  rw [summit_num P X R p W clip u eyes k v T h U]; swap; · exact Girt.pole_w _ (fun (T : FC (Single c₀)) => Reflect.chord rank • T) (by fun_prop) <| env_mult (x.refl i μ).env x.env
  obtain ⟨p0,p1,p2⟩:= both_north_grade f x; exact top_nonnegative_grade i s p W clip X.beta X.p.threshold u v k hu (both f) p0 p1 p2
end YM.CF.Buffered.Heat
namespace YM.CF.Buffered.Afterglow.Journey
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Tap Laic Dial Paige Vault Pec Skye Pastry Cascade Phase Brace Scree RG Spark RP Gloss Branch Reflect Window Vale Girt
open Py (Vestal Cape)
open Reed (Fine think)
open Advance Heat
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {m B L : Side} {j : ℕ} {ho : Odd L.val} {Y : Pricing j L ho (Thread j)}{e : ℝ}
variable (P : Grasp Y B e) (X : Vestal m B L) (R : Cape m B L) (q : Chi) (d : ℝ)
variable (n : ℕ) (Q : ℕ → Haro.SpaceM)
variable (A : Steps m B L) {D J w U : ℕ} (v : Stencil.LaurentRadius j L D) (L' : 3 ≤ L.val) (T : Granted P X R q d n Q A J)
variable (t : ∀ k<n,LoomLaw (R k) w) (p : Margin L D w J U)
local notation "Ω" i:max=> cell m B L i
local notation "ρ" i=> denZ (X i) P (R i)
local notation :max "out_" i:max=>nextMark (ho:=ho) (j:=j) X R q d Q A i
include P v L' T t p
variable {rank : Bool}
lemma sooty_grade (a:Axis){i:ℕ} (h:i<n)(s:ℤ){f:Mark (Ω i)}(u:AtSupport rank (band (Ω i) a s U) f):
    AtSupport rank (band (Ω (i+1)) a ((L.val:ℤ)*s) U) ((out_ i) f) ∧
    markedRead (chord rank • (reflMark a s f*f)) (R i) (ρ i) = markedRead (chord rank • (reflMark a ((L.val:ℤ)*s) ((out_ i) f)*(out_ i) f)) (R (i+1)) (ρ (i+1)):=by
  obtain ⟨g⟩:= T.grant i h; obtain ⟨V,b,c,Y,l⟩:= g.cap
  let K:= apt m B L i
  have we:= T.branch i h
  have vt:= surround K (A i) j (Q i).val (X (i+1)).J.M ho q d (X (i+1)).beta (R i) (g.power.symm ▸ v) Y.bill we g.legal.1 g.legal.2 _ u (t _ h) (T.aligned i h)
  rw [T.radius i h] at vt
  refine ⟨vt.mono (margin_band a _ p K rfl L'),?_⟩
  have hz:= separated_mult K (A i) j (Q i).val (X (i+1)).J.M ho q d (X (i+1)).beta (R i) (g.power.symm ▸ v) Y.bill we g.legal.1 g.legal.2 _ _ (u.refl a s) u (t _ h) (fun x px y py=> margin_separate a s p x y px py)
  have hs:= rising K (A i) j (Q i).val (X (i+1)).J.M ho q d (X (i+1)).beta (R i) a s (T.aligned i h) u we Y (g.power.symm ▸ v) g.legal.1 g.legal.2
  have e : AtSupport false univ (reflMark a s f*f) := by simpa using ((u.refl a s).mono (subset_univ _)).mulM (u.mono (subset_univ _))
  rw [mark_smul,mark_smul,single_num P X R q d n Q A v T e h]; unfold nextMark; rw [hz,hs]; rfl

variable (Z:Buffered.Donor P X R n)
include Z
local notation "ζ" z:max=> gaugeShift B z
lemma onward_grade (a:Axis) (i:ℕ)(h:i≤ n)(z:ℤ)(f:Mark (Ω i))(w_:AtSupport rank (band (Ω i) a (ζ z) U) f):
    0 ≤ markedRead (chord rank • (reflMark a (ζ z) f*f)) (R i) (ρ i) := by
  let E(i:ℕ):= ∀ z:ℤ,∀ f:Mark (Ω i),AtSupport rank (band (Ω i) a (ζ z) U) f → 0 ≤ markedRead (chord rank • (reflMark a (ζ z) f*f)) (R i) (ρ i)
  have he: E n:=by
    intro s f u; obtain ⟨X',Y,w,h,V⟩:= Z.grants; obtain ⟨x,y,t,s',A_⟩:=Z.roof
    exact summit_gram_grade P _ _ Z.pin Z.scroll _ _ Z.top h V s' A_ (T.noTies n le_rfl) a s _ (u.mono (band_anti a (ζ s) (Nat.zero_le _))) Z.warm
  have ht(i:ℕ)(h:i<n)(e:E (i+1)):E i:=by
    intro s f u; obtain ⟨r,h'⟩:= sooty_grade P X R q d n Q A v L' T t p a h (ζ s) u
    rw [show (L.val:ℤ)*(ζ s)=gaugeShift B (L.val*s:ℤ) from by unfold gaugeShift; ring] at r h'; rw [h']; exact e _ _ r
  have H(k:ℕ)(h:k≤n):E (n-k):=by
    induction k with | zero=>simpa using he | succ k ih=> exact ht (n-(k+1)) (by omega) ((show n-k=n-(k+1)+1 by omega) ▸ ih (by omega))
  exact (show E i from (show n-(n-i)=i by omega) ▸ H (n-i) (Nat.sub_le ..)) z f w_

end YM.CF.Buffered.Afterglow.Journey
