import YM.SU5.Selected.Threshold
import YM.SU5.Selected.Recolor
/-!
# Across two fixed, widely separated physical cells of the resolution hierarchy

Same law as the character and `FixedLink`. Character is a vacuum of ALL resolved
slots/levels (strict later for the physical statement, here consistent using both; in source
itself use the continuous first gauge mark with finite chiral access). We give a further
forward/past **composite mark** with nonvanishing interaction in this law. It spans across
any desired fixed physical separation (even its refinements), hence establishing a further
sense in which our coupling witnesses are not simply shrinking-scale readings losing all
separation. No kinetic normalization is claimed. Mixing traps avoided, see definition of
`Outsider`: an explicit factorization test that would set to zero the reading of the actual
neutral word across both cells. Word basis gauge coefficients translated/reflected in tandem
with the subfactors -- these transports are the same physical gauge-field and Spin assignments,
not assuming a rotated quantum state.

BE PRECISE: interaction in this theorem, as in Sustain/Freeze, is a failure of pure-gauge---matter
factorization in the joint even reading. Here at the two cells jointly. Not claiming a
nonzero *truncated two-point function* between the cells! Similar nonfactorization still
would occur even if the cells were completely clustering away one from the other. Use the
filtered physical support calibration of Freeze. No claim numerical value survives replacing
this pair of marks with smaller cells in their respective regions (though all REPRESENTATIVES
of this pair at higher rungs are guaranteed with the same physical collar, accurate SCM refinement).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6500
set_option maxHeartbeats 310000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Selected
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock Set Vacancy
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
local notation "L₀" => Λ.R.L.val
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E) (s : ℕ)
variable {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b) (Qt : Clipped Y H (i ∘ a) (k ∘ b))
variable (j : Axis) (C : Arena Y H Q.circuit j 0 false)
open Tapestry CF.Pannier.Chancel CF.Pannier.Chancel.Cliplet Py.Rate.Pannier
variable {S : Finset Cover}
variable (c : (displayAlgebra Y H V Q Qt j false C) →⋆ₐ[ℂ] ℂ)
local notation "E'" => pigmentReading Y H V s Q Qt j C c
local notation "D₀" => indoor Y H V Q Qt j false C c
local notation "Χ" n:max => response Y H V n Q Qt j false C c

section finance
/-- Offer pure matter in the shifted positive cell, and test WITH arbitrary spectators physically
supported in the other cell. Use a derived Scopes reader, with its normalization subtraction at
unshifted, testing literally responses on this character. -/
private lemma loses_mater {t : ℕ} (v : ℤ) (P' : Finset Cover)
    (u : Disjoint P' (plow K j v S)) (p : Family K)
    (k : InTest K true P' false p) (q : Fin t→ Cover) (hq : Injective q)
    (z : Window.Family) (x : Family K) (h : x∈Lode K z q S) : E' (p*relocate K j v x)=0 := by
  let X := plow K j v S; let Y' := X∪P'
  let ψ := E'
  let M : Family K→Family K := relocate K j v
  let T (x : Family K) := ψ (p*M x)+(1-ψ p)*ψ x
  have hf := scopedColor Y H V s Q Qt j C c S
  have ht := scopedColor Y H V s Q Qt j C c Y'
  have hz(a:Family K)(p : InTest K true S false a) : InTest K true X false (M a) := flow_port K j (gaugeT K v) p
  have hv(a:Family K)(u : InTest K true S false a) : InTest K true Y' false (p*M a) :=
    (k.mono Finset.subset_union_right).mul ((hz a u).mono Finset.subset_union_left)
  have hs : Scopes K S T := by
    refine ⟨?_,?_,?_,?_⟩
    · unfold T; rw [show M 1=1 from relocate_unit K j v,mul_one,show ψ 1=1 from hf.unit]; ring
    · intro i j' a b; unfold T; rw [show M (i+j')=M i+M j' from chime_plus ..,mul_add]
      unfold ψ; rw [ht.plus_v _ _ (hv _ a) (hv _ b),hf.plus_v _ _ a b]; ring
    · intro i a c'; unfold T; rw [show M (c' • i)= c' • M i from chime_scale ..,Algebra.mul_smul_comm]
      unfold ψ; rw [ht.scale _ (hv _ a) c', hf.scale _ a c']; simp only [smul_eq_mul]; ring
    intro x f F a t h
    obtain ⟨a',y⟩ := circle_move j v h t
    obtain ⟨a0,H₁⟩ := both_colors y k (Finset.disjoint_left.mp u)
    unfold T ψ; rw [ht.gauge a0 _ _ (hv _ a) (hv _ t) H₁,hf.gauge _ _ _ a t h]
  have he := hs.footprint hq h; unfold T ψ at he; rwa [hf.footprint hq h,mul_zero,add_zero] at he

variable (J : Calibration)
/-- joint two-cell experiment. formula can freeze copies of translated mark centered observations;
`p` is DIST to plane in tower cells. -/
noncomputable def polar (p : ℤ) (x y : Family J) : Family J := mirror J j 0 (relocate J j p x) * relocate J j p y
variable (p : ℤ)
local notation "P" => polar j (tent Y H) p
local notation "X₀" => plow (tent Y H) j p S
local notation "X₁" => reflectedBox j 0 X₀
local notation "X₂" => X₀ ∪ X₁

private lemma polarized {a b:Family K} (u : InTest K true S false a) (v : InTest K true S false b) :
    InTest K true X₂ false (polar j K p a b) :=
  (((axial K j 0 (flow_port K j (gaugeT K p) u))).mono Finset.subset_union_right).mul ((flow_port K j (gaugeT K p) v).mono Finset.subset_union_left)

/-- Factorization demand in the simultaneous mixed witness class. Tests just basis matters
with **transported** gauge coefficients (narrow). In particular no auxiliary gauge in the test,
matter at POINT presentations touching no wrong contact at source, and gauge 'pure' part has no
Grassmann dependence, pure matter subinputs built from chiral letters/same deformation at their
stated slots, projectively transported by the same translations and mirrors (and therefore without
gauge links). Entire word tested in the same selected extension. -/
def Outsider (S : Finset Cover){i : ℕ}(v : Fin i → Cover) (W : Window.Family) (x : Family J→ℂ) : Prop :=
  ∀ f∈ Lode J W v S,∀ g∈ Lode J W v S,∀ F F' : PairsC→ℂ,Coeff false S F→ Coeff false S F'→
    x (polar j J p (scalar J F*f) (scalar J F'*g)) = x (polar j J p (scalar J F) (scalar J F')) * x (polar j J p f g)
/-- A proposed split of the gauge and matter factors would satisfy Outsider: confirm equality on
polar multiplication (so factorization has its intended operational meaning). -/
lemma polar_factors {a b : Family J} {A B : Family J}
    (u : TestFamily J true b) (v : TestFamily J true A) :
    polar j J p (a*b) (A*B)=polar j J p a A * polar j J p b B := by
  unfold polar; rw [relocate_mul,relocate_mul, mirror_times]
  simp only [mul_assoc]; apply congrArg (mirror J j 0 (relocate J j p a) * ·)
  rw [← mul_assoc, ←mul_assoc, even_tests J (reflect_ok J j 0 (move_ok J j p u)) (move_ok J j p v)]

-- Witness theorem even with **different** inputs (may help non-polar timing later).
lemma polar_price {k : ℕ}{z : Fin k→ Cover}{W : Window.Family}
    (u : Disjoint X₁ X₀) (v : Injective z) (t : Outsider j K p S z W E')
    {x y : Family K} (p1 : x∈Filigree K W z S) (p2 : y∈ Filigree K W z S) : E' (polar j K p x y)=0 := by
  let Φ:= E'; let B:= Filigree K W z S; let Λ₀ := scopedColor Y H V s Q Qt j C c X₂
  have Q₀{f g:Family K}(u:f∈B)(v:g∈B) : InTest K true X₂ false (P f g) :=
    polarized Y H j p (FilTest (S:=S) (W:=W) (b:=z) u|>.widen) (FilTest (W:=W) (b:=z) v|>.widen)
  -- submodule span induction; enumerate basis generators explicitly
  apply Submodule.span_induction₂ (R:=ℂ) (p:=fun x y _ _=> Φ (P x y)=0) _ _ _ _ _ _ _ p1 p2
  · intro x y a b
    obtain ⟨f,z',m,n,he⟩ := a; obtain ⟨g,F,t',δ,h⟩ := b
    
    have hg:= loses_mater Y H V s Q Qt j C c p X₁ u (mirror K j 0 (relocate K j p f)) (axial K j 0 (flow_port K j _ ((Lode_test (S:=S) (W:=W) (b:=z) m).widen))) z v W g t'
    unfold Φ; rw [he,h,t _ m _ t' z' F n δ]; exact (show _ from by rw [show E' (P f g) =0 from hg,mul_zero])
  · intro _ _; rw [show P 0 _=0 from ?_]; exact Λ₀.nil_v
    unfold polar relocate; -- use lemmas
    rw [chime_zeroY K j, mirror_zeroY K j, zero_mul]
  · intro _ _; rw [show P _ 0=0 from ?_]; exact Λ₀.nil_v
    unfold polar relocate; rw [chime_zeroY K j, mul_zero]
  · intro x y z' a b t hx1 hy1; rw [show P (x+y) z'=P x z'+P y z' from ?_];
    · rw [(show Φ _=Φ _+Φ _ from Λ₀.plus_v _ _ (Q₀ a t) (Q₀ b t)),hx1,hy1,add_zero] -- beware rewrite timeout
    unfold polar relocate; rw [chime_plus,mirror_plus, add_mul]
  · intro x y z' a b t hx1 hy1; rw [show P x (y+z')=P x y+P x z' from ?_];
    · rw [(show Φ _=Φ _+Φ _ from Λ₀.plus_v _ _ (Q₀ a b) (Q₀ a t)),hx1,hy1,add_zero]
    unfold polar relocate; rw [chime_plus,mul_add]
  · intro a x y v w p1; rw [show P (a • x) y=star a • P x y from ?_]; swap; · unfold polar relocate; rw [chime_scale,mirror_scale,Algebra.smul_mul_assoc]
    rw [show Φ _=_ from Λ₀.scale _ (Q₀ v w) (star a),show E' _=0 from p1,smul_zero]
  intro a x y v w p1; rw [show P x (a • y)=a • P x y from ?_]; swap; · unfold polar relocate; rw [chime_scale,Algebra.mul_smul_comm]
  rw [show Φ _=_ from Λ₀.scale _ (Q₀ v w) a,show E' _=0 from p1,smul_zero]
where
 chime_zeroY (J₀ : Calibration)(j : Axis)(z:ℤ) : chime J₀ j z 0=0 := by simpa only [zero_smul] using chime_scale J₀ j z (F:=1) (0:ℂ)
 mirror_zeroY (J₀ : Calibration)(j : Axis)(z:ℤ) : mirror J₀ j z 0=0 := by simpa only [star_zero,zero_smul] using mirror_scale J₀ j z (F:=1) (0:ℂ) -- order?
end finance

section twin
local notation "res" => reserve Λ l
local notation "ρ" => ruler Λ.block
local notation "σ" t:max => gaugeMesh Λ t
local notation "P₀" s:max i:max=> gaugePosition Λ s i j
local notation "A₀" => Ark.Ht Y H Q.circuit j 0 false C
/-- Hygienic space larger than δ between any source points (also even arbitrary refined points
of their stencil with their own buffer). -/
def PhysicalHush (S T : Finset Cover) (δ : ℝ) : Prop := 0 < δ ∧ ∀ (v : ℕ) (x:Cover), x∈volumeAround Λ l v S→
    ∀ y∈ volumeAround Λ l v T, P₀ (s+v) x + ((reserve Λ l:ℕ):ℝ)* σ (s+v) + δ ≤ P₀ (s+v) y - ((reserve Λ l:ℕ):ℝ)* σ (s+v)
private lemma plow_seq (n t : ℕ) : plow K j (↑t:ℤ) (plow K j (↑n:ℤ) S) = plow K j (t+n:ℕ) S := by
  unfold plow address; push_cast; rw [Finset.image_image]; congr 1; funext v; rw [gaugeT_add, mul_add,add_smul]; unfold Function.comp; abel_nf; try exact add_assoc _ _ _
variable (S) -- make explicit

local notation "B" n:max => plow K j (n:ℤ) S
local notation "B'" n:max => reflectedBox j 0 (B n)
private lemma arrange_up {δ : ℝ} (d : 0<δ) : ∃ u w : ℕ, 0 < w ∧ Between (tent Y H) j 0 (ρ*w) (plow (tent Y H) j (u:ℤ) S) ∧
    PhysicalHush (Λ:=Λ) (l:=l) s j (reflectedBox j 0 (plow (tent Y H) j (u:ℤ) S)) (plow (tent Y H) j (u:ℤ) S) δ := by
  obtain ⟨n,w,t,h⟩ := plow_up Y H j S
  obtain ⟨z,u⟩ := exists_nat_gt (δ/(gaugeMesh Λ s))
  have hρ : 1 ≤ ruler Λ.block := ruler_gene Λ.block
  have ht := h.relocate K j z
  rw [add_zero,plow_seq Y H j] at ht
  let i := z+n
  let S':= B i; let T:= B' i; have hr : 0 < z+w := by omega
  have hu:0≤ ρ*(z:ℤ):= mul_nonneg (by omega) (by positivity)
  refine ⟨i,z+w,hr, fun i p=>?_ , d,?_⟩
  · obtain ⟨x,g⟩ := ht i p
    push_cast
    rw [mul_add]; exact ⟨le_trans (by omega : 0+((K).ℓ:ℤ) ≤ ruler Λ.block*z+((K).ℓ:ℤ)) x,g⟩
  have hδ : δ ≤ z*(σ s) := ((div_lt_iff₀ (gaugeMesh_pos Λ s)).1 u).le
  have hb {x} (t : x∈ S') : (res:ℝ)*(σ s)+δ ≤ P₀ s x := by
    have hg : (z:ℤ) ≤ ρ*(z:ℤ) := le_mul_of_one_le_left (by positivity) hρ
    have hx : (ruler Λ.block*(z:ℤ))+(res:ℤ) ≤ x j := (ht x t).1 -- xj dummy
    have he : (z:ℝ)+(res:ℝ)≤ (x j:ℝ) := by exact_mod_cast le_trans (add_le_add_left hg (res:ℤ)) hx
    apply le_trans (show (res:ℝ)*(σ s)+δ ≤ (z+(res:ℝ))*(σ s) from by rw [add_mul]; linarith)
    exact mul_le_mul_of_nonneg_right he (gaugeMesh_pos ..).le
  intro v x fx y gy
  obtain ⟨X,V,hX⟩ := physical_shield Λ l s T v fx; obtain ⟨Z,vZ,hZ⟩ := physical_shield Λ l s S' v gy
  obtain ⟨x',Hp,t⟩ := reflect_stays j 0 S' V
  have he:P₀ s X= -(P₀ s x') := by unfold gaugePosition; rw [t]; simp
  calc _ ≤ P₀ s X + (res:ℝ)*(σ s)+δ := by linarith only [le_abs_self (P₀ (s+v) x-P₀ s X), hX j]
       _ ≤ P₀ s Z - (res:ℝ)*(σ s) := by linarith only [he,hb Hp,hb vZ,d]
       _ ≤ _ := by linarith only [neg_le_abs (P₀ (s+v) y-P₀ s Z), hZ j]

variable (p : ℕ) (F : observable (tent Y H) true)
noncomputable def shiftUp (p : ℕ) (x : Marks (tent Y H) true) := moveMark Y H j true p x
-- pay entire joint word, not just its center copies
local notation "Z" p:max f:max=> shiftUp Y H j p f
local notation "W" x:max => mirrorInMarks Y H j true x
local notation "Ω₀" => doorstep Y H V Q Qt j false C c
local notation "F₊" => Z p F
local notation "F₋" => W (Z p F)
local notation "Pp" => polar j K (p:ℤ)
local notation "tw" => (F₋)*(F₊)
local notation "𝔙" t:max => Tower.Field Y H t j 0 false
local notation "X" => B p
local notation "G" => B' p
variable {q d w : ℕ} {z : SU.Slot} {o : Cover}

include c V Qt
/-- Turn a survivor into a pair right at its fixed level. Pay uniform claims at its further
levels too, to emphasize it already gives physical-separation nonloss in this state. -/
theorem further_pair {δ : ℝ} (v : Between K j 0 (ρ*w) (B p)) (hw : 0 < w)
    (d0 : PhysicalHush (Λ:=Λ) (l:=l) s j (B' p) (B p) δ)
    (u : Survivor Y H V s Q Qt j C z o q d S F c) :
    Detached Λ l (B' p) (B p) ∧
      (∀ n : ℕ, (stream Y H D s n (polar j (tent Y H) p F.val F.val)) =
        stream Y H D s n (mirror (tent Y H) j 0 (relocate (tent Y H) j p F.val))*stream Y H D s n (relocate (tent Y H) j p F.val)) ∧
      (∀ n : ℕ, (upward Y H Q true (F₋) s n).val∈ observ (tent Y H) (volumeAround Λ l n (B' p)) true ∧
        (upward Y H Q true (F₊) s n).val∈ observ (tent Y H) (volumeAround Λ l n (B p)) true) ∧
      (∀ n : ℕ, 1/16 ≤ ‖(Χ (s+n)) (bosonLabel K (upward Y H Q true (tw) s n))‖ ∧
        1/16 ≤ ‖E (s+n) (upward Y H Q true (tw) s n).val‖) ∧
      PhysicalHush (Λ:=Λ) (l:=l) s j (B' p) (B p) δ ∧
      ¬ Outsider j K p S (booty o d q) (Window.family z) E' := by
  let f := bosonLabel K F; let T':= bosonLabel K (tw)
  have h := (FilTest u.link.mark_mem).widen
  have hx := flow_port K j (gaugeT K p) h; have hy := axial K j 0 hx
  let t := mirror_detached Λ l (show Tower.region j 0 (reserve Λ l) (B p) from fun x h=> (v x h).1) (fun x h=> (v x h).1)
  let x := (enclose Y H s j false f h p w v).val; let y := bud Y H V s Q Qt j false C c x
  have ht : (Χ s) T'=inner ℂ y y := (earns Y H V s Q Qt j false C c x x).symm
  have he(v:Hilbert)(x:v) (ω:v)(q : ‖ω‖=1) (r : 1/4≤‖inner ℂ ω x‖) : 1/16≤ ‖inner ℂ x x‖ := by
    have hu:= norm_inner_le_norm ω x (𝕜:=ℂ);
    rw [q,one_mul] at hu; rw [inner_self_eq_norm_sq_to_K]; change _≤ ‖((‖x‖:ℂ)^2)‖; rw [norm_pow,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
    nlinarith only [r,hu,norm_nonneg x]
  have hf : 1/16 ≤ ‖(Χ s) T'‖ := by
    rw [ht]; refine he (D₀) y Ω₀ (ready Y H V Q Qt j false C c) ?_; unfold y
    rw [call]; change _ ≤ ‖(Χ s) (moveMark Y H j false p f)‖; rw [waiting]; exact u.responds
  have hb : 1/16≤ ‖E s T'.val‖ := by
    let y:= actor Y H s Q.circuit j 0 false C x; let Ω:=floorV Y H Q.circuit j 0 false C
    have h₀ : E s T'.val=inner ℂ y y := by unfold y; rw [stems Y H V,area0]; rfl
    rw [h₀]; refine he (A₀) y Ω (vane Y H V Q.circuit j 0 false C) ?_
    unfold Ω y; rw [locates Y H V s Q Qt j false C w hw]
    change _≤ ‖E s (chime K j (Heat.gaugeShift Λ.block (2*p)) F.val)‖; rw [SWay Y H V s j _ (aux_test h)]; exact u.link.mixed
  refine ⟨t,fun n=> woven_product Y H Q.circuit s n hy hx t,fun n=> ?_,fun n=>?_,d0,?_⟩
  · exact ⟨chroma Y H Q.circuit s n ((obs_in ..).2 ⟨hy,(marksSpec true (F₋)).2 rfl⟩),chroma Y H Q.circuit s n ((obs_in ..).2 ⟨hx,(marksSpec true (F₊)).2 rfl⟩)⟩
  · have hh := moves_up Y H V s Q Qt j false C c T' n
    have h1 : (Χ (s+n)) (bosonLabel K (upward Y H Q true (tw) s n))=(Χ s) T':=hh
    rw [h1]; exact ⟨hf, hb.trans_eq (congrArg norm ((proceeds Y H Q.circuit s n (polarized Y H j (p:ℤ) h h)).2.symm))⟩
  intro w; let g' := E' T'.val; have hx := polar_price Y H V s Q Qt j C c (p:ℤ) (detached_disjoint t) u.link.anchor_inj w u.link.mark_mem u.link.mark_mem
  have ht : (Χ s) T'=0 := (reads_color Y H V s Q Qt j C c (show Marks K false from T')).symm.trans hx
  rw [ht,norm_zero] at hf; norm_num at hf
-- always choose this δ positive (any specified).
lemma tour_plan (δ : ℝ) (d : 0<δ) : ∃ u w : ℕ, 0 < w ∧ Between K j 0 (ρ*w) (plow K j (u:ℤ) S) ∧ PhysicalHush (Λ:=Λ) (l:=l) s j (reflectedBox j 0 (plow K j u S)) (plow K j u S) δ := arrange_up Y H s j S d
end twin
end YM.CF.Buffered.Afterglow.Tower.Selected
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.further_pair
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.tour_plan
