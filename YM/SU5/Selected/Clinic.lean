import YM.SU5.Selected.Longitude
/-!
# Linear coupling at arbitrary displacement. Adapted from Distant (tandem broad transformation), at two fixed, widely separated physical cells of the resolution hierarchy

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

section clinic
variable (J : Calibration) (p : Cover) (n : Cover) -- arbitrary
/-! Displace-full grade world checks. -/

def drivePlot (v : Cover) (J : Calibration) (l : List Axis) (S : Finset Cover) := l.foldr (fun i e=> plow J i (v i) e) S
abbrev streetBox (J : Calibration) (v : Cover)(S : Finset Cover) := drivePlot v J ordinate S
lemma cad_test {J: Calibration} (t : List Axis) {x : Family J} (u : InTest J true S false x): InTest J true (drivePlot n J t S) false (cad J t n x) := by
  induction t with | nil=>exact u | cons i t ih=> exact flow_port _ _ _ ih
lemma cad_unit (t:List Axis) : cad J t p 1=1 := by induction t with | nil=>rfl | cons i t ih=>rw [cad_step,ih,relocate_unit]
lemma cad_part (t:List Axis) (x y : Family J): cad J t p (x+y)=cad J t p x+cad J t p y := by
  induction t with | nil=> rfl | cons i t ih=> rw [cad_step,cad_step,cad_step,ih]; exact chime_plus ..
lemma cad_scale (t:List Axis) (x : Family J) (z:ℂ) : cad J t p (z•x)=z•cad J t p x := by
  induction t with | nil=> rfl | cons i t ih=> rw [cad_step,cad_step,ih]; exact chime_scale ..
lemma cad_circle {J:Calibration} {f g:Family J}{W: Cover→ SU.E}(t : List Axis)(u : InTest J true S false g)
    (h : Tapestry.Circular S W f g): ∃ W' : Cover → SU.E, Tapestry.Circular (drivePlot n J t S) W' (cad J t n f) (cad J t n g) := by
  induction t with
  | nil=> exact ⟨W,h⟩
  | cons i t ih=>
     obtain ⟨w,q⟩:= ih; exact circle_move i (n i) q (cad_test n t u)

lemma remote_cold {t : ℕ} (v : Cover) (P' : Finset Cover)
    (u : Disjoint P' (streetBox K v S)) (p : Family K)
    (k : InTest K true P' false p) (q : Fin t→ Cover) (hq : Injective q)
    (z : Window.Family) (x : Family K) (h : x∈Lode K z q S) : E' (p*Vacancy.chart K v x)=0 := by
  let X := streetBox K v S; let Y' := X∪P'
  let ψ := E'
  let M : Family K→Family K := Vacancy.chart K v
  let T (x : Family K) := ψ (p*M x)+(1-ψ p)*ψ x
  have hf := scopedColor Y H V s Q Qt j C c S
  have ht := scopedColor Y H V s Q Qt j C c Y'
  have hz(a:Family K)(p : InTest K true S false a) : InTest K true X false (M a) := cad_test v _ p
  have hv(a:Family K)(u : InTest K true S false a) : InTest K true Y' false (p*M a) :=
    (k.mono Finset.subset_union_right).mul ((hz a u).mono Finset.subset_union_left)
  have hs : Scopes K S T := by
    refine ⟨?_,?_,?_,?_⟩
    · unfold T; rw [show M 1=1 from cad_unit K v _,mul_one,show ψ 1=1 from hf.unit]; ring
    · intro i j' a b; unfold T; rw [show M (i+j')=M i+M j' from cad_part ..,mul_add]
      unfold ψ; rw [ht.plus_v _ _ (hv _ a) (hv _ b),hf.plus_v _ _ a b]; ring
    · intro i a c'; unfold T; rw [show M (c' • i)= c' • M i from cad_scale ..,Algebra.mul_smul_comm]
      unfold ψ; rw [ht.scale _ (hv _ a) c', hf.scale _ a c']; simp only [smul_eq_mul]; ring
    intro x f F a t h
    obtain ⟨a',y⟩ := cad_circle v ordinate t h
    obtain ⟨a0,H₁⟩ := both_colors y k (Finset.disjoint_left.mp u)
    unfold T ψ; rw [ht.gauge a0 _ _ (hv _ a) (hv _ t) H₁,hf.gauge _ _ _ a t h]
  have he := hs.footprint hq h; unfold T ψ at he; rwa [hf.footprint hq h,mul_zero,add_zero] at he

noncomputable def remotePair (p n : Cover) (x y : Family J) : Family J := mirror J j 0 (cad J ordinate p x) * cad J ordinate n y
variable (p n : Cover)
local notation "P" => remotePair j (tent Y H) p n
local notation "X₀" => streetBox (tent Y H) n S
local notation "X₁" => reflectedBox j 0 (streetBox K p S)
local notation "X₂" => X₀ ∪ X₁

private lemma remotePairized {a b:Family K} (u : InTest K true S false a) (v : InTest K true S false b) :
    InTest K true X₂ false (remotePair j K p n a b) :=
  (((axial K j 0 (cad_test p _ u))).mono Finset.subset_union_right).mul ((cad_test n _ v).mono Finset.subset_union_left)

/-- Factorization demand in the simultaneous mixed witness class. Tests just basis matters
with **transported** gauge coefficients (narrow). In particular no auxiliary gauge in the test,
matter at POINT presentations touching no wrong contact at source, and gauge 'pure' part has no
Grassmann dependence, pure matter subinputs built from chiral letters/same deformation at their
stated slots, projectively transported by the same translations and mirrors (and therefore without
gauge links). Entire word tested in the same selected extension. -/
def RemoteSplit (S : Finset Cover){i : ℕ}(v : Fin i → Cover) (W : Window.Family) (x : Family J→ℂ) : Prop :=
  ∀ f∈ Lode J W v S,∀ g∈ Lode J W v S,∀ F F' : PairsC→ℂ,Coeff false S F→ Coeff false S F'→
    x (remotePair j J p n (scalar J F*f) (scalar J F'*g)) = x (remotePair j J p n (scalar J F) (scalar J F')) * x (remotePair j J p n f g)
/-- A proposed split of the gauge and matter factors would satisfy RemoteSplit: confirm equality on
remotePair multiplication (so factorization has its intended operational meaning). -/
lemma remotePair_factors {a b : Family J} {A B : Family J}
    (u : TestFamily J true b) (v : TestFamily J true A) :
    remotePair j J p n (a*b) (A*B)=remotePair j J p n a A * remotePair j J p n b B := by
  unfold remotePair; rw [cad_prod,cad_prod, mirror_times]
  simp only [mul_assoc]; apply congrArg (mirror J j 0 (cad J ordinate p a) * ·)
  rw [← mul_assoc, ←mul_assoc, even_tests J (reflect_ok J j 0 (cad_paid J ordinate u p)) (cad_paid J ordinate v n)]

-- Witness theorem even with **different** inputs (may help non-remotePair timing later).
lemma remotePair_price {k : ℕ}{z : Fin k→ Cover}{W : Window.Family}
    (u : Disjoint X₁ X₀) (v : Injective z) (t : RemoteSplit j K p n S z W E')
    {x y : Family K} (p1 : x∈Filigree K W z S) (p2 : y∈ Filigree K W z S) : E' (remotePair j K p n x y)=0 := by
  let Φ:= E'; let B:= Filigree K W z S; let Λ₀ := scopedColor Y H V s Q Qt j C c X₂
  have Q₀{f g:Family K}(u:f∈B)(v:g∈B) : InTest K true X₂ false (P f g) :=
    remotePairized Y H j p n (FilTest (S:=S) (W:=W) (b:=z) u|>.widen) (FilTest (W:=W) (b:=z) v|>.widen)
  -- submodule span induction; enumerate basis generators explicitly
  apply Submodule.span_induction₂ (R:=ℂ) (p:=fun x y _ _=> Φ (P x y)=0) _ _ _ _ _ _ _ p1 p2
  · intro x y a b
    obtain ⟨f,z',m,n',he⟩ := a; obtain ⟨g,F,t',δ,h⟩ := b
    
    have hg:= remote_cold Y H V s Q Qt j C c n X₁ u (mirror K j 0 (cad K ordinate p f)) (axial K j 0 (cad_test p _ ((Lode_test (S:=S) (W:=W) (b:=z) m).widen))) z v W g t'
    unfold Φ; rw [he,h,t _ m _ t' z' F n' δ]; exact (show _ from by rw [show E' (P f g) =0 from hg,mul_zero])
  · intro _ _; rw [show P 0 _=0 from ?_]; exact Λ₀.nil_v
    unfold remotePair; -- use lemmas
    rw [chart_zeroY, mirror_zeroY K j, zero_mul]
  · intro _ _; rw [show P _ 0=0 from ?_]; exact Λ₀.nil_v
    unfold remotePair; rw [chart_zeroY, mul_zero]
  · intro x y z' a b t hx1 hy1; rw [show P (x+y) z'=P x z'+P y z' from ?_];
    · rw [(show Φ _=Φ _+Φ _ from Λ₀.plus_v _ _ (Q₀ a t) (Q₀ b t)),hx1,hy1,add_zero] -- beware rewrite timeout
    unfold remotePair; rw [cad_part,mirror_plus, add_mul]
  · intro x y z' a b t hx1 hy1; rw [show P x (y+z')=P x y+P x z' from ?_];
    · rw [(show Φ _=Φ _+Φ _ from Λ₀.plus_v _ _ (Q₀ a b) (Q₀ a t)),hx1,hy1,add_zero]
    unfold remotePair; rw [cad_part,mul_add]
  · intro a x y v w p1; rw [show P (a • x) y=star a • P x y from ?_]; swap; · unfold remotePair; rw [cad_scale,mirror_scale,Algebra.smul_mul_assoc]
    rw [show Φ _=_ from Λ₀.scale _ (Q₀ v w) (star a),show E' _=0 from p1,smul_zero]
  intro a x y v w p1; rw [show P x (a • y)=a • P x y from ?_]; swap; · unfold remotePair; rw [cad_scale,Algebra.mul_smul_comm]
  rw [show Φ _=_ from Λ₀.scale _ (Q₀ v w) a,show E' _=0 from p1,smul_zero]
where
 chart_zeroY (J₀:Calibration) (v:Cover): cad J₀ ordinate v 0=0 :=by simpa only [zero_smul] using cad_scale J₀ v ordinate 1 (0:ℂ)
 mirror_zeroY (J₀ : Calibration)(j : Axis)(z:ℤ) : mirror J₀ j z 0=0 := by simpa only [star_zero,zero_smul] using mirror_scale J₀ j z (F:=1) (0:ℂ) -- order?
end clinic
end YM.CF.Buffered.Afterglow.Tower.Selected
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.remotePair_price
