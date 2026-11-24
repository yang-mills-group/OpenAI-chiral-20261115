import YM.SU5.Selected.Compression
import YM.SU5.FiniteGaugeData.Tapestry.Oriflamme
/-!
# The cap itself pays the linear and local gauge laws (on the one Satin history)

The nonfactorization test is on charged tomography, not on a pair of
standalone gauge singlets. Prove the gauge law **on the ground operators**,
before splitting off a vacuum. Use spatial support even without faithfulness
of other estimates. No older estimates on a different history used;
Tapestry provides gauge lemmas on the test objects themselves. `ledgerRule`
used below is on exactly Y,V.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6500
set_option maxHeartbeats 230000
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
variable (j : Axis) (strict : Bool) (C : Arena Y H Q.circuit j 0 strict)
open Tapestry CF.Pannier.Chancel
local notation "A" => Ark.Ht Y H Q.circuit j 0 strict C
local notation "R" => Aurora Y H V Q j strict C
local notation "ℛ" => groundRoom Y H V Q j strict C
local notation "𝒪" => observable (tent Y H) strict
local notation "Λ₀" => ruler Λ.block
local notation "π" => (R).orthogonalProjectionOnto
local notation "ω" => floorV Y H Q.circuit j 0 strict C
local notation "Ω" => seat0 Y H V Q j strict C
local notation "𝔄" => displayAlgebra Y H V Q Qt j strict C
local notation "Λ₁" F:max => Selected.display Y H V s Q Qt j strict C F
local notation "𝒳" t:max => cap Y H V t Q Qt j strict C
local notation "𝔙" t:max => Tower.Field Y H t j 0 strict
local notation "β" f:max p:max => boxOp Y H V s Q Qt j strict C _ f p
local notation "ιₜ" t:max => actor Y H t Q.circuit j 0 strict C

/-- All these helpers are on literal test presentations, no common state
norm needed for the translations. -/
def marksAlgebra (J : Calibration) (strict : Bool) : Subalgebra ℂ (Family J) where
  carrier := {x | TestFamily J true x ∧ (strict = true → CovCover J x)}
  one_mem' := ⟨TestFamily.oneT,fun _ => covariant_one _⟩
  zero_mem' := ⟨TestFamily.zeroT,fun _ => covariant_zero _⟩
  add_mem' := fun h p => ⟨TestFamily.add h.1 p.1, fun t => (covariant_parts J (h.2 t) (p.2 t)).1⟩
  mul_mem' := fun h p => ⟨TestFamily.mul h.1 p.1, fun t => (covariant_parts J (h.2 t) (p.2 t)).2⟩
  algebraMap_mem' z := by
    rw [Algebra.algebraMap_eq_smul_one]; exact ⟨TestFamily.oneT.scale _,fun _ => covariant_scale J (covariant_one _) z⟩
-- avoid introducing instances globally for Vacancy.observable; `Marks` definitionally same.
abbrev Marks (J : Calibration) (strict : Bool) := ↥(marksAlgebra J strict)
lemma marksSpec {J : Calibration} (f : Marks J strict) : TestFamily J true f.val ∧ (strict=true → CovCover J f.val) := f.property
/-- Same shift for Verandas of a full local class. Keeps input support S
(as opposed to e.g. just saying a representative exists in the half-space). -/
lemma plow_up (S : Finset Cover) : ∃ n w : ℕ, 0 < w ∧ Between K j 0 (Λ₀*w) (plow K j n S) := by
  -- from Vacancy.anyporch
  obtain ⟨d,t⟩ := Tower.sizes S; obtain ⟨x,t⟩ := t j
  let n : ℕ := x.natAbs+(K).ℓ+1
  let Z := ruler Λ.block; have ht : 1 ≤ Z := ruler_gene Λ.block
  let k := 2*n+x.natAbs+d
  refine ⟨n,k,by unfold k n; omega,?_⟩
  intro i u; obtain ⟨v,h,rfl⟩ := plow_stays K j n S u; specialize t v h; rw [moves,if_pos rfl]
  change 0+_ ≤ v j+Z*n ∧ v j+Z*n+_ ≤ Z*k
  unfold k n; push_cast; obtain ⟨u,y⟩ := t; have h:(x.natAbs:ℤ)=|x|:= Int.natCast_natAbs x; constructor
  · nlinarith [neg_le_abs x, mul_le_mul_of_nonneg_right ht (show 0 ≤ |x|+ ((K).ℓ:ℕ)+1 by positivity)]
  nlinarith [le_abs_self x, mul_le_mul_of_nonneg_right ht (show 0 ≤ 2* |x|+ ((K).ℓ:ℕ)+(d:ℕ)+1 by positivity)]

/-- Insert in any half-space *with* proof of its support. -/
def enclose {S : Finset Cover} (F : 𝒪) (p : InTest K true S false F.val)
    (n w : ℕ) (h : Between K j 0 (Λ₀*w) (plow K j (n:ℤ) S)) : Entry Y H s j strict w := by
  let W := plow K j (n:ℤ) S
  let f := relocate K j n F.val
  have hf : InTest K true W false f := flow_port K j _ p
  have ht : f ∈ purpose K (meshface (Λ:=Λ) 0 s) j strict :=
    (purpose_ok ..).2 ⟨⟨W,hf,by intro i hi; rw [area0]; exact (h i hi).1⟩,
      fun e => chime_cov K j _ p (F.property.2 e)⟩
  exact ⟨(⟨f,ht⟩ : (𝔙 s)),W,hf,h⟩

local notation "𝔽" => enclose Y H s j strict
lemma cap_posbox {S : Finset Cover} (F : 𝒪) (p : InTest K true S false F.val)
    {n w : ℕ} (h : Between K j 0 (Λ₀*w) (plow K j (n:ℤ) S)) (e : 0 < w) :
    (𝒳 s) F = (π).comp ((β (𝔽 F p n w h) e).comp (R).subtypeL) :=
  onAny Y H V s Q Qt j strict C (⟨n,w,e,𝔽 F p n w h,rfl⟩ : Veranda Y H s j strict F)
lemma cap_posbox_value {S : Finset Cover} (F : 𝒪) (p : InTest K true S false F.val)
    {n w : ℕ} (h : Between K j 0 (Λ₀*w) (plow K j (n:ℤ) S)) (e : 0 < w) :
    ((𝒳 s) F) Ω = π ((ιₜ s) (𝔽 F p n w h).val) := by
  rw [cap_posbox Y H V s Q Qt j strict C F p h e]
  change π ((β (𝔽 F p n w h) e) ω) = _; rw [lays]

-- Use `Marks` preferably. Definitionally equal to `observable` on inputs, may need annot.
def located : Marks (tent Y H) strict →ₗ[ℂ] 𝔄 where
  toFun f := Λ₁ (f : observable _ _)
  map_add' x y := by
    apply display_faithful Y H V Q Qt j strict C
    let p : observable K strict := x
    let q : observable K strict := y
    let t : observable K strict := (show Marks K strict from x+y)
    obtain ⟨S,h⟩ := p.property.1.paid; obtain ⟨T,g⟩ := q.property.1.paid
    let W := S∪T
    have hx : InTest K true W false p.val := h.mono Finset.subset_union_left
    have hy : InTest K true W false q.val := g.mono Finset.subset_union_right
    have ht := (show InTest K true W false t.val from hx.add hy)
    obtain ⟨n,w,k,e⟩ := plow_up Y H j W
    change (𝒳 s) t Ω = (𝒳 s) p Ω + (𝒳 s) q Ω
    rw [cap_posbox_value Y H V s Q Qt j strict C p hx e k, cap_posbox_value Y H V s Q Qt j strict C q hy e k, cap_posbox_value Y H V s Q Qt j strict C t ht e k, show (𝔽 t ht n w e).val = (𝔽 p hx n w e).val + (𝔽 q hy n w e).val from Subtype.ext (chime_plus K j _)]
    change π (arrows Y H V Q.circuit j 0 strict C s (_+_)) = _
    rw [map_add,map_add]; rfl
  map_smul' z x := by
    apply display_faithful Y H V Q Qt j strict C
    let p : observable K strict := x
    let t : observable K strict := (show Marks K strict from z • x)
    obtain ⟨S,h⟩ := p.property.1.paid
    have ht : InTest K true S false t.val := InTest.smul z h
    obtain ⟨n,w,k,e⟩ := plow_up Y H j S
    change (𝒳 s) t Ω = z • ((𝒳 s) p Ω)
    rw [cap_posbox_value Y H V s Q Qt j strict C p h e k, cap_posbox_value Y H V s Q Qt j strict C t ht e k, show (𝔽 t ht n w e).val = z • (𝔽 p h n w e).val from Subtype.ext (chime_scale K j _ z)]
    change π (arrows Y H V Q.circuit j 0 strict C s (z • _)) = _
    rw [map_smul,map_smul]; rfl
lemma located_display (x : Marks K strict) :
    located Y H V s Q Qt j strict C x = Λ₁ (show 𝒪 from x) := rfl
lemma located_one : located Y H V s Q Qt j strict C 1 = 1 := by
  apply display_faithful Y H V Q Qt j strict C
  change (𝒳 s) (actorLabel Y H s j strict (unity Y H j 0 strict s)) Ω = Ω
  rw [cap_plant, ← vacua Y H V]
  exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self Ω

-- separate, even before selecting. gauge purchase on fixed class.
open Haro Tap Cascade Dial Mir Girt Nacre Pastry Phase RP
section circular
variable {Z : Calibration} {S : Finset Cover} {f F : Family Z} {wide b : Bool}
  {W W' : Cover → SU.E}

lemma circle_swap (p : Circular S W f F) (h : ∀ x ∈ S, W' x = W x) :
    Circular S W' f F := by
  intro m g t
  exact p m g fun i v => (t i v).trans (h i v)
lemma circle_still (p : InTest Z true S false F) : Circular S (1:Cover → SU.E) F F := by
  obtain ⟨m,h⟩ := (Buffered.separates Z S).exists
  obtain ⟨F',q,t⟩ := reColor (1:Cover → SU.E) p
  have he (x) := t m (1:Seat (Z.c m) → SU.E) (fun _ _ => rfl) x
  have heq : F = F' := looksLike  (m:=m) ⟨h⟩ p q (funext fun x =>
    (twist (quantU (tradew _ (1:Seat (Z.c m) → SU.E)))).injective ((oneHarmony (F m) x).symm.trans (he x)))
  rwa [←heq] at t
lemma both_colors {T : Finset Cover} {g : Family Z} (p : Circular S W f F)
    (v : InTest Z true T false g) (h : ∀ x ∈ T, x ∉ S) :
    ∃ a : Cover → SU.E, Circular (S ∪ T) a (g*f) (g*F) := by
  let a := fun x => if x ∈ S then W x else 1
  have hF : Circular S a f F := circle_swap p fun _ u => if_pos u
  have hx : Circular T a g g := circle_swap (circle_still v) fun _ u => if_neg (h _ u)
  exact ⟨a, Circular.mul a _ (largerGauge Finset.subset_union_right hx)
    (largerGauge Finset.subset_union_left hF)⟩
lemma circle_mirror (z : ℤ) (p : Circular S W f F) (g : InTest Z wide S b F) :
    Circular (reflectedBox j z S) (reflectGauge j z W) (mirror Z j z f) (mirror Z j z F) := by
  intro n w h
  refine reflectHarmony j z (p n (w ∘ (plane j z).anon _) ?_) (g.support n)
  intro i v
  have he := h _ (show (plane j z).motion i ∈ reflectedBox j z S from
    Finset.mem_image_of_mem _ v)
  have hk : (plane j z).motion ((plane j z).motion i) = i := by
    funext a; by_cases p : j=a <;> simp_all only [fling_move, ↓reduceIte] ; ring
  unfold reflectGauge at he
  change w _ = W i
  simp only [Shape.anno]
  simpa only [Function.comp_apply,hk] using he

lemma circle_move (n : ℤ) (p : Circular S W f F) (g : InTest Z wide S b F) :
    ∃ a : Cover → SU.E, Circular (plow Z j n S) a (relocate Z j n f) (relocate Z j n F) := by
  have ht := circle_mirror j (gaugeT Z n) (circle_mirror j 0 p g) (axial Z j 0 g)
  unfold plow; rw [support_translation,sub_zero] at ht
  exact ⟨_,ht⟩
end circular

include V in
/-- Local gauge change of a future actor does not change the vector, even
with strict=false (all even inputs used), before ground selection. -/
theorem actor_paint {T : Finset Cover} (f g : 𝔙 s)
    (p : InTest K true T false f.val) (q : InTest K true T false g.val)
    (h : Tower.region j (meshface (Λ:=Λ) 0 s) (K).ℓ T) (v : Cover → SU.E)
    (hv : Circular T v f.val g.val) : (ιₜ s) f = (ιₜ s) g := by
  let M := meshface (Λ:=Λ) 0 s
  have he (k : 𝔙 s) : inner ℂ ((ιₜ s) k) ((ιₜ s) f) = inner ℂ ((ιₜ s) k) ((ιₜ s) g) := by
    rw [stems Y H V,stems Y H V]
    obtain ⟨S,t,w⟩ := (show ∃ S : Finset Cover, InTest K true S false k.val ∧
      Tower.region j M (K).ℓ S from ((purpose_ok ..).1 k.property).1)
    let S' := reflectedBox j M S
    let l' := mirror K j M k.val
    let r := axial K j M t
    have hx : Detached Λ l S' T := mirror_detached Λ l w h
    obtain ⟨c,x⟩ := both_colors hv r (show ∀ a ∈ S', a ∉ T from fun a k i => hx a k a i (by simp [Lattice.box_test]; omega))
    exact (Papal.ledgerRule Y H V (T∪S') s).gauge c (l'*f.val) (l'*g.val)
      ((r.mono Finset.subset_union_right).mul (p.mono Finset.subset_union_left))
      ((r.mono Finset.subset_union_right).mul (q.mono Finset.subset_union_left)) x
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜:=ℂ)).mp
  rw [inner_sub_left,inner_sub_right,inner_sub_right,he f,he g]; simp

theorem located_same_paint {S : Finset Cover} (f g : Marks K strict)
    (p : InTest K true S false f.val) (q : InTest K true S false g.val)
    (v : Cover → SU.E) (u : Circular S v f.val g.val) :
    located Y H V s Q Qt j strict C f = located Y H V s Q Qt j strict C g := by
  obtain ⟨n,w,h,e⟩ := plow_up Y H j S
  apply display_faithful Y H V Q Qt j strict C
  change (𝒳 s) f Ω = (𝒳 s) g Ω
  rw [cap_posbox_value Y H V s Q Qt j strict C f p e h, cap_posbox_value Y H V s Q Qt j strict C g q e h]
  apply congrArg π
  obtain ⟨a,ha⟩ := circle_move j n u q
  exact actor_paint Y H V s Q j strict C (𝔽 f p n w e).val (𝔽 g q n w e).val (flow_port K j _ p)
    (flow_port K j _ q) (by intro x hx; rw [area0]; exact (e x hx).1) a ha

variable (C' : Arena Y H Q.circuit j 0 false)
local notation "𝔄'" => displayAlgebra Y H V Q Qt j false C'
variable (c : (displayAlgebra Y H V Q Qt j false C') →⋆ₐ[ℂ] ℂ)
-- for testing Parcel on precisely the proper law; no extension claim off system
-- (the values out there are not used)
def pigmentReading (f : Family K) : ℂ :=
  if h : f ∈ marksAlgebra K false then
    c (located Y H V s Q Qt j false C' (⟨f,h⟩ : Marks K false)) else 0
lemma reads_color (f : Marks K false) : pigmentReading Y H V s Q Qt j C' c f.val =
    c (located Y H V s Q Qt j false C' f) := dif_pos f.property
local notation "ψ" t:max => pigmentReading Y H V t Q Qt j C' c
lemma scopedColor (S : Finset Cover) : Scopes K S (ψ s) := by
  let L := (c.toAlgHom.toLinearMap).comp (located Y H V s Q Qt j false C')
  have mark {f : Family K} (h : InTest K true S false f) : f ∈ marksAlgebra K false :=
    ⟨aux_test h, nofun⟩
  refine ⟨?_,?_,?_,?_⟩
  · have h := reads_color Y H V s Q Qt j C' c 1
    rw [located_one,map_one] at h
    exact h
  · intro x y p q; let a : Marks K false := ⟨x,mark p⟩; let b : Marks K false := ⟨y,mark q⟩
    have he : (ψ s) (x+y) = L (a+b) := reads_color Y H V s Q Qt j C' c (a+b)
    change (ψ s) _ = _ + _
    rw [he,map_add]; exact congrArg₂ (·+·) (reads_color Y H V s Q Qt j C' c a).symm
      (reads_color Y H V s Q Qt j C' c b).symm
  · intro x p z; let a : Marks K false := ⟨x,mark p⟩
    have he : (ψ s) (z • x) = L (z • a) := reads_color Y H V s Q Qt j C' c (z • a)
    change (ψ s) _ = z • _
    rw [he,map_smul]; exact congrArg (z • ·) (reads_color Y H V s Q Qt j C' c a).symm
  intro v x y p q h; let a : Marks K false := ⟨x,mark p⟩; let b : Marks K false := ⟨y,mark q⟩
  change (ψ s) a.val = (ψ s) b.val
  rw [reads_color, reads_color, located_same_paint Y H V s Q Qt j false C' a b p q v h]

end YM.CF.Buffered.Afterglow.Tower.Selected
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.actor_paint
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.located_same_paint
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.scopedColor
