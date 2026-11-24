import YM.SU5.Selected.Gather
import YM.SU5.Selected.Threshold
/-!
# Reserved, the physical gauge-invariant system is determining throughout selection

These are EXACT identities of operators on the whole OS space. The strict
marked Entry operators (acting on the loose arena H with no assumption about
physical density there a priori) attain each loose one, hence generate the
same C* algebra when allowing arbitrary resolutions. Check also the support
budget: only pay one extra level of refinement for any specific request. We
retain all local neutral marks, not just a weaker claim to clustering products.
Do not need to quotient the whole loose algebra, e.g. there could be effects
when multiplying loose tests next to a neighbor before preparing an Entry.
Prove responses to all local arguments are obtainable from neutral marks even
without time-shape, and with no independent continuation prescription.

Not asserting Minkowski interpretation of this system of insertions. For
instance, the slab operators here aren't claimed to be generating an isotonic
*spacetime* net. This is a determining resolution algebra (supported in
physical coordinates, no sending the observes to lattice zero), usable for
continuum reconstruction problems hereafter.
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
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock Set Vacancy
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
local notation "L₀" => Λ.R.L.val
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E) (s : ℕ)
variable {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b) (Qt : Clipped Y H (i ∘ a) (k ∘ b))
variable (j : Axis) (C : Arena Y H Q.circuit j 0 false)
open Tapestry _root_.YM.SelectionAnalysis CF.Pannier.Chancel
variable (S : Finset Cover)
local notation "𝔄" => Ark.Ht Y H Q.circuit j 0 false C
local notation "ℛ" => Aurora Y H V Q j false C
local notation "R₀" => groundRoom Y H V Q j false C
local notation "𝔅" => driveAlgebra Y H V Q Qt j false C
local notation "A" => displayAlgebra Y H V Q Qt j false C
local notation "ω₀" => floorV Y H Q.circuit j 0 false C
local notation "π" => (ℛ).orthogonalProjectionOnto
local notation "Ω₀" => seat0 Y H V Q j false C
local notation "qv" s:max i:max x:max => entrance Y H V s Q Qt j false C i x
local notation "P₁" t:max => actor Y H t Q.circuit j 0 false C
local notation "σ" => ruler Λ.block
local notation "Ρ" x:max => indoor Y H V Q Qt j false C x
local notation "κ₀" f:max t:max x:max => bud Y H V t Q Qt j false C f x

section rise
local notation "X" => Swatch S
local notation "Λ₀" => fitting Y H false S
/-- All Swatch S fits loose. A continuous linear passport both for box creation
and later comparisons. -/
noncomputable def passport : Swatch S →L[ℂ] fitting Y H false S := by
  let a (x : X) : Λ₀ := ⟨x, (show render S K x∈ marksAlgebra K false from ⟨aux_test (texture ..),nofun⟩)⟩
  exact { toFun := a
          map_add' _ _ := rfl
          map_smul' _ _ := rfl
          cont := (continuous_id («X»:=Swatch S)).subtype_mk _ }
noncomputable def labelL : Swatch S →ₗ[ℂ] Marks (tent Y H) false where
  toFun x := ⟨render S K x, fitsMarks Y H false S (passport Y H S x)⟩
  map_add' _ _ := Subtype.ext (map_add ..)
  map_smul' _ _ := Subtype.ext (map_smul ..)

noncomputable def paletteT {w : ℕ} (p : Between K j 0 (σ*w) S) (x : Swatch S) :
    Entry Y H s j false w := patron Y H s j false S p (passport Y H S x)
local notation "P" t:max u:max p:max x:max => paletteT Y H t j u p x
lemma palette_val {w : ℕ} (p : Between K j 0 (σ*w) S) (x : Swatch S) :
    (P s S p x).val.val=render S K x := rfl
variable {w : ℕ} (p : Between (tent Y H) j 0 (ruler Λ.block * w) S) (v : 0<w)
noncomputable def coat_of_arms : Swatch S →L[ℂ] (Ark.Ht Y H Q.circuit j 0 false C).Op :=
 ((show _ →L[ℂ] (𝔄).Op from ⟨shellLinear Y H V s Q Qt j false C S p v,shell_cont Y H V s Q Qt j false C S p v⟩).comp (passport Y H S))
lemma coat_dresses (x : Swatch S) : coat_of_arms Y H V s Q Qt j C S p v x = (qv s (P s S p x) v).val := rfl
local notation "Z" x:max m:max => sigil S m (tent Y H) x
lemma club_coup (x : Swatch S) (m : Side) (h : Integrable (fun u=> coup S m (tent Y H) u x) (domeLaw ((tent Y H).c m))) :
    qv s (P s S p (Z x m)) v = qv s (P s S p x) v := by
  let L := coat_of_arms Y H V s Q Qt j C S p v
  let U₀ := fun u : Zodiac ((tent Y H).c m) => L (coup S m (tent Y H) u x)
  have he : U₀=(fun _ => L x) := by
    funext u; dsimp only [U₀]
    unfold L; rw [coat_dresses,coat_dresses]
    refine (congrArg (fun z : (driveAlgebra Y H V Q Qt j false C) => z.val) ?_)
    apply Eq.symm
    apply color_slab Y H V s Q Qt j false C v (P s S p x) (paletteT Y H s j S p (coup S m K u x)) _ _ p (u ∘ wrap _)
    · rw [palette_val, palette_val]; exact coup_local S m K u x
    · rw [palette_val]; exact texture ..
    rw [palette_val]; exact texture ..
  apply Subtype.ext; change L (Z x m) = L x; unfold sigil
  refine (ContinuousLinearMap.integral_comp_comm (E:=Swatch S) (Fₗ:=(𝔄).Op) (𝕜:=ℂ) L h).symm.trans ?_
  change (∫ u,U₀ u ∂domeLaw ((tent Y H).c m))=L x
  rw [he]; simp

/-- Also on cap. We verify this ON ANY support / rung, not just on the box operators
whose clock is legal. -/
noncomputable def usher (S : Finset Cover) (n : ℤ) : Swatch S →ₗ[ℂ] Swatch (plow (tent Y H) j n S) where
  toFun x := fabric _ (tent Y H) (flow_port (tent Y H) j (gaugeT (tent Y H) n) (texture S (tent Y H) x)) -- tune target notation plow
  map_add' x y := by apply Tapestry.render_inj (plow (tent Y H) j n S) (tent Y H); rw [map_add (render (plow K j n S) K),render_fabric,render_fabric,render_fabric,map_add,chime_plus] -- `render_fabric` `flow_port` col support defeq address/plow ?
  map_smul' a x := by apply Tapestry.render_inj (plow (tent Y H) j n S) (tent Y H); rw [map_smul (render (plow K j n S) K),render_fabric,render_fabric,map_smul,chime_scale]; rfl
local notation "H₀" n:max => plow (tent Y H) j n S
lemma ushers (n : ℤ) (x : Swatch S) : render (plow (tent Y H) j n S) (tent Y H) (usher Y H j S n x) = relocate (tent Y H) j n (render S (tent Y H) x) := render_fabric (plow K j n S) K (flow_port K j (gaugeT K n) (texture S K x))
lemma usher_cont (n : ℤ) : Continuous (usher Y H j S n) := by
  apply AddMonoidHomClass.continuous_of_bound _ (spread S); intro x
  obtain ⟨m,h⟩ := (Buffered.separates (tent Y H) (H₀ n)).exists
  apply sampling (H₀ n) K m ⟨h⟩; intro v; rw [← appearRender, ushers]; exact chime_pay K j (gaugeT K n) (spread S * ‖x‖) (F:=render S K x) (fun m u=> renderLe ..) m v

lemma cap_fee : Continuous (fun x : Swatch S => (located Y H V s Q Qt j false C (labelL Y H S x)).val) := by
  obtain ⟨n,w,k',h⟩ := plow_up Y H j S; let f := coat_of_arms Y H V s Q Qt j C (H₀ (n:ℤ)) h k'; let V' := usher Y H j S n
  let X₁ := compress Y H V Q j false C
  have he (x : Swatch S) : (located Y H V s Q Qt j false C (labelL Y H S x)).val = X₁ (f (V' x)) := by
    let X' : Veranda Y H s j false (labelL Y H S x) := ⟨n,w,k',paletteT Y H s j _ h (V' x), ushers Y H j S _ x⟩
    exact onAny Y H V s Q Qt j false C X' -- tune
  simp_rw [he]
  exact X₁.continuous.comp (f.continuous.comp (usher_cont Y H j S n))

noncomputable def cognizable : Swatch S →L[ℂ] (groundRoom Y H V Q j false C).Op := by
  let f := ((A).subtype.toAlgHom.toLinearMap).comp ((located Y H V s Q Qt j false C).comp (labelL Y H S))
  exact { f with cont:= cap_fee Y H V s Q Qt j C S }

lemma registered (x : Swatch S) (m : Side) (h : Integrable (fun u=> coup S m (tent Y H) u x) (domeLaw ((tent Y H).c m))) :
    located Y H V s Q Qt j false C (labelL Y H S (sigil S m (tent Y H) x))=located Y H V s Q Qt j false C (labelL Y H S x) := by
  apply Subtype.ext; let F := cognizable Y H V s Q Qt j C S; change F (sigil S m (tent Y H) x)= F x
  have ht := ContinuousLinearMap.integral_comp_comm (E:=Swatch S) (Fₗ:=(R₀).Op) (𝕜:=ℂ) F h
  let g := fun u : Zodiac ((tent Y H).c m) => coup S m (tent Y H) u x
  refine ht.symm.trans ?_
  change (∫ u,F (g u) ∂domeLaw ((tent Y H).c m))=F x
  have he(u : Zodiac ((tent Y H).c m)) : F (g u)=F x := congrArg Subtype.val
    (located_same_paint Y H V s Q Qt j false C (labelL Y H S x) (labelL Y H S (g u)) (texture ..) (texture ..) (u ∘ wrap _) (coup_local S m (tent Y H) u x)).symm
  simp_rw [he]; simp
end rise

section strictpass
variable {S} -- S implicit, w?

def admit (x : Tower.Field Y H s j 0 true) : Tower.Field Y H s j 0 false :=
  ⟨x.val, (purpose_ok ..).mpr ⟨((purpose_ok ..).mp x.property).1,nofun⟩⟩
def composer {w : ℕ} (x : Entry Y H s j true w) : Entry Y H s j false w := ⟨admit Y H s j x.val, x.property⟩

/-- Over any price / shape at one rung, find its resolved representation **physically in the next
corresponding refinement region**. The f input MUST have its clock legal even for loose words. -/
theorem nearest_bud {w : ℕ} (x : Entry Y H s j false w) (p : 0<w) (t : InTest K true S false x.val.val)
    (q : Between K j 0 (σ*w) S) :
    ∃ g : Entry Y H (s+1) j true (L₀^(s+1-s)*w),
      g.val.val ∈ observ (tent Y H) (wingspan Λ l S) true ∧
        entrance Y H V (s+1) Q Qt j false C (composer Y H (s+1) j g)
           (Nat.mul_pos (pow_pos Λ.R.L.property _) p)=entrance Y H V s Q Qt j false C x p := by
  obtain ⟨y,h⟩ := rendered S (tent Y H) t
  let T := wingspan Λ l S; let Z := renovate Y H s Q S y
  have hx : x=paletteT Y H s j S q y := Subtype.ext (Subtype.ext h.symm)
  let g := furnished Y H s Q j false w x (s+1) (le_add_of_nonneg_right (by simp))
  have q' := expanding_lane Y H V Q Qt j q (s+1-s); let n:= L₀^(s+1-s)*w
  have hP : 0 < n := Nat.mul_pos (pow_pos Λ.R.L.property _) p
  have ht : T=volumeAround Λ l (s+1-s) S := by rw [show s+1-s=1 by omega]; rfl
  have Hq : Between (tent Y H) j 0 (σ*((L₀^(s+1-s)*w:ℕ):ℤ)) (wingspan Λ l S) := ((show wingspan Λ l S=volumeAround Λ l (s+1-s) S from ht)).symm ▸ q'
  have he : g.val.val=render T (tent Y H) Z := by -- tune ht
    change stream Y H D s (s+1-s) _ = _; rw [←h]; unfold T Z; rw [renovate_eq,show s+1-s=1 by omega]; rfl
  obtain ⟨m,Hx⟩ := (Buffered.separates (tent Y H) T).exists; let z := sigil T m (tent Y H) Z; have hZ := pays_refined_gauge Y H V s Q S m y ⟨Hx⟩
  let f' := paletteT Y H (s+1) j T Hq z -- notation scoped? section rose; lean local?
  have h0 : f'.val.val∈observ (tent Y H) T true := (obs_in ..).2 ⟨texture .., sigil_cov T m K ⟨Hx⟩ Z hZ⟩
  let F : Tower.Field Y H (s+1) j 0 true := ⟨f'.val.val,(purpose_ok ..).2 ⟨((purpose_ok ..).1 f'.val.property).1,fun _=> ((obs_in ..).1 h0).2⟩⟩
  refine ⟨(⟨F,f'.property⟩ : Entry Y H (s+1) j true (L₀^(s+1-s)*w)),h0,?_⟩
  change qv (s+1) (paletteT Y H (s+1) j T Hq (sigil T m K Z)) hP= _
  have hg : g=paletteT Y H (s+1) j T Hq Z := Subtype.ext (Subtype.ext he)
  rw [club_coup Y H V (s+1) Q Qt j C T Hq hP Z m hZ, ←hg]; exact Subtype.ext (refined_box Y H V s Q Qt j false C w x p (s+1) (by omega)).symm

/-- Every cap operator (and its answer in the phase) already on a singlet at the next level. -/
lemma cap_in_common (f : Marks K false) (p : InTest K true S false f.val) :
    ∃ g : Marks K true, g.val ∈ observ (tent Y H) (wingspan Λ l S) true ∧
        ∀ (j : Axis) (C : Arena Y H Q.circuit j 0 false),
          located Y H V (s+1) Q Qt j false C (bosonLabel (tent Y H) g)=located Y H V s Q Qt j false C f := by
  obtain ⟨x,e⟩ := rendered S (tent Y H) p
  let T := wingspan Λ l S; let y := renovate Y H s Q S x
  obtain ⟨m,Hx⟩ := (Buffered.separates (tent Y H) T).exists
  let z := sigil T m (tent Y H) y; let f' := labelL Y H T z; have ht := pays_refined_gauge Y H V s Q S m x ⟨Hx⟩
  have H0 := sigil_cov T m (tent Y H) ⟨Hx⟩ y ht
  refine ⟨(⟨f'.val, (marksSpec false f').1, fun _ => H0⟩ : Marks K true), ⟨texture ..,H0⟩, ?_⟩
  intro j C; change located Y H V (s+1) Q Qt j false C (labelL Y H T z)= _; unfold z; rw [registered Y H V (s+1) Q Qt j C T y m ht]
  apply Subtype.ext
  have hu : (labelL Y H T y)= (show Marks K false from upward Y H Q false f s (s+1-s)) := Subtype.ext (by
    rw [show s+1-s=1 by omega]; change render (wingspan Λ l S) K _=D s f.val; rw [← e]; exact renovate_eq ..)
  rw [hu]; exact cap_level (F:=f) Y H V s Q Qt j false C (s+1) (by omega)

def clubbed := Set.range (fun u : (Σ s:ℕ, Σ w : {n:ℕ // 0<n}, Entry Y H s j true w.val) =>
      boxOp Y H V u.1 Q Qt j false C u.2.1.val (composer Y H u.1 j u.2.2) u.2.1.property)

lemma clubs_account : objects Y H V Q Qt j false C=clubbed Y H V Q Qt j C := by
  apply Set.Subset.antisymm; swap; · rintro _ ⟨t,rfl⟩; exact object_at ..
  rintro _ ⟨s,w,t,p,rfl⟩
  obtain ⟨S,v,e⟩ := t.property
  obtain ⟨x,q,h⟩ := nearest_bud Y H V s Q Qt j C t p v e
  exact ⟨⟨s+1,⟨_,Nat.mul_pos (pow_pos Λ.R.L.property _) p⟩,x⟩,congrArg Subtype.val h⟩
theorem reserved_operators : driveAlgebra Y H V Q Qt j false C=(StarAlgebra.adjoin ℂ (clubbed Y H V Q Qt j C ∪ breezes Y H V Q j false C)).topologicalClosure := by unfold driveAlgebra; rw [clubs_account]
include V Q Qt
lemma reserved_arena : Dense (⋃ s, range (fun x : Tower.Field Y H s j 0 true => (P₁ s) (admit Y H s j x))) := by
  apply (sounds Y H V Q.circuit j 0 false C).mono; intro x h
  obtain ⟨s,v⟩ := Set.mem_iUnion.mp h; obtain ⟨y,e⟩ := v; obtain ⟨w,p,f,u⟩ := artist_fits_slab Y H s j false y
  obtain ⟨S,q,t⟩ := f.property
  obtain ⟨g,t,h⟩ := nearest_bud Y H V s Q Qt j C f p q t
  refine Set.mem_iUnion.mpr ⟨s+1,g.val,?_⟩
  change (P₁ (s+1)) ((composer Y H (s+1) j g).val)= x
  have ht := congrArg (fun z : 𝔅 => z.val ω₀) h; change (boxOp Y H V (s+1) Q Qt j false C (L₀^(s+1-s)*w) (composer Y H (s+1) j g) (Nat.mul_pos (pow_pos Λ.R.L.property _) p)) ω₀=(boxOp Y H V s Q Qt j false C w f p) ω₀ at ht
  rw [lays,lays,u] at ht; exact ht.trans e
lemma reserved_actor (f : (displayAlgebra Y H V Q Qt j false C) →⋆ₐ[ℂ] ℂ) :
    Dense (⋃ s, range (fun x : Tower.Field Y H s j 0 true => bud Y H V s Q Qt j false C f (admit Y H s j x))) := by
  apply (stroll_dense Y H V Q Qt j false C f).mono; intro x h
  obtain ⟨s,v⟩ := Set.mem_iUnion.mp h; obtain ⟨y,e⟩ := v
  obtain ⟨w,p,F,u⟩ := artist_fits_slab Y H s j false y
  obtain ⟨S,t,q⟩ := F.property
  obtain ⟨g,t,h⟩ := nearest_bud Y H V s Q Qt j C F p t q
  refine Set.mem_iUnion.mpr ⟨s+1,g.val,?_⟩
  have ht := congrArg (arrive Y H V Q Qt j false C f) h; rw [←turns,←turns,u] at ht
  exact ht.trans e
end strictpass
end YM.CF.Buffered.Afterglow.Tower.Selected
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.nearest_bud
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.registered
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.club_coup
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.cap_in_common
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.reserved_operators
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.reserved_actor
