import YM.SU5.Selected.Commutative

/-! Box linearity and cap linearity -- at common width/rise first. A composition
of boxes (with a positive shape) corresponds to one mark product, keeping
orientation. This doesn't give multiplicativity of compression. -/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.PhaseChoice
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
  (V:Universal Y H i k I E)
  (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
variable (j : Axis) (strict : Bool) (C : Arena Y H G.history.circuit j 0 strict)
local notation "A"=>Ark.Ht Y H G.history.circuit j 0 strict C
local notation "Fₛ" i:max=>Tower.Field Y H i j 0 strict
local notation "κ" s:max=>actor Y H s G.history.circuit j 0 strict C
local notation "ω"=>floorV Y H G.history.circuit j 0 strict C
local notation "Γ"=>Aurora Y H V G.history j strict C
local notation "Ω"=>seat0 Y H V G.history j strict C
local notation "ι₀"=> (Γ).subtypeL
local notation "π"=> (Γ).orthogonalProjectionOnto
local notation "B" s:max f:max h:max=>boxOp Y H V s G.history G.clipped j strict C _ f h
local notation "P" s:max=>cap Y H V s G.history G.clipped j strict C
local notation "A₀"=> catalog Y H V G j strict C

section
variable (s u : ℕ) (f g t:Entry Y H s j strict u) (x y z:observable (tent Y H) strict)
  (hu:0 < u)

lemma box_add (e:t.val.val=f.val.val + g.val.val) :
    B s t hu = (B s f hu) + (B s g hu) := by
  apply test_high Y H V s G.history j strict C
  intro r p y
  rw [ContinuousLinearMap.add_apply]
  simp only [snatch Y H V s G.history G.clipped j strict C u _ hu p]
  let T : (q : Entry Y H s j strict u) → Fₛ r := fun q =>
    slabT Y H r j strict _ (furnished Y H s G.history j strict u q r p) y
  change arrows Y H V G.history.circuit j 0 strict C r (T t)=
    arrows Y H V G.history.circuit j 0 strict C r (T f) + arrows Y H V G.history.circuit j 0 strict C r (T g)
  rw [←map_add]
  apply congrArg _; apply Subtype.ext
  change (T t).val=(T f).val + (T g).val
  unfold T
  simp only [slab_eq]
  rw [←add_mul]
  apply congrArg (fun x => x * (relocate K j _ y.val : Family K))
  change stream Y H G.refine s _ t.val.val = stream Y H G.refine s _ f.val.val + stream Y H G.refine s _ g.val.val
  rw [e]
  exact woven_add Y H G.history.circuit _ _ (test_entry ..) (test_entry ..)

lemma box_scale (a : ℂ) (e:t.val.val=a • f.val.val) :
    B s t hu = a • (B s f hu) := by
  apply test_high Y H V s G.history j strict C
  intro r p y
  rw [ContinuousLinearMap.smul_apply]
  simp only [snatch Y H V s G.history G.clipped j strict C u _ hu p]
  let T : (q : Entry Y H s j strict u) → Fₛ r := fun q =>
    slabT Y H r j strict _ (furnished Y H s G.history j strict u q r p) y
  change arrows Y H V G.history.circuit j 0 strict C r (T t)=
    a • arrows Y H V G.history.circuit j 0 strict C r (T f)
  rw [←map_smul]
  apply congrArg _; apply Subtype.ext
  change (T t).val=a • (T f).val
  unfold T
  simp only [slab_eq]
  rw [← Algebra.smul_mul_assoc]
  apply congrArg (fun x => x * (relocate K j _ y.val : Family K))
  change stream Y H G.refine s _ t.val.val = a • stream Y H G.refine s _ f.val.val
  rw [e]
  exact woven_smul Y H G.history.circuit _ _ (test_entry ..) a

lemma cap_moved_entry (c : ℤ) (e:f.val.val=relocate K j c x.val) :
    (P s) x = (π).comp ((B s f hu).comp (ι₀)) :=
  onAny Y H V s G.history G.clipped j strict C (⟨c,u,hu,f,e⟩ : Veranda Y H s j strict x)

/-- Prescribe a large rise and then any sufficiently large width. -/
theorem offsets : ∀ᶠ n : ℤ in atTop, ∀ᶠ u : ℕ in atTop,
    ∃ f : Entry Y H s j strict u, f.val.val = relocate K j n x.val := by
  obtain ⟨p⟩ := anyporch Y H s j strict x
  filter_upwards [eventually_ge_atTop p.rise] with c hc
  let q := (c-p.rise).toNat
  let r := heft Y H s j strict q p
  filter_upwards [field_entry Y H j strict s r.fwd.val] with u ⟨f,h⟩
  refine ⟨f,?_⟩
  rw [h,r.yes, show r.rise = c from ?_]
  change (q:ℤ)+p.rise=c
  unfold q; omega

lemma cap_add (e : x.val = y.val + z.val) : (P s) x=(P s) y+(P s) z := by
  obtain ⟨w,a,b,c⟩ := ((offsets Y H j strict s x).and ((offsets Y H j strict s y).and (offsets Y H j strict s z))).exists
  obtain ⟨u,h,⟨f,f'⟩,⟨g,g'⟩,p,p'⟩ := ((eventually_gt_atTop (0:ℕ)).and (a.and (b.and c))).exists
  rw [cap_moved_entry Y H V G j strict C s u f x h w f',
    cap_moved_entry Y H V G j strict C s u g y h w g',
    cap_moved_entry Y H V G j strict C s u p z h w p',
    box_add Y H V G j strict C s u g p f h, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
  rw [f',e,g',p']; exact chime_plus ..

lemma cap_scale (d : ℂ) (e:x.val = d • y.val) : (P s) x=d • (P s) y := by
  obtain ⟨w,a,b⟩ := ((offsets Y H j strict s x).and (offsets Y H j strict s y)).exists
  obtain ⟨u,h,⟨f,f'⟩,g,g'⟩ := ((eventually_gt_atTop (0:ℕ)).and (a.and b)).exists
  rw [cap_moved_entry Y H V G j strict C s u f x h w f',
    cap_moved_entry Y H V G j strict C s u g y h w g', box_scale Y H V G j strict C s u g f h d,
    ContinuousLinearMap.smul_comp,ContinuousLinearMap.comp_smul]
  rw [e] at f'
  rw [f',g']; exact chime_scale ..

lemma cap_unit (h : x.val = 1) : (P s) x = 1 := by
  let f := SlabMark.identity Y H s j strict 1
  have ht:x=observableOf Y H j strict s f.val := Subtype.ext h
  have p := cap_entry Y H V G j strict C s 1 f Nat.zero_lt_one
  have hp : (B s f Nat.zero_lt_one).comp ι₀ = ι₀ :=
    (congrArg (fun a : (Ark.Ht Y H G.history.circuit j 0 strict C).Op => a.comp ι₀)
      (ticket_birth Y H V s G.history G.clipped j strict C 1 Nat.zero_lt_one)).trans
        (behind' Y H V G.history j strict C _)
  have hp2 : (π).comp ι₀ = (1 : (Γ) →L[ℂ] (Γ)) := by
    ext1 v
    exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self v
  exact (congrArg (P s) ht).trans (p.trans ((congrArg (ContinuousLinearMap.comp (π)) hp).trans hp2))
end
section cap_forms
variable (s : ℕ) (f g : Fₛ s) (X : observable K strict)
local notation "Box" s:max u:max x:max h:max=>boxOp Y H V s G.history G.clipped j strict C u x h

/-- Mixed rectangle identity, as an *operator* on the joint ground space.
Shift the adjoint mark into an entry ending at u. Here the mark subdivision
is appropriate because of the two future entries. -/
lemma rectangle (mark₀ : observable K strict) {u w} (x: Entry Y H s j strict u) (p:0<u) (y: Entry Y H s j strict w) (q:0<w)
    (h:mark₀.val=mirror K j 0 x.val.val * y.val.val) :
    (P s) mark₀ = (π).comp ((star (B s x p) * (B s y q)).comp (ι₀)) := by
  change _ = (π).comp (((B s x p).adjoint.comp (B s y q)).comp ι₀)
  have hW : (edit Y H s j strict u w (inverse Y H s j strict u x) y).val.val = relocate K j (u:ℤ) mark₀.val := by
    rw [editor,h,relocate_mul]
    change mirror K j (gaugeT K (u:ℤ)) x.val.val * _= _
    have ha := mirror_cancel K j (u:ℤ) 0 (test_entry Y H s j strict x)
    rw [gaugeT_zero,sub_zero] at ha
    exact congrArg (· * relocate K j (u:ℤ) y.val.val) ha
  let n := edit Y H s j strict u w (inverse Y H s j strict u x) y
  have he : (B s x p).adjoint.comp (B s y q) = (B s n (by omega)) :=
    (congrArg (fun d : A →L[ℂ] A => d.comp (B s y q))
      (respects Y H V s G.history G.clipped j strict C u x p)).trans
        (edit_comp Y H V s G.history G.clipped j strict C u w (inverse Y H s j strict u x) y p q)
  exact (cap_moved_entry Y H V G j strict C s (u+w) n mark₀ (by omega) u hW).trans
    (congrArg (fun d : A →L[ℂ] A => (π).comp (d.comp (ι₀))) he.symm)
end cap_forms
end YM.CF.Buffered.Afterglow.Tower.PhaseChoice
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.cap_add
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.rectangle
