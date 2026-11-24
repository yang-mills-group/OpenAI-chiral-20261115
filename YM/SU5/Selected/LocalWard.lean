import YM.SU5.Selected.Addition

/-!
# The local gauge squeezing rule on the joint-Aurora algebra

Independently of extremality or momentum bounds. Use all axes (any choice of
reflection here); shift TWO operators simultaneously and use the unshifted
trace/patched support. Thus can pass the Ward hypothesis of `Parcel` through
selection even if the latter state isn't produced by a Poincaré criterion.
In particular it will be exact after projection (use cyclicity of caps).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 600000
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
open Tapestry (TraceGauge Circular)

private lemma change_gauge {J : Calibration} {t u : Cover → SU.E} {S : Finset Cover}
    {f g : Family J} (w : Circular S t f g) (h : ∀ i ∈ S, u i = t i) : Circular S u f g :=
  fun m v hv => w m v (fun i p => (hv i p).trans (h i p))

private lemma id_gauge {J : Calibration} {S : Finset Cover} {f : Family J}
    (p:InTest J true S false f) : Circular S (1 : Cover → SU.E) f f := by
  let g : Tapestry.Dome J := ⟨f,Tapestry.broadCompile J S p⟩
  have ht : g∈Tapestry.bay J S true := p
  have he := Tapestry.pennantTrace J S (1 : Cover → SU.E) ht
  rw [Tapestry.pennantId] at he
  exact he

include V in
lemma ward_cancel (s : ℕ) {S T : Finset Cover} {p : Cover → SU.E} {f F g : Family (tent Y H)}
    (q : InTest K true S false f) (Q' : InTest K true S false F)
    (gT : InTest K true T false g) (t : Disjoint S T) (hp : Circular S p f F) :
    E s (g*f) = E s (g*F) := by
  let R (x : Cover) := if x∈ S then p x else 1
  have hx: InTest K true (S∪T) false g := gT.mono Finset.subset_union_right
  apply (Papal.ledgerRule Y H V (S∪T) s).gauge R (g*f) (g*F) (hx.mul (q.mono Finset.subset_union_left))
    (hx.mul (Q'.mono Finset.subset_union_left))
  apply Circular.mul R _
  · apply Tapestry.largerGauge Finset.subset_union_right
    exact change_gauge (id_gauge gT) (fun i g => if_neg (fun h => Finset.disjoint_left.mp t h g))
  apply Tapestry.largerGauge Finset.subset_union_left
  exact change_gauge hp (fun i h => if_pos h)

local notation "U" t:max=>relocate K j t
local notation "θ"=>mirror K j 0
section
variable (S : Finset Cover) (s : ℕ)
private def farTest (c : ℤ) := plow K j (-c) (reflectedBox j 0 (plow K j c S))
lemma negative_room : ∀ᶠ c : ℤ in atTop, Disjoint S (farTest Y H j S c) := by
  obtain ⟨d,p⟩ := Tower.sizes S
  obtain ⟨x,q⟩ := p j
  let r := ruler (K).B
  have hr : 0 < r := ruler_gene _
  filter_upwards [(Tendsto.const_mul_atTop' hr (tendsto_id (x := atTop))).eventually_gt_atTop (-x)] with c hc
  apply Finset.disjoint_left.mpr
  intro i t u
  obtain ⟨y,w,e⟩ := plow_stays K j (-c) _ u
  obtain ⟨z,h,a⟩ := reflect_stays j 0 _ w
  obtain ⟨v,hv,rfl⟩ := plow_stays K j c _ h
  have hi := (q v hv).1; have hf := (q i t).1
  specialize a j
  rw [if_pos rfl,moves,if_pos rfl] at a
  rw [e,moves,if_pos rfl] at hf
  change -x < ruler (K).B * c at hc
  linarith

include V C
lemma cap_ward {g : Cover → SU.E} (f F : observable (tent Y H) strict)
    (p:InTest K true S false f.val) (q:InTest K true S false F.val)
    (w:Circular S g f.val F.val) : (P s) f=(P s) F := by
  obtain ⟨c,hc,a,b⟩ := ((negative_room Y H j S).and ((offsets Y H j strict s f).and
    (offsets Y H j strict s F))).exists
  obtain ⟨u,h,⟨x,x'⟩,y,y'⟩ := ((eventually_gt_atTop (0:ℕ)).and (a.and b)).exists
  have hh (m : Fₛ s) (T : InTest K true (plow K j c S) false m.val) :
    inner ℂ ((κ s) m) ((κ s) x.val)=inner ℂ ((κ s) m) ((κ s) y.val) := by
    have hg(X t): E s ((U (-c)) X)= E s X := SWay Y H V s j (2*(-c)) (F:=X) t
    let fM := θ m.val
    have hp:InTest K true (reflectedBox j 0 (plow K j c S)) false fM := axial K j 0 T
    rw [stems Y H V,stems Y H V,area0]
    change E s (fM*_)= E s (fM*_)
    rw [←hg _ ((aux_test hp).mul (test_entry Y H s j strict x)), ← hg _ ((aux_test hp).mul (test_entry Y H s j strict y)),
      relocate_mul,relocate_mul]
    rw [x', y', relocate_sums K j _ _ f.property.1, relocate_sums K j _ _ F.property.1, neg_add_cancel,
      relocate_zero K j f.property.1, relocate_zero K j F.property.1]
    exact ward_cancel Y H V s p q (flow_port K j _ hp) hc w
  let x0 := (κ s) x.val
  let y0 := (κ s) y.val
  have hx : InTest K true (plow K j c S) false x.val.val := x'.symm ▸ flow_port K j _ p
  have hy : InTest K true (plow K j c S) false y.val.val := y'.symm ▸ flow_port K j _ q
  have he:x0=y0 := by
    have h0:inner ℂ x0 (x0-y0)=0 := by rw [inner_sub_right, show inner ℂ x0 x0=inner ℂ x0 y0 from hh _ hx,sub_self]
    have h1:inner ℂ y0 (x0-y0)=0 := by rw [inner_sub_right,show inner ℂ y0 x0=inner ℂ y0 y0 from hh _ hy,sub_self]
    exact sub_eq_zero.mp (inner_self_eq_zero.mp (by rw [inner_sub_left,h0,h1,sub_self] : inner ℂ (x0-y0) (x0-y0)=0))
  let B₁ := P s
  have hP(m: Entry Y H s j strict u) (Fq : observable (tent Y H) strict) (e:m.val.val=relocate K j c Fq.val):
      (B₁ Fq) Ω = π ((κ s) m.val) := by
    unfold B₁; rw [cap_moved_entry Y H V G j strict C s u m Fq h c e]
    exact congrArg (π) (lays Y H V s G.history G.clipped j strict C u m h)
  apply sub_eq_zero.mp
  apply faithful_of_commute Y H V G j strict C
  · intro m
    exact (commutes Y H V G j strict C (s,f) m).sub_left
      (commutes Y H V G j strict C (s,F) m)
  change (B₁ f) Ω - (B₁ F) Ω = 0
  rw [hP x f x',hP y F y', show (κ s) x.val=(κ s) y.val from he,sub_self]
end
end YM.CF.Buffered.Afterglow.Tower.PhaseChoice
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.cap_ward
