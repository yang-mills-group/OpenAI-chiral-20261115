import YM.SU5.FiniteGaugeData.Tower.Stilled
import YM.SU5.FiniteGaugeData.Tower.Charms
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6500
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Vacancy
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock Set
/-!
# Cap on arbitrary *graded* texture fields. All compressed to joint ground
with continuity, no need for an a.e. choice yet (algebra). Challenge remains
interaction lower, genuine continuum restoration.
-/
variable {Λ:Preparation}{lp:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus lp))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
local notation "L₀"=>Λ.R.L.val
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}{a b:ℕ→ℕ}(Q:Coherent (i:=i) (k:=k) (E:=E) Y H D a b)(Qt:Clipped Y H (i∘a) (k∘b))
variable (j:Axis)(strict:Bool)(C:Arena Y H Q.circuit j 0 strict)
local notation "A"=>Ark.Ht Y H Q.circuit j 0 strict C
local notation "S₀" s:max=> office Y H V s Q j strict C
local notation "Ω"=>floorV Y H Q.circuit j 0 strict C
local notation "P₀" s:max=> Console.sky (S₀ s) (look j)
local notation "R"=>Aurora Y H V Q j strict C
local notation "π"=> (R).orthogonalProjectionOnto
local notation "relic"=> (R).subtypeL
local notation "A₀"=> ((R)→L[ℂ] (R))
local notation "B" s:max f:max h:max=>boxOp Y H V s Q Qt j strict C _ f h
local notation "N₀" s:max X:max=>Veranda.placed Y H V s Q Qt j strict C X
local notation "T" t:max=>relocate K j t
local notation "Ε"=>advance Y H V Q.circuit j 0 strict C
variable {F:observable (tent Y H) strict}
noncomputable def candidate (X:Veranda Y H s j strict F) : A₀ := (π).comp ((N₀ s X).comp (relic))
local notation "C₀" s:max X:max=>candidate Y H V s Q Qt j strict C X
include V C
lemma behind (t:ℝ≥0):(π).comp (Ε t)= π:=by
 ext1 i
 apply ext_inner_left ℂ; intro f
 change inner ℂ (f: ↥R) ((π) ((Ε t) i))=_
 simp only [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
 rw [←advance_adjoint Y H V Q.circuit j 0 strict C t,ContinuousLinearMap.adjoint_inner_right,floor_rise]
lemma behind' (t:ℝ≥0): (Ε t).comp relic = relic:=by ext1 f; exact floor_rise ..
include Qt
private lemma pad_le(X X':Veranda Y H s j strict F)(h:X.rise=X'.rise)(p:X.span≤X'.span): (N₀ s X').comp relic=(N₀ s X).comp relic:=by
 cases X' with
 | mk r k h₁ f hk=>
    obtain ⟨v,hv⟩:=Nat.exists_eq_add_of_le (show X.span≤ k from p)
    subst k
    unfold Veranda.placed; have ht:f.val.val=X.fwd.val.val:=hk.trans ((show relocate K j r F.val=X.fwd.val.val from (show X.rise=r from h) ▸ X.yes.symm))
    dsimp only
    rw [SlabMark.shape_right Y H V s Q Qt j strict C X.span X.span X.fwd X.pos v f ht, ContinuousLinearMap.comp_assoc, behind']
lemma width (X X':Veranda Y H s j strict F)(h:X.rise=X'.rise):(N₀ s X').comp relic=(N₀ s X).comp relic:=by rcases le_total X.span X'.span with p|p; exact pad_le Y H V s Q Qt j strict C X X' h p; exact (pad_le Y H V s Q Qt j strict C X' X h.symm p).symm

noncomputable def heft(n:ℕ)(X:Veranda Y H s j strict F): Veranda Y H s j strict F where
 rise:= (n:ℤ)+X.rise
 span:= n+X.span
 pos:=by have h:=X.pos; omega
 fwd:= edit Y H s j strict n X.span (identity Y H s j strict n) X.fwd
 yes:=by rw [editor]; unfold identity unity; change 1*((T (n:ℤ)) _)= _; rw [one_mul,X.yes,relocate_sums K j _ _ F.property.1]
lemma along_heat(n:ℕ)(X:Veranda Y H s j strict F):N₀ s (heft Y H s j strict n X)=(Ε (MeshClock.whenly (timeMesh Λ) s n)).comp (N₀ s X):=by
 have p:=X.pos
 unfold Veranda.placed; dsimp only [heft]
 apply SlabMark.shape_left Y H V s Q Qt j strict C X.span X.span X.fwd X.pos
 rw [editor]; exact one_mul _
lemma same_porch (X X':Veranda Y H s j strict F): C₀ s X = C₀ s X':=by
 wlog p:X.rise≤ X'.rise generalizing X X'
 · symm; exact this X' X (by omega)
 let n:=(X'.rise-X.rise).toNat
 have hz:(n:ℤ)+X.rise=X'.rise:=by unfold n; omega
 have he:=width Y H V s Q Qt j strict C X' (heft Y H s j strict n X) hz.symm
 rw [along_heat Y H V s Q Qt j strict C n X] at he
 unfold candidate; rw [←he,←ContinuousLinearMap.comp_assoc,← ContinuousLinearMap.comp_assoc,← ContinuousLinearMap.comp_assoc (π),behind Y H V Q j strict C]
-- cap filled label.
noncomputable def cap (F:observable (tent Y H) strict):A₀:=C₀ s ((Classical.choice (anyporch Y H s j strict F)))
local notation "N₁" i:max=>cap Y H V i Q Qt j strict C
lemma onAny (X:Veranda Y H s j strict F):(N₁ s) F=C₀ s X:=same_porch Y H V s Q Qt j strict C _ X
noncomputable def upward(F:observable K strict)(p n:ℕ):observable K strict where
 val:=stream Y H D p n F.val
 property:= ⟨streams_test Y H Q.circuit p n F.property.1, fun a=>by
    obtain ⟨S,t⟩:=F.property.1.paid
    have h:F.val∈observ K S true:= (obs_in ..).2 ⟨t,F.property.2 a⟩
    exact (obs_in ..).1 (chroma Y H Q.circuit p n h) |>.2 ⟩
-- Pinned porch at any common level used for our assembly x→∞
noncomputable def addLevel (X:Veranda Y H s j strict F)(t:ℕ)(p:s≤ t): Veranda Y H t j strict (upward Y H Q strict F s (t-s)) where
 rise:= (Λ.R.L.val:ℤ)^(t-s)*X.rise
 span:= Λ.R.L.val^(t-s)*X.span
 pos:=Nat.mul_pos (pow_pos Λ.R.L.property _) X.pos
 fwd := furnished Y H s Q j strict X.span X.fwd t p
 yes:=by
    change stream Y H D s (t-s) X.fwd.val.val = relocate K j _ (stream Y H D s (t-s) F.val)
    rw [X.yes]; unfold relocate gaugeT; rw [show (K).B =Λ.block from rfl,chime_X Y H V s j (2*X.rise) Q.circuit F.property.1]; congr 2; ring
lemma allLevels (X:Veranda Y H s j strict F)(t:ℕ)(p:s≤ t): (N₀ s X)=N₀ t (addLevel Y H V s Q j strict X t p):=refined_box Y H V s Q Qt j strict C X.span X.fwd X.pos t p
lemma cap_level(t:ℕ)(h:s≤t):(N₁ t) (upward Y H Q strict F s (t-s))=(N₁ s) F:=by
 let b:=Classical.choice (anyporch Y H s j strict F)
 rw [onAny Y H V t Q Qt j strict C (addLevel Y H V s Q j strict b t h),onAny Y H V s Q Qt j strict C b]
 unfold candidate; rw [allLevels Y H V s Q Qt j strict C b t h]
-- star on all compressed. choose veranda of reflected f with tailored rise/width
noncomputable def dual (F:observable K strict):observable K strict:=by
 refine ⟨mirror K j 0 F.val,reflect_ok K j 0 F.property.1,fun e=>?_⟩
 obtain ⟨s,m⟩:= F.property.1.paid; exact covariant_flips K _ _ m (F.property.2 e)
noncomputable def verandStar (X:Veranda Y H s j strict F): Veranda Y H s j strict (dual Y H j strict F):=by
 refine ⟨X.span-X.rise,X.span,X.pos,inverse Y H s j strict X.span X.fwd,?_⟩
 change mirror K j (gaugeT K X.span) X.fwd.val.val=_
 rw [X.yes,odd_cancel K j _ 0 X.rise F.property.1,sub_zero,gaugeT_zero]; rfl
lemma mirror_cap: (ContinuousLinearMap.adjoint ((N₁ s) F))=(N₁ s) (dual Y H j strict F):=by
 let X':=Classical.choice (anyporch Y H s j strict F)
 rw [onAny Y H V s Q Qt j strict C X',onAny Y H V s Q Qt j strict C (verandStar Y H s j strict X')]
 unfold candidate Veranda.placed; rw [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_comp,Submodule.adjoint_subtypeL,Submodule.adjoint_orthogonalProjectionOnto,respects]; rfl
noncomputable def seat0 : ↑(R):=⟨Ω, belongs Y H V Q j strict C⟩
local notation "Ω₀"=>seat0 Y H V Q j strict C
-- conclude axis ensemble moments = E on arbitrary occurrences
lemma inspected: inner ℂ Ω₀ (((N₁ s) F) Ω₀)= E s F.val:=by
 let x:=Classical.choice (anyporch Y H s j strict F)
 rw [onAny Y H V s Q Qt j strict C x]
 change inner ℂ _ ((π) ((B s x.fwd x.pos) Ω))=_
 rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]; change inner ℂ Ω ((B s x.fwd x.pos) Ω)= _
 rw [boxed_at,x.yes]; exact SWay Y H V s j (2*x.rise) F.property.1

end YM.CF.Buffered.Afterglow.Tower.Vacancy
#print axioms YM.CF.Buffered.Afterglow.Tower.Vacancy.mirror_cap
