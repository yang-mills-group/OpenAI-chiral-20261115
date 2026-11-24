import YM.SU5.Reconstruction.Cross.Train
import YM.SU5.Reconstruction.Cross.Acceptance
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Selected Tapestry Tapestry.Altitude Tapestry.Exhibition
open Set OS.Semigroup MeshClock Germ
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
local notation "L₀" => Λ.R.L.val
local notation "Μ" => timeMesh Λ
open _root_.YM.SelectionAnalysis Vacancy.Average
/-! variation of unprojected raw kernel. First work on Γ with its standard dense topology.
Use directly the true time heat movement. On overlaps WHERE all axes accept, this will
pay raw and projected agreement. -/
section estimates
variable {A D : Type*} {X:Filter D} [NormedRing A]
-- moving targets
structure NearFlow (X:Filter D) (f g:D→A) : Prop where
  worth : ∃ C:ℝ, ∀ x, ‖f x‖≤C ∧ ‖g x‖ ≤ C
  thin : Tendsto (fun i=>dist (f i) (g i)) X (𝓝 0)
variable {f g f' g':D→A}
lemma NearFlow.times (p:NearFlow X f g)(q:NearFlow X f' g') : NearFlow X (fun i=> f i*f' i) (fun i=>g i*g' i):=by
 obtain ⟨t,h⟩:=p.worth; obtain ⟨s,k⟩:=q.worth
 constructor
 · refine ⟨t*s,fun i => ⟨(norm_mul_le ..).trans (mul_le_mul ((h i).1) ((k i).1) (norm_nonneg _) ((norm_nonneg _).trans (h i).1)),(norm_mul_le ..).trans (mul_le_mul ((h i).2) ((k i).2) (norm_nonneg _) ((norm_nonneg _).trans (h i).2))⟩⟩
 apply squeeze_zero' (Eventually.of_forall fun _=>dist_nonneg) (g:= fun i=>s*dist (f i) (g i)+t*dist (f' i) (g' i)) ?_ (by simpa using (p.thin.const_mul s).add (q.thin.const_mul t))
 apply Eventually.of_forall; intro i; apply (dist_triangle _ (g i * f' i) _).trans; simp only [dist_eq_norm]
 apply add_le_add; · rw [← _root_.sub_mul,mul_comm s]; exact (norm_mul_le ..).trans (mul_le_mul_of_nonneg_left ((k i).1) (norm_nonneg _))
 rw [← _root_.mul_sub]; exact (norm_mul_le ..).trans (mul_le_mul_of_nonneg_right ((h i).2) (norm_nonneg _))
lemma selfNear (p: ∃ t:ℝ,∀ x,‖f x‖≤ t) : NearFlow X f f:=⟨let ⟨c,h⟩:=p; ⟨c,fun i=>⟨h i,h i⟩⟩,by simp only [dist_self]; exact tendsto_const_nhds⟩
lemma twoAt {x:A} (h: Tendsto f X (𝓝 x))(p:Tendsto g X (𝓝 x))(a:∃ t:ℝ,∀ x,‖f x‖≤t ∧ ‖g x‖≤ t): NearFlow X f g:=⟨a,by simpa using h.dist p⟩
lemma NearFlow.cont_pair {Z : Type*} [NormedAddCommGroup Z] (L:A→Z) {C:ℝ≥0} (h:NearFlow X f g)(q:LipschitzWith C L): Tendsto (fun i=>dist (L (f i)) (L (g i))) X (𝓝 0):= squeeze_zero' (.of_forall fun _=> dist_nonneg) (.of_forall fun i=> q.dist_le_mul _ _) (by simpa using (h.thin.const_mul (C:ℝ)))
lemma list_near_flow{Z:Type*}(f g: Z→D→A)(t:List Z) (p:∀ j∈t,NearFlow X (f j) (g j)) : NearFlow X (fun i=> (t.map fun j=>f j i).prod) (fun i=> (t.map fun j=>g j i).prod) :=by induction t with
| nil=> exact selfNear ⟨_,fun _=>le_refl (‖(1:A)‖)⟩
| cons i t ih => exact (p _ (List.Mem.head ..)).times (ih (fun i h=> p _ (List.Mem.tail _ h)))
lemma read_at {L : Hilbert} (x y:L) {f g: D→L.Op} (p:NearFlow X f g) : Tendsto (fun i=>dist (inner ℂ x (f i y)) (inner ℂ x (g i y))) X (𝓝 0):= p.cont_pair _ ((innerSL ℂ x).comp (ContinuousLinearMap.apply ℂ L.space y)).lipschitz

end estimates
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ} {E : ℕ → Family (tent Y H) → ℂ}
  (V : Universal Y H i k I E)
  {D : ℕ→Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i:=i) (k:=k) (E:=E) Y H D a b) (Qt : Clipped Y H (i∘a) (k∘b))
  (s : ℕ) (j : Axis) (C : Arena Y H Q.circuit j 0 false) -- aim all even incl characters extension
variable (c : (displayAlgebra Y H V Q Qt j false C) →⋆ₐ[ℂ] ℂ)
local notation "𝔄" => driveAlgebra Y H V Q Qt j false C
local notation "ρ" => indoor Y H V Q Qt j false C c
local notation "Ρ" => procession Y H V Q Qt j false C c
local notation "Ω" => doorstep Y H V Q Qt j false C c
local notation "Eχ" s:max => Selected.response Y H V s Q Qt j false C c
local notation "Ex" => ride Y H V Q Qt j false C c
local notation "Φ" t:max => Tower.Field Y H t j 0 false
local notation "T" n:max => Selected.bud Y H V n Q Qt j false C c
local notation "O₀" q:max => indoorOp Y H V Q Qt s j C c q
local notation "U" x:max => ambient (M:=timeMesh Λ) (turnstile Y H V Q Qt j false C c) x
local notation "S" => turnstile Y H V Q Qt j false C c
local notation "Β" x:max p:max => entrance Y H V s Q Qt j false C x p
local notation "B" x:max => Ρ x
local notation "Ο" => seeMesh (timeMesh Λ)
local notation "Tv" x:max=> toR (M:=timeMesh Λ) x
section
variable {X:Type*} {P : Filter X} {F : Marks (tent Y H) false} (g : Gate Y H s j F)
lemma nearby_flow {v : seeMesh (timeMesh Λ)} (hp : g.within_ (Tv v)) {u u' : X→seeMesh (timeMesh Λ)}
    (he : ∀ i l,l≠j → u i l=u' i l) (q : Tendsto u P (𝓝 v)) (q' : Tendsto u' P (𝓝 v)) :
    NearFlow P (fun i=> (O₀ g) (u i)) (fun i=> (O₀ g) (u' i)) := by
 let L(q:Ο) := (Ex).E (g.left (Tv q)).toNNReal
 let A(q:Ο):= (Ex).E (g.right (Tv q)).toNNReal
 have ht:ContinuousAt L v:= (norm_cont_area Ex (Real.toNNReal_pos.mpr hp.1)).comp (f:=fun x:Ο=> (g.left (Tv x)).toNNReal) (((left_cont Y H s j g).comp (toR_cont Μ)).continuousAt)
 have hA:ContinuousAt A v:= (norm_cont_area Ex (Real.toNNReal_pos.mpr hp.2)).comp (f:=fun x:Ο=> (g.right (Tv x)).toNNReal) (((right_cont Y H s j g).comp (toR_cont Μ)).continuousAt)
 have Xz(i:X): U (u i)= U (u' i):= ignoresExtras _ _ (fun j _=>he i _ j.property)
 have Xn(i:X): U (-u i)= U (-u' i):= ignoresExtras _ _ (fun j _=>congrArg Neg.neg (he i (j:Axis) j.property))
 unfold indoorOp; simp_rw [Xz,Xn]
 refine NearFlow.times (NearFlow.times (NearFlow.times (NearFlow.times ?_ ?_) ?_) ?_) ?_
 · exact twoAt (ht.tendsto.comp q) (ht.tendsto.comp q') ⟨1,fun i=>⟨(Ex).shrinks _,(Ex).shrinks _⟩⟩
 · exact selfNear ⟨1,fun i=> ambient_cost ..⟩
 · exact selfNear ⟨_,fun _=> (le_refl ‖Ρ (Β g.entry g.pos)‖)⟩
 · exact selfNear ⟨1,fun i=> ambient_cost ..⟩
 exact twoAt (hA.tendsto.comp q) (hA.tendsto.comp q') ⟨1,fun i=>⟨(Ex).shrinks _,(Ex).shrinks _⟩⟩
end
section
variable {ι X : Type*} {P : Filter X} (f : ι→ Marks (tent Y H) false) (g : ∀ x, Gate Y H s j (f x))
-- even if order non-unique. gr.probe subsequent.
lemma vary_city {v : ι→Ο} (L:List ι) (hp : ∀ x∈L,(g x).within_ (Tv (v x)))
    {u u':X→ι→Ο} (e:∀ x i l, l≠j→ u x i l=u' x i l) (h:Tendsto u P (𝓝 v)) (h':Tendsto u' P (𝓝 v)): Tendsto (fun i=>dist (rawTrace Y H V Q Qt s j C c f g L (u i)) (rawTrace Y H V Q Qt s j C c f g L (u' i))) P (𝓝 0):=by
 exact read_at Ω Ω (list_near_flow (X:=P) (fun i x=> (O₀ (g i)) (u x i)) (fun i x=> (O₀ (g i)) (u' x i)) L (fun i he=> nearby_flow Y H V Q Qt s j C c (g i) (u:=fun x=>u x i) (u':=fun x=>u' x i) (hp i he) (fun x l p=> e x i l p) (((continuous_apply i).tendsto v).comp h) (((continuous_apply i).tendsto v).comp h')))
end
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas.vary_city
