import YM.SU5.Reconstruction.Cross.Cased
import YM.SU5.Reconstruction.Cross.AllReal
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
/-!
# Observation chart space (axis i, any accepted common resolution charts)
Results aim include different axes/heights. A possible alternative to AY boundary data.
-/
variable {ι:Type*} [Finite ι] (f : ι → Marks (tent Y H) false) (g : ∀ i,Gate Y H s j (f i))
local notation "F₀" t:max x:max => upGrade Y H s Q false (f x) t
local notation "Ωt" t:max => (fun i=> upGrade Y H s Q false (f i) t)
local notation "S" => seeMesh (timeMesh Λ)
local notation "Tv" => gridChart (ι:=ι) Μ
local notation "Xi" => electedAtlas Y H V Q Qt s j C c f g
variable {j':Axis} (C' : Arena Y H Q.circuit j' 0 false) (c' : (displayAlgebra Y H V Q Qt j' false C') →⋆ₐ[ℂ] ℂ)
local notation "Eχ'" t:max => Selected.response Y H V t Q Qt j' false C' c'
local notation "Xi'" t:max f:max g:max=> electedAtlas Y H V Q Qt t j' C' c' f g

private lemma grade_same (s : ℕ) (x: Marks (tent Y H) false) : upGrade Y H s Q false x s=x:=Subtype.ext (by change stream Y H D s (s-s) x.val=x.val; rw [Nat.sub_self]; rfl)
lemma shares_path {e a b t:ℕ}(h : e≤a)(u:a≤t)(p:e≤b)(q:b≤t)(x:Marks (tent Y H) false):
    (upGrade Y H a Q false (upGrade Y H e Q false x a) t:Marks K false)=upGrade Y H b Q false (upGrade Y H e Q false x b) t:=by
  suffices hp:∀ (k:ℕ),e≤ k→ k≤t→ upGrade Y H k Q false (upGrade Y H e Q false x k) t=upGrade Y H e Q false x t by rw [hp a h u,hp b p q]
  intro k h tP; apply Subtype.ext; change stream Y H D k _ (stream Y H D e (k-e) _)= stream Y H D e (t-e) _
  have hx := joined (D:=D) Y H e (k-e) (t-k) x.val
  rwa [show k-e+(t-k)=t-e by omega,show e+(k-e)=k by omega,Eq.comm] at hx
lemma keyPath (t e:ℕ) (h:s≤e)(p:e≤t)(l':List ι)(v:ι→ Cover) : orderWord Y H Q s f t l' v= orderWord Y H Q e (Ωt e) t l' v:=by
 unfold orderWord; apply congrArg; refine congrArg (fun f:ι→Marks (tent Y H) false=> l'.map f) ?_
 funext x; apply congrArg; exact (grade_same Y H Q s (f x)) ▸ shares_path Y H Q (e:=s) (show s ≤ s from le_rfl) (h.trans p) h p (f x) -- order check
variable (t r:ℕ)(g₁:∀ i,Gate Y H t j (upGrade Y H s Q false (f i) t)) (g₂:∀ i,Gate Y H r j' (upGrade Y H s Q false (f i) r))
local notation "ξX" => electedAtlas Y H V Q Qt t j C c (fun i=> F₀ t i) g₁
local notation "ξZ" => electedAtlas Y H V Q Qt r j' C' c' (fun i=> F₀ r i) g₂
local notation "ξ" => rawTrace Y H V Q Qt t j C c (fun i=> F₀ t i) g₁
local notation "ξ'" => rawTrace Y H V Q Qt r j' C' c' (fun i=> F₀ r i) g₂
local notation "Θ" => Marks (tent Y H) false
variable {t r}
private lemma by_dense_range {V A X:Type*}[TopologicalSpace X][PseudoMetricSpace A][PseudoMetricSpace V] [T2Space V]{f:X→ A}{g s:A→V}{w:Set A}(p:∀ x:X,f x∈w→ g (f x)=s (f x))(h:IsOpen w)(x:A)(hx:x∈w)(hg:DenseRange f)(t:Continuous g)(u:Continuous s) : g x=s x:= by
    apply EqOn.closure (s:=Set.range f∩ w) (f:=g) (g:=s) ?_ t u ?_
    · rintro y ⟨⟨i,rfl⟩,q⟩; exact p i q
    apply Metric.mem_closure_iff.mpr; intro ε p; obtain ⟨c,g,he⟩:= hg.exists_mem_open (h.inter Metric.isOpen_ball) (show (w∩ Metric.ball x ε).Nonempty from ⟨x,hx,Metric.mem_ball_self p⟩)
    exact ⟨f c,⟨⟨c,rfl⟩,g⟩,(dist_comm _ _).trans_lt (show _ from he)⟩
lemma differentRungs {x y:List ι}(h:x.Perm y)(hp:x.Nodup)
    (he:∀ (t:ℕ)(f:Marks (tent Y H) false), (Eχ t) f = (Eχ' t) f)
    {a b:ℤ}(p:s≤t)(q:s≤r)(u : Leaves Y H t j (Ωt t) g₁ a x)(v:Leaves Y H r j' (Ωt r) g₂ b y)
    {w:ι→Axis→ℝ}(xt: ∀ i∈x,(g₁ i).within_ (w i))(yt:∀ i∈y,(g₂ i).within_ (w i)):
    electedAtlas Y H V Q Qt t j C c (Ωt t) g₁ x w=electedAtlas Y H V Q Qt r j' C' c' (Ωt r) g₂ y w:=by
 classical
 letI:=Fintype.ofFinite ι
 let G:Set (ι→Axis→ℝ):= {w|∀ i∈x,(g₁ i).within_ (w i)}∩{w|∀ i∈y,(g₂ i).within_ (w i)}
 have hg:IsOpen G:=(open_window Y H t j _ g₁ x).inter (open_window Y H r j' _ g₂ y)
 suffices A : ∀ q : ι→S, Tv q ∈ G → ξX x (Tv q)=ξZ y (Tv q) from
     (by_dense_range A hg w (show w∈G from ⟨xt,yt⟩) (gridChart_dense Μ) (electedAtlas_continuous Y H V Q Qt t j C c _ _ _) (electedAtlas_continuous Y H V Q Qt r j' C' c' _ _ _) ) -- tune define helper
 intro d m
 apply tendsto_nhds_unique_of_eventuallyEq (handles Y H V Q Qt t j C c _ _ x d hp) (handles Y H V Q Qt r j' C' c' _ _ y d (h.nodup_iff.mp hp)) ?_
 refine (besidePositions Μ ((Tv) ⁻¹' G) d ((hg.preimage (grid_continuity Μ)).mem_nhds m)).mono (fun n v'=> ?_)
 refine Average.eq_of _ _ fun l=> ?_
 let K' := disclose Μ d n l; change ξ x K'=ξ' y K'
 obtain ⟨e,n₀,n',X⟩ := (((eventually_ge_atTop t).and ((eventually_ge_atTop r).and (eventually_all.mpr (fun i=> grid_higher Μ (K' i)))))).exists
 choose W w using X
 have h':Tv K'∈ G:= v' l
 have hx:K'=grid Μ e ∘ W:=(funext w).symm; rw [hx] at h' ⊢ -- BAD replaces v' dependent, h': Tv pred.
 rw [train_lattice Y H V Q Qt t j C c _ g₁ e n₀ W x _ u (fun i s=>(g₁ i).allows (h'.1 i s)),train_lattice Y H V Q Qt r j' C' c' _ g₂ e n' W y _ v (fun i s=>(g₂ i).allows (h'.2 i s)),
   ←keyPath Y H Q s f e t p n₀,←keyPath Y H Q s f e r q n',order_word_perm Y H Q s f e h,he]
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas.differentRungs
