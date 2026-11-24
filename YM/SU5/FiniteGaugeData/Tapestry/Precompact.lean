import YM.SU5.FiniteGaugeData.Tapestry.Raiment
import Mathlib.Analysis.Normed.Operator.Compact.Basic
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra

/-!
# Total boundedness of the outputs, in local Swatch norm even as step and
blocks vary. In particular not only compact from the domain side of marks.
-/

universe u
variable {I:Type*}
lemma capture {X:Type*}[PseudoMetricSpace X](f:I→X)(p:∀ ε:ℝ,0<ε→ ∃ (Y:Type u) (_:PseudoMetricSpace Y) (g:I→Y) (δ:ℝ),0<δ ∧ TotallyBounded (Set.range g) ∧ ∀ i j,dist (g i) (g j)<δ → dist (f i) (f j)<ε): TotallyBounded (Set.range f):=by
  apply Metric.totallyBounded_iff.mpr; intro ε e
  obtain ⟨Y,m,g,δ,d,b,h⟩:= p _ e
  obtain ⟨S,a,H,V⟩:= Metric.finite_approx_of_totallyBounded b δ d
  letI:= H.fintype
  choose j h' using fun i:↥S=>a i.property
  refine ⟨Set.range (fun i:↥S=>f (j i)),Set.finite_range _,?_⟩
  rintro x ⟨i,rfl⟩; have hv:= V (Set.mem_range_self i); simp only [Set.mem_iUnion] at hv ⊢
  obtain ⟨y,w,q⟩:= hv; let r:↥S:=⟨y,w⟩
  exact ⟨_, Set.mem_range_self r, h i (j r) (by rw [h']; exact mem_ball.mp q)⟩

lemma captureTuple {J:Type*}[Finite J]{V:J→Type*}[∀ i,PseudoMetricSpace (V i)][∀ i,CompleteSpace (V i)](f:I→∀ i,V i)(h:∀ i, TotallyBounded (Set.range (fun j=> f j i))): TotallyBounded (Set.range f):=
  let A:= fun i=>closure (Set.range (fun j=> f j i))
  ((isCompact_pi_infinite (fun i=> (h i).closure.isCompact_of_isComplete (isClosed_closure.isComplete) : ∀ i,IsCompact (A i))).totallyBounded).subset (by rintro _ ⟨i,rfl⟩; exact fun j=> subset_closure (Set.mem_range_self _))

variable (S:Finset Cover)
lemma paletteTB {f:I→Pigment S}(h:Menu (I:=I) (fun i x=> daub S (f i) x)) : TotallyBounded (Set.range f):=by
  apply capture f; intro ε e; let δ:= ε/4; have d: 0<δ:=by unfold δ; linarith
  obtain ⟨K,k,t⟩:= h.deal _ d
  let T (a:K.Sign):PairsC:= if p:∃ v,K.idT v=a then Classical.choose p else (1,1)
  let V(i:I)(a:K.Sign):= daub S (f i) (T a)
  obtain ⟨C,c,u⟩:= h.budget
  refine ⟨K.Sign→ℂ,inferInstance,V,δ,d,(isCompact_closedBall (0:K.Sign →ℂ) C).totallyBounded.subset ?_,?_⟩
  · rintro _ ⟨i,rfl⟩; rw [mem_closedBall_zero_iff]; exact (pi_norm_le_iff_of_nonneg c).2 fun y=> u i (T y)
  intro i j ij; rw [dist_eq_norm]
  apply (pigmentLe S (f i-f j) (C:=3*δ) (by positivity) ?_).trans_lt (by unfold δ; linarith)
  intro x; let k:= K.idT x; let z:=T k; have he : K.withZ x z:= K.id_spec x z (by have w: ∃ y,K.idT y=k:=⟨x,rfl⟩; unfold z T; rw [dif_pos w]; exact (Classical.choose_spec w).symm)
  have v(r:I): dist (daub S (f r) x) (V r k)< δ:= t _ _ he r
  apply (show ‖daub S (f i-f j) x‖ ≤ dist (daub S (f i) x) (V i k)+dist (V i k) (daub S (f j) x) from (dist_eq_norm (daub S (f i) x) (daub S (f j) x)).symm.le.trans (dist_triangle ..)).trans
  have hv:= (dist_triangle (V i k) (V j k) (daub S (f j) x)); rw [dist_comm (V j k)] at hv; linarith [v i,v j,(dist_pi_lt_iff d).mp ij k]

open Py Py.Rate LocalLimit Preparation Journey Vale
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l)) (H: Real.exp 1 ≤ Λ.x)
variable (s:ℕ)(a b:I→ℕ)(p:∀ i,Satin.PairIdx Y s (a i) (b i))
local notation "B"=> followBox (Λ:=Λ) (l:=l) S
local notation "P" i:max=>side Y (a i) (s+1)
set_option quotPrecheck false
variable (r:∀ i, Roomy (followBox (Λ:=Λ) (l:=l) S) (side Y (a i) (s+1)))
    (f:I→ Swatch S){C:ℝ}(h:∀ i,‖f i‖ ≤ C)
local notation "F" i:max=> Tapestry.costume Y H s (a i) (b i) S (p i) (r i) (f i)
include h
lemma carpet (e:Evens B): Menu (I:=I) (fun i x=> daub B ((F i) e) x):=by
  let X(i:I)(x:PairsC):= present Y H (s+1) (a i) B (F i) (replant B (P i) x)
  have ht: Menu X:= by unfold X; simp_rw [costumed]; exact clothMenu Y H s S a b p f h
  choose m u using fun i :I=> eyes_native Y H (s+1) (a i) B (Roomy.seats (r i))
  let Z(i:I):FC (Single (P i)) →L[ℂ] ℂ := m i e
  let ψ(i:I)(x:PairsC):= Z i (X i x)
  have hv(i:I)(v:FC (Single (P i))): ‖Z i v‖ ≤ ‖v‖:= (u i 0 (1,1) e).1 v
  have hy:Menu ψ:=by
    obtain ⟨c,z,U⟩:=ht.budget
    refine ⟨Deal.along (fun i (x:FC (Single (P i)))=>Z i x) ht.deal ?_, c,z,fun i x=> (hv ..).trans (U ..)⟩
    intro ε he; refine ⟨ε,he,fun i x y b=>?_⟩; rw [dist_eq_norm,←map_sub]; rw [dist_eq_norm] at b; exact (hv ..).trans_lt b
  exact hy.congr fun i x=> (u i (F i) x e).2.symm

lemma costumeTB : TotallyBounded (Set.range (fun i=> Tapestry.costume Y H s (a i) (b i) S (p i) (r i) (f i))):= captureTuple (fun i=> F i) fun i=> paletteTB _ (carpet S Y H s a b p r f h i)

omit h
abbrev Turn (i k:ℕ):Prop:= Satin.PairIdx Y s i k ∧ Roomy (followBox (Λ:=Λ) (l:=l) S) (side Y i (s+1))
abbrev RangeLine := {x:ℕ×ℕ//Turn S Y s x.1 x.2}
def gallery (i: RangeLine S Y s) : Swatch S →ₗ[ℂ] Swatch B:= gangway Y H s _ _ S i.property.1 i.property.2
abbrev Trade := Swatch S →L[ℂ] Swatch (followBox (Λ:=Λ) (l:=l) S)
lemma rate_gallery: ∃ C:ℝ, 0≤C ∧ ∀ i: RangeLine S Y s, ∀ f:Swatch S, ‖gallery S Y H s i f‖ ≤ C*‖f‖:=by
  let I:= RangeLine S Y s; let X:= I × (Metric.closedBall (0:Swatch S) 1); let p:X→I:=Prod.fst; let ν:X→Swatch S:= fun i=> i.2.val
  have ht : TotallyBounded (Set.range (fun i:X=> gallery S Y H s (p i) (ν i))):=costumeTB S Y H s (fun i:X=>(p i).val.1) (fun i:X=>(p i).val.2) (fun i=>(p i).property.1) (fun i=>(p i).property.2) ν (C:=1) (fun i=> by exact mem_closedBall_zero_iff.mp i.2.property)
  obtain ⟨C,h⟩:= ht.isBounded.exists_norm_le; let c:=max C 0
  refine ⟨c,le_max_right ..,fun i f=>?_⟩; let t:=(algebraMap ℝ ℂ (‖f‖⁻¹)); let f':=gallery S Y H s i; change ‖f' f‖ ≤ _
  by_cases q:f=0
  · rw [q, map_zero,norm_zero,norm_zero,mul_zero]
  have he:0<‖f‖:= norm_pos_iff.mpr q
  have x : ‖t • f‖ = 1:=by simp [t,norm_smul,inv_mul_cancel₀ he.ne']
  let a:X:=⟨i,t • f, mem_closedBall_zero_iff.mpr x.le⟩
  have hp:‖f' (t • f)‖ ≤ c:=(h _ (Set.mem_range_self a)).trans (le_max_left ..)
  have hy:‖f‖⁻¹ * ‖f' f‖ ≤ c:=by simpa [t,norm_smul,map_smul] using hp
  rw [←div_eq_inv_mul,div_le_iff₀ he] at hy; exact hy

noncomputable def barter (i: RangeLine S Y s) : Swatch S →L[ℂ] Swatch (followBox (Λ:=Λ) (l:=l) S) := (gallery S Y H s i).mkContinuous _ ((rate_gallery S Y H s).choose_spec.2 i)
lemma barter_apply {i k:ℕ} (p : Turn S Y s i k)(x:Swatch S) : barter S Y H s ⟨(i,k),p⟩ x=Tapestry.costume Y H s i k S p.1 p.2 x:=rfl
lemma compact_barter (i: RangeLine S Y s): IsCompactOperator (barter S Y H s i):=by
  let f:=barter S Y H s i; let U:= closedBall (0:Swatch S) 1
  let x: RangeLine S Y s:=i
  have h : TotallyBounded (Set.range (fun z:U=> f z.val)):= costumeTB S Y H s (fun _:↑U=>x.val.1) (fun _:↑U=>x.val.2) (fun _=>x.property.1) (fun _=>x.property.2) (fun z:U=>z.val) (C:=1) (fun i=> mem_closedBall_zero_iff.mp i.property)
  let W:= Set.range (fun z:U=> f z.val); apply (isCompactOperator_iff_image_closedBall_subset_compact (f.toLinearMap) (r:=1) zero_lt_one).2
  exact ⟨closure W, h.closure.isCompact_of_isComplete isClosed_closure.isComplete, fun x (b:x∈f '' U)=> by obtain ⟨y,hz,rfl⟩:= b; exact subset_closure (Set.mem_range_self (⟨y,hz⟩:↑U))⟩
end YM.CF.Buffered.Afterglow.Tapestry
#print axioms YM.CF.Buffered.Afterglow.Tapestry.compact_barter
#print axioms YM.CF.Buffered.Afterglow.Tapestry.costumeTB
