import YM.CF.BProof.Dream.Lotus
import YM.CF.BProof.Extension.Card
/-! Continuous spin matrix addresses. Smooth path cost finite at prechoices. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Dream
open Matrix SU Finset Function Set Module Metric Complex Extension.Mar Real.smoothTransition
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator Kronecker ContDiff ComplexConjugate
attribute [local instance] opCStarAlgebra
variable {n m : Type*} [Fintype n][DecidableEq n][Fintype m][DecidableEq m]

abbrev Zone : Set ℝ:= Set.Icc 0 1 -- curve parameter
@[simp] lemma z0:(0:ℝ)∈Zone:=⟨le_rfl,zero_le_one⟩
@[simp] lemma z1:(1:ℝ)∈Zone:=⟨zero_le_one,le_rfl⟩
abbrev Window : Set (ℝ × ℝ):= Zone ×ˢ Zone
def ease (t:ℝ):= Real.smoothTransition (2*t-(1/2))
lemma ease_low (t:ℝ)(h:t≤1/4): ease t=0 := Real.smoothTransition.zero_of_nonpos (by linarith)
lemma ease_up (t:ℝ)(h:3/4≤t): ease t=1:=Real.smoothTransition.one_of_one_le (by linarith)
@[simp] lemma ease_zero : ease 0=0:= ease_low _ (by norm_num)
@[simp] lemma ease_one : ease 1=1:=ease_up _ (by norm_num)
@[fun_prop] lemma ease_s : ContDiff ℝ ∞ ease:=Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
lemma easeZ(t:ℝ) : ease t∈ Zone:= ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩
variable {X : Type*}[NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X]
section
variable {K:Type*}[RCLike K]
lemma moveK (f:n≃m)(A:Matrix n n K)(h:inK A): inK (Matrix.reindex f f A):=by
 let L:=Matrix.reindexAlgEquiv K K f; change inK (L A); have he (x:Matrix n n K): star (L x)=L (star x):=rfl; refine ⟨?_, (Matrix.det_reindex_self ..).trans h.2⟩; constructor <;> rw [he,←map_mul] <;> first | rw [h.1.1,map_one] | rw [h.1.2,map_one]
theorem climb [Nonempty n](S T:Set X)(s:IsCompact S)(p: Convex ℝ S)(t:T⊆S)
 (F:X→Matrix n n K) (d:Module.finrank ℝ X < 2*Module.finrank ℝ K) (h: SuitM S F)(W:∀ x∈T,inK (F x)) : ∃ G:X→Matrix n n K, SuitM S G∧ EqOn F G T∧ ∀ x∈S,inK (G x):=by
 have hu:Fintype.card n≠0:=Fintype.card_pos.ne'; let N:=Fintype.card n-1; let f:n≃ Fin (N+1):=Fintype.equivFinOfCardEq (by dsimp only [N]; omega)
 let L:=reindex (α:=K) f f; obtain ⟨G,g,H,K'⟩:= smooth_extend d S T s p t (L ∘ F) (fun i j=> h (f.symm i) (f.symm j)) (fun x hx=> moveK f _ (W x hx))
 refine ⟨reindex f.symm f.symm ∘ G,fun i j=> g (f i) (f j),fun i hi => ?_,fun x hx=> moveK f.symm _ (K' x hx)⟩ -- tune
 rw [Function.comp_apply, ←H hi]; exact (L.symm_apply_apply (F i)).symm
lemma jumpstart [Nonempty n](V W:Matrix n n K)(h:inK V)(e:inK W) : ∃ G:ℝ→Matrix n n K,(∀ i j,ContDiff ℝ ∞ (fun x=> G x i j))∧ G 0=V∧ G 1=W ∧ ∀ x,inK (G x):=by
 let S : Set ℝ:={0,1}; let f (x:ℝ) : Matrix n n K := (1-x) • V+x • W
 have hv : f 0=V:=by simp [f]
 have hw : f 1=W:=by simp [f]
 obtain ⟨G,g,H,P⟩:=climb Zone S isCompact_Icc (convex_Icc ..) (insert_subset z0 (by simp) -- tune
   ) f (by rw [Module.finrank_self]; have ht:0<Module.finrank ℝ K:=Module.finrank_pos; omega) (fun i j x hx=> ((contDiffAt_const.sub contDiffAt_id).smul contDiffAt_const).add (contDiffAt_id.smul contDiffAt_const)) (fun x hx=> by rcases hx with hx|hx; rw [hx,hv]; exact h; rw [Set.mem_singleton_iff] at hx; rw [hx,hw]; exact e)
 refine ⟨G ∘ ease,fun i j=>contDiff_iff_contDiffAt.mpr fun x=>(g i j _ (easeZ x)).comp x ease_s.contDiffAt,?_,?_,fun x=>P _ (easeZ x)⟩; rw [Function.comp_apply,ease_zero,←H (show (0:ℝ)∈S by simp [S]),hv]; rw [Function.comp_apply,ease_one,←H (show (1:ℝ)∈ S by simp [S]),hw]
end
lemma consistent (S:Set X) (F:X→Op n): SuitM S F ↔ Suit S F:=by
 constructor
 · exact fun h x hx=> (smoothView (I:=n)).toContinuousLinearMap.contDiff.contDiffAt.comp x (contDiffAt_pi.mpr (fun i=>contDiffAt_pi.mpr (fun j=>h i j x hx)))
 intro h i j x hx; let L:Op n→ₗ[ℝ] ℂ := ⟨⟨fun A=> A i j,fun _ _=>rfl⟩,fun _ _=>rfl⟩; exact L.toContinuousLinearMap.contDiff.contDiffAt.comp x (h x hx)
lemma jumpU [Nonempty n](V W:Op n)(h:inK V)(e:inK W) : ∃ G:ℝ→Op n, ContDiff ℝ ∞ G ∧ G 0=V∧ G 1=W∧ ∀ x,inK (G x):=by obtain ⟨G,g,h,e,t⟩:= jumpstart V W h e; exact ⟨G,smoothM G g,h,e,t⟩
lemma rect_climb [Nonempty n](F:ℝ × ℝ→ Op n) (T:Set (ℝ × ℝ))(t:T⊆Window)(p:ContDiff ℝ ∞ F)(u:∀ x∈T,inK (F x)): ∃ G:ℝ × ℝ→ Op n, Suit Window G ∧ EqOn F G T ∧ ∀ x∈Window,inK (G x):=by
 obtain ⟨g,G,h,w⟩:= climb Window T (isCompact_Icc.prod isCompact_Icc) ((convex_Icc ..).prod (convex_Icc ..)) t F (by rw [Module.finrank_prod,Module.finrank_self,Complex.finrank_real_complex]; decide -- namespace tune
   ) ((consistent _ _).mpr (fun _ _=> p.contDiffAt)) u; exact ⟨g,(consistent _ _).mp G,h,w⟩
end YM.CF.BProof.Dream
