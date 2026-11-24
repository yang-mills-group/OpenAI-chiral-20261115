import YM.SU5.Registration.Ink.Potential
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
/-!
 # Restrict translations/spectrum to the point sector.
 No star-hypothesis needed for *reducing* heat away from proof of fields.
 Use this also on the larger sector if later buying more families.
 Inspiration `Next/BOUNDARY/Core` (project GNS Hilbert independent)
 and `YM/SU5/Selected/{Elected,etc}`. Here do not commute in sectors
 beyond literal estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SatinWFixed
open Function Filter MeasureTheory Measure Set Complex Submodule SatinRegistration
open Boundary Probe Mink Multiplier Roy Spectral OS.Semigroup SatinEdge.RealSheet
open CF.Buffered.Afterglow.Hierarchy.Seld
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder
variable {H: Hilbert}{S: OS.Semigroup H timeAxis}{V:Type*}[AddCommGroup V][Module ℂ V]
local notation "D"=> radial S
namespace Carton
variable (B : Carton S V)
-- two spans: in budgets within D, in H. both induced SUBSPACES, no grand assumption cycFull
noncomputable def words : Submodule ℂ D := span ℂ (range B.row)
noncomputable def inH: Submodule ℂ H:= B.words.map (D).subtype
noncomputable def pointShelf: Submodule ℂ H := B.inH.topologicalClosure
lemma true_words : B.inH=span ℂ (range (fun p=> (B.row p).1)):=by
 unfold inH words; rw [Submodule.map_span, ← Set.range_comp]; rfl
lemma span_shelf : B.pointShelf= (span ℂ (range (fun p=>(B.row p).1))).topologicalClosure:= by unfold pointShelf; rw [B.true_words]
lemma words_exist (p): (B.row p)∈ B.words:= Submodule.subset_span (mem_range_self _)
lemma writes (p): (B.row p).val∈ B.pointShelf:= B.inH.le_topologicalClosure (Submodule.mem_map_of_mem (B.words_exist p)) -- check args
lemma at_root : B.omega∈ B.pointShelf:= B.writes []
instance : CompleteSpace B.pointShelf:=B.inH.isClosed_topologicalClosure.completeSpace_coe
noncomputable abbrev euSlide (u:E4)(p:MarkType V): MarkType V:= (p.1,ahead u p.2) -- note despite name uses Mink outside Eu spacetime
lemma shifted_row (u:E4) (p:MarkWords V): SatinRegistration.shift S u (B.row p)=B.row (p.map (euSlide u)):=by
 induction p with
 | nil=> exact Subtype.ext (B.stay u)
 | cons a p ih=> rw [B.row_picks,List.map_cons,B.row_picks]; change SatinRegistration.shift _ _ (SatinRegistration.field S _ (B.coherent a.1) (B.price a.1) _ _) = _; rw [field_translate,ih]
-- on budget-domain span uses onDomain on all its elements
lemma shift_write (u:E4) (x:D)(h:x∈ B.words): SatinRegistration.shift S u x∈ B.words:= by
 refine Submodule.map_le_iff_le_comap.mp (show B.words.map (SatinRegistration.shift S u) ≤ B.words from ?_) h
 unfold words; rw [Submodule.map_span, ← Set.range_comp]; refine Submodule.span_le.mpr ?_
 rintro _ ⟨p,rfl⟩; change SatinRegistration.shift S u (B.row p)∈ B.words; rw [B.shifted_row]; exact B.words_exist _
open Submodule
lemma tMoves (u:E4)(x:H)(h:x∈B.pointShelf): S.unit.translation u x∈ B.pointShelf:=by
 refine closure_minimal (s:=(B.inH:Set H)) (t:=S.unit.translation u ⁻¹' ↑B.pointShelf) ?_ (B.inH.isClosed_topologicalClosure.preimage (S.unit.translation u).continuous) h
 rintro _ ⟨a,t,rfl⟩; exact B.inH.le_topologicalClosure (mem_map_of_mem (B.shift_write u a t))
local notation "Q"=> B.pointShelf
lemma tAway (u:E4)(x:H)(h:x∈ Qᗮ): M S u x∈ Qᗮ:= fun y p=> by rw [tboth]; exact inner_right_of_mem_orthogonal (B.tMoves _ _ p) h
noncomputable abbrev sideMirror:= B.pointShelf.reflection
noncomputable abbrev editR : H.Op:= B.sideMirror.toContinuousLinearEquiv.toContinuousLinearMap
lemma blocks_t (x:H)(u:E4): (Q).reflection (M S u x)= M S u ((Q).reflection x):=by
 let a:H:= (Q).starProjection x; have he:a ∈ Q:= ((Q).orthogonalProjectionOnto x).2
 let v:H:=x-a; have h:v∈ Qᗮ:= sub_starProjection_mem_orthogonal x
 have ht:v+a=x:=sub_add_cancel x a
 calc _=(Q).reflection (M S u (v+a)):= congrArg (fun x:H=>(Q).reflection (M S u x)) ht.symm
      _ = _:= by
       rw [← ht]; rw [map_add,map_add,map_add,map_add]; rw [reflection_mem_subspace_eq_self he, reflection_mem_subspace_eq_self (B.tMoves u a he),reflection_mem_subspace_orthogonalComplement_eq_neg h,reflection_mem_subspace_orthogonalComplement_eq_neg (B.tAway u v h),map_neg] -- nth_rw occurrence? let a v expanded not spotted. inspect
lemma across_spectrum (x:H) : S.ℚmeasure.diagonal ((Q).reflection x)=S.ℚmeasure.diagonal x:= by
 apply Measure.ext_of_charFun; funext u;
 rw [S.joint,S.joint,← B.blocks_t x u]; exact LinearIsometryEquiv.inner_map_map ..
lemma clockAccount {Z:H.Op} {f:E4→ℂ}(h:Registers S.ℚmeasure f Z): Commute B.editR Z:=by
 let A:=B.editR; let Y:= A * Z * A; have hY(x:H): Y x= (Q).reflection (Z ((Q).reflection x)):= rfl
 have he(x:H): inner ℂ x (Y x) = inner ℂ ((Q).reflection x) (Z ((Q).reflection x)):=by
    rw [hY,← LinearIsometryEquiv.inner_map_map (Q).reflection x, reflection_reflection]
 have hz: Y = Z:= Registers.single (f:=f) (P:=S.ℚmeasure) ⟨h.price,fun x=> by rw [he,h.awakes,B.across_spectrum]⟩ h
 have hl:A*A=(1:H.Op):= by ext x; exact (Q).reflection_reflection x
 change A*Z= Z*A; refine ((mul_one _).symm.trans ((congrArg (fun v:H.Op=> (A*Z)*v) hl.symm).trans ?_)); -- lhs wrongly factor A. recompute Y=A Z A; goal (A Z)(A A) ...
 unfold Y at hz; rw [← mul_assoc,hz]
lemma registeredMoves {Z:H.Op} {f:E4→ℂ} (h:Registers S.ℚmeasure f Z)(x:H)(p:x∈ Q): Z x∈ Q:=by
 have t:= DFunLike.congr_fun (B.clockAccount h).eq x; change (Q).reflection (Z x)=Z ((Q).reflection x) at t; apply (reflection_eq_self_iff _).1; rw [t,reflection_mem_subspace_eq_self p]
lemma registeredAway {Z:H.Op} {f:E4→ℂ} (h:Registers S.ℚmeasure f Z)(x:H)(p:x∈ Qᗮ): Z x∈ Qᗮ:=by
 intro a z; rw [← ContinuousLinearMap.adjoint_inner_left]; exact inner_right_of_mem_orthogonal (B.registeredMoves h.adjoint a z) p
lemma warmMoves (t:ℝ≥0) (x:H)(p:x∈ B.pointShelf): S.E t x∈ B.pointShelf:= B.registeredMoves (costT S t) x p
lemma zoneMoves (s:Set E4)(t:MeasurableSet s)(x:H)(w:x∈ B.pointShelf): S.ℚmeasure.region s x∈B.pointShelf:= B.registeredMoves (Registers.box _ t) x w
-- region counts on an actual projection to Sh. Can equip with Orbit, S remains original!
noncomputable abbrev station : Hilbert := { space:= B.pointShelf }
local notation "R"=> B.station
noncomputable def joinT : Orbit R E4 where
 translation x := (S.unit.translation x).restrict (p:=Q) (q:=Q) (fun a p=> B.tMoves x _ p) -- check lemma
 origin := by ext1 v; apply Subtype.ext; exact DFunLike.congr_fun S.unit.origin v.val
 sends i j:=by ext1 v; apply Subtype.ext; exact DFunLike.congr_fun (S.unit.sends i j) v.val
 unitary i v:= S.unit.unitary i v.val
 moves v:= Continuous.subtype_mk (S.unit.moves v.val) _ -- check type
lemma buys_t (x:E4)(v:B.station) : (B.joinT.translation x v).1=S.unit.translation x v.1:= rfl
lemma sees_m (x:B.station): B.joinT.P.diagonal x=S.ℚmeasure.diagonal x.val:=by
 apply Measure.ext_of_charFun; funext b; rw [B.joinT.total, S.joint]; rfl
lemma sees_zone (s:Set E4)(t:MeasurableSet s)(x:B.station): (B.joinT.P.region s x).1=S.ℚmeasure.region s x.val:= by
 let Y:= (S.ℚmeasure.region s).restrict (p:=Q) (q:=Q) (fun x p=>B.zoneMoves s t x p);
 suffices h:B.joinT.P.region s=Y by rw [h]; rfl
 refine Registers.single (Registers.box B.joinT.P t) ⟨(Registers.box B.joinT.P t).price, fun x=>?_⟩ -- goal h:
 rw [B.sees_m x]; exact (Registers.box _ t).awakes x.val
end Carton
end YM.SatinWFixed
