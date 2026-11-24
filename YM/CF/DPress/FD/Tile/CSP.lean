import YM.CF.DPress.FD.Tile.Clerk
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.DPress.FD
open Function Set Metric Filter SU MeasureTheory Ramp Row Frame
open scoped Topology BigOperators NNReal ENNReal Matrix.Norms.Frobenius Classical
attribute [local instance] Gauge.frobInner
variable {I K:Type*}[Fintype I][Fintype K]{m:ℕ}
namespace Warm
scoped instance : BorelSpace Key:=⟨rfl⟩
variable (S: Finset I)(T:Finset K)(P:ℝ)
abbrev Receipt (F:Paint I K m)(Q:Paint I K m):Prop:= EqOn Q F (boundary S) ∧ Clear (facet S) Q T ∧ Tends S Q P
abbrev Land(F:Paint I K m)(A: Pair K I m):Prop:= EqOn (faceF A.1) F (boundary S) ∧ Clear (facet S) (faceF A.1) T ∧ ((∀ i ∈ facet S,Frame.Fits 0 ((A.1 i).val) ((A.2 i).val))∧Ramp.Speed (facet S) (faceF A.2) P)
lemma feltS : IsClosed {X:Paint I K m×Pair K I m | Land S T P X.1 X.2}:=by
 refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_)); · change IsClosed {X: Paint I K m ×Pair K I m  | ∀ x∈boundary S,faceF X.2.1 x=X.1 x}; simp_rw [setOf_forall]; refine isClosed_iInter fun i=> isClosed_iInter fun j=>?_ ; exact isClosed_eq (by unfold faceF; fun_prop) (by fun_prop)
 · change IsClosed {X:Paint I K m×Pair K I m  |  Clear (facet S) (faceF X.2.1) T}; unfold Clear Skip; simp_rw [setOf_forall]; refine isClosed_iInter fun i=> isClosed_iInter fun j=>isClosed_iInter fun y=>isClosed_iInter fun z=> ?_; exact isClosed_eq ((Continuous.comp (continuous_apply y) (show Continuous (fun x:Paint I K m × Pair K I m=>faceF x.2.1 i) from by unfold faceF; fun_prop))) continuous_const
 · change IsClosed {X:Paint I K m×Pair K I m | ∀ i ∈ facet S,Frame.Fits 0 ((X.2.1 i).val) ((X.2.2 i).val)}; simp_rw [setOf_forall]; refine isClosed_iInter fun i=>isClosed_iInter fun j=>?_ ; exact (Frame.aloof (I:=K) 0).preimage (f:=fun x:Paint I K m×Pair K I m=> ((x.2.1 i).val,(x.2.2 i).val)) (by fun_prop)
 change IsClosed {X:Paint I K m×Pair K I m | Ramp.Speed (facet S) (faceF X.2.2) P}; unfold Ramp.Speed; simp_rw [setOf_forall]; refine isClosed_iInter fun i=> isClosed_iInter fun j=>isClosed_iInter fun y=> isClosed_iInter fun z=>?_ ; exact isClosed_le (by unfold faceF; fun_prop) continuous_const
lemma Seam.backward {x y z: Paint I K m}{D:Set (Ramp I m)}{a:ℝ}(v: Seam D y z a)(e:EqOn x y D):Seam D x z a:= ⟨fun i p=> e p ▸ v.legal p,fun i p=>by rw [e p]; exact v.pay i p,v.e⟩
variable [Nonempty K]
lemma hike(x:Paint I K m)(h:∃ G, Receipt S T P x G):∃ g, Land S T P x g:=by
 obtain ⟨E,z,C,t,q⟩:=h; let f(y): veil K:= if p:y∈ facet S then ⟨E y,q.legal p⟩ else ⟨_,Frame.defaultP K⟩; let g(y): veil K:= if p:y∈ facet S then ⟨t y,q.shape p⟩ else ⟨_,Frame.defaultP K⟩; let i:= faceF f; let l:= faceF g; have ht: EqOn i E (facet S):= by intro k p; unfold i faceF f; rw [dif_pos p] -- no goals?
 have he:EqOn t l (facet S):=by intro k p; unfold l faceF g; rw [dif_pos p]
 have hy:= Seam.backward (q.congr he) ht; exact ⟨(f,g),fun i p=>(ht (border p)).trans (z p),fun k p=> (show Skip (i k) T from ht p ▸ C k p),hy.pay,hy.e⟩
local instance : CompactSpace (veil K) := isCompact_iff_compactSpace.mp (Frame.pact K)
local instance : Nonempty (veil K):=⟨⟨_,Frame.defaultP K⟩⟩
scoped instance : SecondCountableTopology Key:= inferInstanceAs (SecondCountableTopology (F→F→ℂ))
scoped instance : TopologicalSpace.MetrizableSpace Key:= inferInstanceAs (TopologicalSpace.MetrizableSpace (F→F→ℂ))
lemma poll : ∃ φ:Paint I K m→Paint I K m, Measurable φ ∧ (∀ x,(∃ y, Receipt S T P x y)→Receipt S T P x (φ x))∧∀ x y, EqOn x y (boundary S)→φ x = φ y:=by
 obtain ⟨F,h,t⟩:= BPress.choose_if_closed (X:=Paint I K m) (Y:=Pair K I m) _ (feltS S T P); let f(x:Paint I K m)(i:Ramp I m):= if i∈ boundary S then x i else 0; let P'(x:Paint I K m):= faceF (F (f x)).1
 have h0(x:Paint I K m): EqOn x (f x) (boundary S):= fun i p=> (if_pos p).symm
 refine ⟨P',measurable_pi_lambda _ fun i=>?_,fun x v=>?_, fun x y v=> (congrArg (fun z:Paint I K m=> faceF (F z).1) (show f x=f y from funext (fun i=>by unfold f; split; exact v (by assumption); rfl)))⟩ -- tune notation
 · have hf: Measurable f:= measurable_pi_lambda _ (fun i=>by unfold f; split; exact measurable_pi_apply i; exact measurable_const); exact measurable_subtype_coe.comp ((measurable_pi_apply i).comp (measurable_fst.comp (h.comp hf)))
 obtain ⟨y,u,q,v⟩:=v; have hw: Receipt S T P (f x) y:= ⟨u.trans (h0 x),q,v⟩; obtain ⟨hq,u,v',h⟩:=t (f x) (by obtain ⟨u,t⟩:= hike S T P (f x) ⟨y,hw⟩; exact ⟨u,t⟩); exact ⟨hq.trans (h0 x).symm,u,faceF (F (f x)).2,⟨fun i _=> ((F (f x)).1 i).property,v',h⟩⟩ -- Shape by subtype property
end Warm
end YM.CF.DPress.FD
