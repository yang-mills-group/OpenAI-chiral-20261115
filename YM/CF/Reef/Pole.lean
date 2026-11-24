import YM.CF.Reef.Ice
set_option autoImplicit false
noncomputable section
namespace YM.CF.Reef
open Function Filter NormedSpace Fock SU Spire Lattice Wilson RG Finset
open scoped Topology Matrix.Norms.Frobenius InnerProductSpace ContDiff
variable {ι:Type*}
abbrev echo(x:ι→SU.group.El):ι→SU.group.El:= fun i=> qG (x i)
lemma echo2(x:ι→SU.group.El): echo (echo x)=x:=funext fun _=>q0 _
lemma echo_r [AddCommGroup ι][One ι](U:Links ι SU.group.El)(i)(d:Step): d.read (echo U) i=qG (d.read U i):=by unfold Step.read; split; symm; exact map_inv qG _; rfl
lemma echo_t [AddCommGroup ι][One ι](U:Links ι SU.group.El)(w:Walk)(i): travel (echo U) i w=qG (travel U i w):=by induction w generalizing i <;> simp_all only [travel, echo_r, map_one,map_mul] -- tune
lemma echo_p{n:Side}(x:Config SU.group n)(i:Signed)(t:Site n): Lattice.pull i t (echo x)=echo (Lattice.pull i t x):=funext fun _=> echo_r ..
lemma invoke (P:Patch)(U:CoverConfig SU.group)(F:P.Frame SU.group) (C:KernelChoices):
 (P.score (echo U) (echo F)=P.score U F) ∧ (P.usesMin C (echo U) ↔ P.usesMin C U)∧ P.eligible C (echo U)=P.eligible C U:=by
 have he(x:P.Frame SU.group)(a b n):P.via (echo x) (echo U) a b n=qG (P.via x U a b n):=by simp only [Patch.via,echo_t,map_mul,map_inv]
 have hp(r): P.axial (echo U) r= echo (P.axial U r):= funext fun i=>echo_t ..
 have ht: P.facesum (echo U)=P.facesum U:=by unfold Patch.facesum faceValue; simp_rw [echo_t,cool]
 refine ⟨?_,?_,?_⟩
 · simp_rw [Patch.score,he,cold]
 · simp_rw [Patch.usesMin,hp,he,cool]
 have hv(i):P.axialCost (echo U) i=P.axialCost U i:=by unfold Patch.axialCost; simp_rw [hp,echo]; simp only [← map_inv,← map_mul,cool]
 ext i; simp_rw [Patch.eligible,hv,ht]
lemma sing_p {P:Patch}{C:KernelChoices}(h:P.Branches C SU.group)(U:CoverConfig SU.group)(i): P.frame C (echo U) i= echo (P.frame C U i) ∧ P.frameMass C (echo U) i=P.frameMass C U i:=by
 obtain ⟨_,hp,hv⟩:=invoke P U 1 C
 rw [Patch.frame,Patch.frame,Patch.frameMass, Patch.frameMass, hv]; by_cases k:P.usesMin C U
 · simp only [if_pos k, if_pos (hp.mpr k),and_true]
   apply (h.frame_unique (echo U) (hp.mpr k)).unique (show P.minimizing (echo U) _ from (P.min_exists (echo U)).choose_spec); let F:=P.selected U; let u:= (show P.minimizing U F from (P.min_exists U).choose_spec); refine ⟨?_,fun i g=>?_⟩; change qG (F _)=1; rw [u.1,map_one]
   rw [(invoke P U _ C).1]; calc
    _ ≤ P.score U (echo i):=u.2 (echo i) (by unfold echo; rw [g,map_one])
    _ = P.score (echo U) (echo (echo i)):= (invoke P U _ C).1.symm
    _ = _:=by rw [echo2]
 simp only [if_neg k,if_neg (fun x=> k (hp.mp x)), ↓reduceIte,and_true]; funext x; unfold Patch.axial; simp_rw [echo_t]; simp only [echo,map_mul,map_inv]
lemma pays(P:Patch)(x:P.Connector SU.group)(v): P.bondCost (echo x) (qG v)=P.bondCost x v:=by unfold Patch.bondCost echo; simp only [←map_inv, ←map_mul,cold]
lemma rhyme {P:Patch}{C:KernelChoices}(h:P.Branches C SU.group) (x:P.Connector SU.group)(v): P.predict C (echo x) v=qG (P.predict C x v) ∧ P.predictorMass C (echo x) v=P.predictorMass C x v:=by
 let H(y):=P.best (G:=SU.group) y
 have he(y) (v):P.bondCost y (H y) ≤ P.bondCost y v:= (P.bond_min y).choose_spec v
 have hp(y) :P.bondCost (echo y) (H (echo y)) ≤ P.bondCost y (H y):= (he (echo y) (qG (H y))).trans_eq (pays P y _)
 have hl: P.bondCost x (H x)≤ P.bondCost (echo x) (H (echo x)):=by have hx:=hp (echo x); rwa [echo2] at hx
 have ht:P.usesBest C x ↔ P.usesBest C (echo x):=⟨fun k=> lt_of_le_of_lt (hp x) k, fun k=>lt_of_le_of_lt hl k⟩
 unfold Patch.predict Patch.predictorMass
 by_cases g:P.usesBest C (echo x)
 · rw [if_pos g, if_pos g,if_pos (ht.mpr g),if_pos (ht.mpr g)]; refine ⟨?_,rfl⟩
   apply (h.predictor_unique (echo x) g).unique (he (echo x)); intro v; obtain ⟨y,rfl⟩:=qG.surjective v; rw [pays,pays]; exact he x y
 rw [if_neg g,if_neg g, if_neg (fun k=>g (ht.mp k)),if_neg (fun k=>g (ht.mp k))]; exact ⟨rfl,rfl⟩
variable {c f:Side}{S:StepData c f}
lemma proceeds (h:S.patch.Branches S.kernel SU.group)(x:Config SU.group f)(t:S.Choices): S.prediction (echo x) t=echo (S.prediction x t) ∧ S.likelihood (echo x) t=S.likelihood x t:=by
 have he(i):expandAt i (echo x)=echo (expandAt i x):=rfl
 have hv(i y): S.frames (echo x) t.1 i y= qG (S.frames x t.1 i y):= congr_fun (sing_p h (expandAt (S.ratio.embed i) x) _).1 y
 have ht(e):S.connector (echo x) t.1 e=echo (S.connector x t.1 e):=by funext i; unfold StepData.connector; simp only [he,echo_t,hv,echo,map_mul,map_inv]
 refine ⟨funext fun i=>?_,?_⟩
 · unfold StepData.prediction; rw [ht]; exact (rhyme h _ _).1
 simp_rw [StepData.likelihood,ht,(rhyme h _ _).2, he,(sing_p h _ _).2] -- tune
end YM.CF.Reef
