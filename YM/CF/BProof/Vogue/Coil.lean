import YM.CF.BProof.Vogue.Scene
/-! Core FD patent. States explicit latent field and finite-region penalty. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Vogue
open Function Filter MeasureTheory ProbabilityTheory Skye Spire Lattice Wilson Mesh Shore Finset Equiv
open scoped Topology BigOperators NNReal ENNReal Classical
variable {X Y:Type}{n:Side}{d u:ℝ}{F: Orbit n→ Pane n} {k r q L:ℕ}
private theorem reprint(P:Spice n X d u k L) [Fintype Y](e:X≃Y): Nonempty (Spice n Y d u k L):=by
 let Ψ: Y→ Pane n→ Pane n:= P.P ∘ e.symm; refine ⟨e.nonempty_congr.mp P.ne,inferInstanceAs (Finite Y),Ψ,fun i=>P.ok _,?_,?_⟩ -- Nonempty nested?
 · intro s i k; obtain ⟨E,h⟩:= P.ride s i k; refine ⟨(e.symm.trans E).trans e, fun i U=>?_⟩; simpa only [coe_trans,Function.comp_apply, symm_apply_apply,Ψ] using h (e.symm i) U
 -- syntax local opens fail?
 intro a b t; obtain ⟨E,h⟩:=P.gap a b t; let U:= prodCongr e.symm e.symm; let V: Perm (Y × Y):=(U.trans E).trans U.symm
 refine ⟨V,Regard.penMake _ _ _ _ fun x=>?_⟩; have he:e.symm ((V x).1)=(E (U x)).1∧e.symm ((V x).2)=(E (U x)).2:= by simp [V,U]
 obtain ⟨i,j,k,l⟩:= Regard.fromPen h (U x); unfold Ψ; simp only [Function.comp_apply,he.1,he.2]; exact ⟨i,j,k,l⟩

/-- Available property on history Loom. Range R buys the deterministic stencil in the
latent law representation for fixed world, and ALSO dependence range on world outputs.
Use only after averaging tags (incl. the identity action on the frame coordinates).
Finite-dependence in product Haar g costs an additional + successive halo
radius when doing spatial tests. -/
structure Quartz(n:Side)(q:ℕ)(u:ℝ)(R:ℕ)(F:Orbit n→ Pane n) where
  d : ℝ
  k : ℕ
  L : ℕ
  fit:k ≤ R
  pay:L ≤ R
  spice:Spice n (Fin q) d u k L
  bill:Measurable F
  joint_eq(U:Pane n): (depot n).map (fun t=>(frameP t,F (U,t)))=((paperMeas (Fin q)).prod (rootM n)).map (joint spice U)
def Cream (u:ℝ)(R:ℕ)(F:Orbit n→ Pane n): Prop:=∃ q:ℕ,Nonempty (Quartz n q u R F)
namespace Quartz
variable (Q:Quartz n q u r F)
lemma lawful(U:Pane n): (depot n).map (fun t=>F (U,t))=((paperMeas (Fin q)).prod (rootM n)).map (fun t=> (joint Q.spice U t).2):=by
 haveI := Q.spice.ne; let h(t:Ids n):=(frameP t,F (U,t)); have hm:Measurable h:= frameM.prodMk (Q.bill.comp measurable_prodMk_left); let g:=joint Q.spice U
 change Measure.map (Prod.snd ∘ h) (depot n)=Measure.map (Prod.snd ∘ g) _
 rw [← Measure.map_map measurable_snd hm, Q.joint_eq, Measure.map_map measurable_snd (joint_m ..)] -- tune n
end Quartz
lemma publication(x y:ℝ)(p:0<x)(f:0<y):∃ k N:ℕ,∃ u:ℝ,0<u∧u≤y∧ ∀ n:Side,N ≤(Cube.More n).val→ ∃ Φ: Skye.Orbit n→Pane n,Roof n u x k Φ ∧ Cream u k Φ:=by
 obtain ⟨α,a,T⟩:= taxon p; obtain ⟨L,r,N,u,hU,t,Q⟩:= Fancy.bright_spice α y a f
 let k:=r+L; have hz:r≤k:= Nat.le_add_right ..; refine ⟨k,N,u,hU,t,fun n h=>?_⟩; obtain ⟨K,P⟩:=Q n h; letI :Finite K:= P.some.book; letI:=Fintype.ofFinite K; obtain ⟨V⟩:= reprint P.some (Fintype.equivFin K); haveI:=V.ne
 exact ⟨conic V k,covers_toit V hz x (T n),Fintype.card K,⟨α,r,L,hz,Nat.le_add_left ..,V,conicM V k,ident V hz (by unfold k; omega)⟩⟩ -- nested nonempty syntax
end YM.CF.BProof.Vogue
