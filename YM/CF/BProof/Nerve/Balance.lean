import YM.CF.BProof.Nerve.Shard
/-! Use weighted Voronoi gaps instead of Delaunay lemma. This surrogate has
 dimension-4 *abstract simplices of barycentric weights*, used only in making
 the Basic maps. No eta' for other distances needed: can use any MinAbs tie lift beyond.
-/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 4800
set_option maxHeartbeats 780000
noncomputable section
namespace YM.CF.BProof.Mesh.Nerve
open Lattice Function Finset Equiv Regard Rows Sleet
open scoped BigOperators Classical
variable {n:Side}{C A:Type*}{s z l k R d:ℕ}
abbrev Quint(n:Side):= Fin 6→Site n
abbrev value(i:Cover):= fun x:Axis=>(i x:ℝ)
abbrev Bunch:=Fin 6 → ℝ
def Wind(c:Bunch)(V:Fin 6 → Axis→ℝ) :Prop:= (∑ i,c i)=0 ∧ (∀ j:Axis,∑ i:Fin 6,c i* V i j =0) ∧ (∀ i,|c i| ≤1)∧ ∃ i,|c i|=1
private theorem yieldZ (V:Fin 6→Axis→ℝ):∃ c,Wind c V:=by
 let P(i): Fin 5→ℝ:= Fin.cons 1 (V i); have hp: ¬LinearIndependent ℝ P :=fun h=>by have he:=h.fintype_card_le_finrank; simp at he
 obtain ⟨c,H,i,h⟩:=Fintype.not_linearIndependent_iff.mp hp; have ht(j:Fin 5): ∑ x:Fin 6,c x*P x j=0:=by have ht:=congrFun H j; simpa using ht
 obtain ⟨x,-,he⟩:=exists_max_image (f:=fun i=>|c i|) univ univ_nonempty; set V0:=|c x|; have hv:0< V0:= lt_of_lt_of_le (abs_pos.mpr h) (he i (mem_univ _)); refine ⟨V0⁻¹ • c,?_,?_,?_,x,?_⟩ -- ∑ bool e
 · have hp:= ht 0; simp_rw [P,Fin.cons_zero,mul_one] at hp; simp [←mul_sum,hp]
 · intro j; have ht:=ht j.succ; simp_rw [P,Fin.cons_succ] at ht; simp [mul_assoc, ←mul_sum, ht]
 · intro j; have hp: |c j|≤V0:= he j (mem_univ _); rw [Pi.smul_apply,smul_eq_mul,abs_mul,abs_of_pos (by positivity)]; exact (mul_le_mul_of_nonneg_left hp (by positivity)).trans_eq (inv_mul_cancel₀ (ne_of_gt hv))
 rw [Pi.smul_apply,smul_eq_mul,abs_mul,abs_of_pos (by positivity),show |c x|=V0 from rfl,inv_mul_cancel₀ (ne_of_gt hv)]
abbrev arms(X:Quint n) := fun x=> lift (X x-X 0)
abbrev armS(X:Quint n)(P:Site n):=fun i=> lift (X i-P)
abbrev stakes(X:Quint n)(c:Bunch):Prop:= Wind c (value ∘ arms X)
private def enact(f:Bunch→ Prop)(p:∃ y,f y) := Classical.choose p
def wind (X:Quint n) :Bunch:= enact (stakes X) (yieldZ _)
lemma permit(X:Quint n):Wind (wind X) (value ∘ arms X):=Classical.choose_spec (yieldZ _)
def lead(X:Quint n):=Classical.choose (permit X).2.2.2
lemma lead_p(X:Quint n):|wind X (lead X)|=1:= Classical.choose_spec (permit X).2.2.2
-- distances.Rigid spins
lemma yaw{c:Bunch}(x:Fin 6→ Cover)(p:Wind c (value∘x))(s:Signed):Wind c (value∘s.act∘x):=by -- c implicit bad
 refine ⟨p.1,fun j=> ?_,p.2.2⟩; obtain ⟨j,rfl⟩:=s.perm.surjective j; have h:=p.2.1 j; unfold Function.comp value at h ⊢; simp_rw [Signed.act_at]; split; simp [Finset.sum_neg_distrib,h]; exact h
lemma fold(e:Signed)(x:Site n)(V:Quint n)(p:∀ i,separation (V i) (V 0) ≤ 2*(King*s))(h:SmallN s n): let Y:= facet e x ∘ V; wind Y=wind V∧lead Y=lead V:=by
 intro Y; have he:arms Y=e.act ∘ arms V:=funext fun i=> rel_turn _ _ _ _ (p i) h; have hx:stakes Y=stakes V:=funext fun c=> propext <| by
   unfold stakes; rw [he]; refine ⟨fun p=> ?_,fun p=> yaw _ p e⟩; have hv:Wind c (value∘ (e⁻¹.act ∘ e.act ∘ arms V)):=yaw _ p _; convert! hv; ext u v; simp -- tune Proof
 have hg(f g:Bunch→Prop)(h:f=g)(p:∃ i,f i)(v:∃ i,g i): enact f p=enact g v:=by subst g; rfl
 have hu(c d:Bunch)(h:c=d)(p:∃ i,|c i|=1)(v:∃ i,|d i|=1): Classical.choose p=Classical.choose v:=by subst d; rfl
 have hw:wind Y=wind V:= hg (stakes Y) _ hx _ _ -- motive dependent simp choose proof
 refine ⟨hw,?_⟩; exact hu _ _ hw _ _ -- choose Exists motive

def Mode(s:ℕ)(X:Quint n)(f:Site n→ ℝ)(x:Site n) :ℝ:=∑ i,wind X i * (sizeD s (X i) x+ f (X i))
def Drift(s:ℕ)(X:Quint n)(f:Site n→ℝ):ℝ:= Mode s X f (X 0)
local notation "Sm"=> King*s
-- across x.X 0. translations in centred lift.Spin.Real
lemma orbit_sum (X:Quint n)(f:Site n→ℝ)(x:Site n)(p:∀ i,separation (X i) x≤ Halo*s) (q:SmallN s n):Mode s X f x=Drift s X f:=by
 let V:= arms X; let Y:=lift (X 0-x); let g(i:Fin 6): Cover:= lift (X i-x); let W:= value∘ V; let c:=wind X; have ht:=permit X; let t:=(s:ℝ)^2; have hy:2*(Halo*s) ≤ Sm:= by unfold King; nlinarith
 have hu(i):g i=V i + Y:=rel_sum (X i) (X 0) x (by have ht:=p 0; have he:=separation_triangle (X i) x (X 0); rw [separation_comm _ x] at ht; linarith [p i]) ((p 0).trans (by omega)) q
 unfold Drift Mode sizeD; simp_rw [mul_add,mul_sum]; rw [sum_add_distrib,sum_add_distrib,sum_comm (s:=univ),sum_comm (s:=univ) (f:=fun i j=> wind X i * (_:ℝ))] -- tune pattern
 refine congrArg (·+_) (?_); apply sum_congr rfl; intro j _
 let a:ℝ:=Y j; have u(i): (g i j:ℝ)= W i j + a:= by rw [hu,Pi.add_apply]; exact Int.cast_add ..
 change ∑ i, c i * ((g i j:ℝ)^2 /t)=∑ i,c i * ((W i j)^2/t); simp_rw [u, show ∀ i,c i*((W i j + a)^2/t)= c i*((W i j)^2/t)+(2*a/t)*(c i*W i j)+(a^2/t)*c i from fun i=>by ring,Finset.sum_add_distrib,← mul_sum]; rw [show ∑ i, c i* W i j=_ from ht.2.1 j,show ∑ i,c i=_ from ht.1]; ring
end YM.CF.BProof.Mesh.Nerve
