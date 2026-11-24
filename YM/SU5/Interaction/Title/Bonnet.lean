import YM.SU5.Interaction.Title.Scooter
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 650000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
variable {P:BudgetPoint}{X Y Z:Aura n}{V W:Firing n}{D:Support (More n)}
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
local notation "JS"=> Single n
local notation "SO"=> Support (More n)
local notation "Γ"=> (FC (Dwell n))
/- Price Title at one support. Actually gets qualifications on arbitrary end supports &
 static D. Keep explicit finite decorations even when totaling values. -/

variable {h a v w c s t:ℝ}{δ:ℕ}{F G:Firing n}
structure Fringe (P:BudgetPoint)(h:ℝ)(F:Firing n)(X:Aura n)(c:ℝ): Prop where
 pay : ∃ Y:Finset (Dwell n)→ℝ, 0≤Y∧(∑ i:Finset (Dwell n),h^i.card*Y i)≤c∧ ∀ V:Orbit n, V.1∈σX P X ∅→∀ D:Support (More n),∀ i:Finset (Dwell n), Pence P.order (fun y:tangD n=> F (pressQ P D V.1 y,V.2) i ∅) 0 (Y i)
-- no need Halo δ rules for Fringe.Lib.
def BirthRight (P:BudgetPoint)(h:ℝ)(F:Firing n)(X:Aura n)(c:ℝ):Prop:=∀ Y:Aura n,X.val ⊆ Y.val→Fringe P h F Y c

lemma Fringe.whole (p:AuraOp P X ∅ F h c): Fringe P h F X c:=by obtain ⟨V,h,f,a⟩:=p; exact ⟨⟨fun i=>V i ∅,fun i=>h i ∅,by simpa using f ∅,fun W p D i=> a W p D (empty_subset _) i ∅⟩⟩
lemma Fringe.plus (p:Fringe P h F X c)(q:Fringe P h G X a): Fringe P h (F+G) X (c+a):= by
 obtain ⟨V,v,f,a⟩:=p.pay; obtain ⟨W,w,u,c⟩:=q.pay; refine ⟨⟨V+W,add_nonneg v w,?_ ,fun i r D x=>(a i r D x).add (c i r D x)⟩⟩; simp_rw [Pi.add_apply,mul_add,sum_add_distrib]; exact add_le_add f u
lemma Fringe.raise (p:Fringe P h F X c)(q:c≤a):Fringe P h F X a:=by obtain ⟨A,v,p,h⟩:=p.pay; exact ⟨A,v,p.trans q,h⟩
lemma Fringe.format (p:Fringe P h F X c)(z:ℂ):Fringe P h (z • F) X (‖z‖*c):=by
 obtain ⟨A,h,f,p⟩:= p.pay; refine ⟨⟨fun i=>‖z‖*A i, fun i=>mul_nonneg (norm_nonneg z) (h i),?_,fun W u D i=>(p W u _ i).σ z⟩⟩; simp_rw [mul_left_comm (_^_) ‖z‖, ←mul_sum]; exact mul_le_mul_of_nonneg_left f (norm_nonneg _)
lemma Fringe.pass (p:F=0): Fringe P h F X 0:=by rw [p]; let T:=Title.free (P:=P) (h:=h) (δ:=0) (X:=X); apply Fringe.whole; exact ⟨(T.scope _ (Subset.refl _) ∅ (empty_subset _) (by simp [Lattice.halo])).vet⟩
lemma Fringe.sumP {ι:Type*}(s:Finset ι)(F:ι→Firing n)(v:ι→ℝ)(hF:∀ i∈s,Fringe P h (F i) X (v i)): Fringe P h (∑ i∈s,F i) X (∑ i∈s,v i):=by induction s using Finset.induction_on with | empty=> rw [sum_empty,sum_empty]; exact Fringe.pass rfl | insert i s t ih=> rw [sum_insert t,sum_insert t]; exact (hF i (mem_insert_self ..)).plus (ih fun i v=> hF i (mem_insert_of_mem v))
lemma Fringe.zeroem (p:∀ V:Orbit n,V.1 ∈ σX P X ∅→∀ i:Finset (Dwell n), F V i ∅=0): Fringe P h F X 0:=by
 refine ⟨0,le_rfl,by simp,fun V v D i=>?_⟩; have h:= Pence.const (k:=P.order) (0:tangD n) (0:ℂ); rw [norm_zero] at h; change Pence _ _ _ 0; apply h.germ; filter_upwards [Vow.tick (Y:=D) v.1] with y w; exact (p (pressQ P D V.1 y,V.2) ⟨w,empty_subset _⟩ i).symm
lemma Fringe.leftP (p: AuraOp P X ∅ F h c)(t:0≤ c)(q:Fringe P h G X a):Fringe P h (F*G) X (c*a):=by
 obtain ⟨A,e,a,c⟩:= p.pay; obtain ⟨B,f,b,d⟩:= q.pay
 let C (i:Finset (Dwell n)):= ∑ r: Finset (Dwell n),A i r*B r
 refine ⟨⟨C,fun i=>sum_nonneg fun _ _=> mul_nonneg (e ..) (f _),?_, fun U p Z i=>?_⟩⟩
 · unfold C; refine le_trans ?_ (mul_le_mul_of_nonneg_left b t); simp_rw [mul_sum]; rw [sum_comm]; apply sum_le_sum; intro j _; simp_rw [←mul_assoc, ←sum_mul]; exact mul_le_mul_of_nonneg_right (a j) (f j)
 let V(y:tangD n):=((pressQ P Z U.1 y,U.2):Orbit n); refine Pence.germ (Pence.money (G:=fun r=>fun y=>F (V y) i r* G (V y) r ∅) (fun r (_:r∈Finset.univ)=> (c U p Z (empty_subset _) i r).twice (d U p Z r))) (Eventually.of_forall fun y=>?_); rw [Finset.sum_apply]; exact (Matrix.mul_apply ..).symm
lemma BirthRight.whole (p:Title P h δ F X c): BirthRight P h F X c:= fun Y v=> Fringe.whole ⟨(p.scope Y v ∅ (empty_subset _) (by simp [Lattice.halo])).vet⟩
lemma BirthRight.prodL (p:Title P h δ F X c)(q:BirthRight P h G X a):BirthRight P h (F*G) X (c*a):= fun Y v=> (q Y v).leftP ⟨(p.scope Y v ∅ (empty_subset _) (by simp [Lattice.halo])).vet⟩ p.pay
lemma BirthRight.void (p:∀ v:Orbit n, v.1∈σX P X ∅→ acts (F v) (vacuum (Dwell n))=0): BirthRight P h F X 0:=by
 intro Y v; apply Fringe.zeroem; intro V h i; have hh: acts (F V) (basisKet (∅:Finset (Dwell n)))=0:=p V ⟨grow_b (show X.val \ ∅ ⊆ Y.val \ ∅ from by rwa [sdiff_empty,sdiff_empty]) h.1,empty_subset _⟩; rw [←basis_act (F V) i ∅,hh]; rfl -- signature
lemma BirthRight.sumP {ι:Type*}(s:Finset ι)(F:ι→Firing n)(v:ι→ℝ)(hF:∀ i∈s,BirthRight P h (F i) X (v i)): BirthRight P h (∑ i∈s,F i) X (∑ i∈s,v i):=fun x t=> Fringe.sumP _ _ _ (fun i r=> hF i r x t)
lemma BirthRight.format (p:BirthRight P h F X c)(z:ℂ):BirthRight P h (z • F) X (‖z‖*c):=fun i v=> (p i v).format z
lemma BirthRight.plus (p:BirthRight P h F X c)(q:BirthRight P h G X a):BirthRight P h (F+G) X (c+a):=fun i v=>(p i v).plus (q i v)
lemma BirthRight.repaint (p:BirthRight P h F X c)(t:X.val⊆Y.val):BirthRight P h F Y c:=fun Z q=> p Z (t.trans q)
-- end price.Budget actually burns.V.
lemma Fringe.burn (p:Crate P X ∅ X F)(T:Fringe P h F X c) : Fray P h δ X ∅ (p.motion 1) c:=by
 let F':=p.motion 1; obtain ⟨A,hp,f,T⟩:=T.pay; refine ⟨⟨(p.body_s (show Medal P X.val ∅ 1 h 1 from Medal.oneT).toThemeR (Subset.refl _)),A,hp,fun x t Z s=>?_,f⟩, fun i v=>by simp [Lattice.halo]⟩ -- infer h
 refine ⟨Eventually.of_forall (fun _=> (fineShape _).allP),fun i=>?_⟩; refine (T x ⟨t,empty_subset _⟩ Z i).germ ?_; filter_upwards [Vow.tick (Y:=Z) t] with y w
 let u:Orbit n:=(pressQ P Z x.1 y,x.2); change F u i ∅= crumb (Sault.rind (coll_T P X ∅ F u*1)) i; rw [mul_one,skyF,p.pointV u ⟨w,empty_subset _⟩]
lemma Title.powerQ (T:Aura n→Firing n)(A:Aura n→ℝ)(k:∀ X, Title P h δ (T X) X (A X)): Bias δ T P h A:= ⟨fun i=> (k i).valid, fun i=>(k i).pay,fun X Y=>fun D v u q=>(k Y).scope X v D u q⟩
-- assemble Wick for any nonzero assigned family. Clean.Bias.vel.
open Bias
lemma covenant (p:3≤P.B)(F: Aura n→ Firing n)(A B:Aura n→ℝ)(pA:∀ X,Title P h δ (F X) X (A X))(pB:∀ X,BirthRight P h (F X) X (B X))(t:0≤h)(S:Support (More n))(v:∀ X:Aura n,¬ S⊆ X.val→F X=0) : WickL P h δ (Title.powerQ F A pA).payX A B (fun i Y=>F Y i) S:=by
 let Y:=Title.powerQ F A pA; refine ⟨Y.buys p t,fun X=>?_,fun X G D e F=>?_⟩
 · unfold payX; split; next d=> exact Fringe.burn _ (pB X X (Subset.refl _))
   next h=> exact (h ⟨Subset.refl _, empty_subset _,by simp [Lattice.halo]⟩).elim
 unfold payX; split
 next hx=> funext i; apply Subtype.ext; have H:=v G e; change Sault.rind (coll_T _ _ _ _ _*_)=0; rw [H]; simp [coll_T,Sault.rind]
 rfl
end YM.CF.Sour
#print axioms YM.CF.Sour.covenant
