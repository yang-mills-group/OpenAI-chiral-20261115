import Anomaly.Basis.Baton
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Vow.TreasuryFog
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tenant Tulip
open Pastry Hake Peaks Fock Branch Drapes Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Palot Cadre Rill Stax Rive Ione Larch Roots Push.AbsoluteSums.Trees Sour Py Py.Rate.BScale Mew PowerSeries
open scoped Mew
open Swell Porticus Tye Bake Neon Pressure
variable {n m N B:Side} {I:Type} [LinearOrder I] [Fintype I] {C:BudgetPoint} {h v u z w p:ℝ} {q k L':ℕ}
-- Bound tape ceiling all weights Offshell.Phase offset extra. - shape bound for each slice
local notation "θ" => mid N B
local notation "Qz" => ℂ
abbrev pilasters (L:ℕ)(C:BudgetPoint)(o:Site (mid N B))(A:RegBudget (mid N B)):ArcΦ:=∑ X:Scree.Hub (mid N B) with X.val.1=node o∧ Moto.chose L C X,pillar o (A X) C
structure AxStamp (L:ℕ)(p:BudgetPoint)(o:Site (mid N B))(A:RegBudget (mid N B))(Ψ:ArcΦ)(h u v:ℝ) :Prop where
 rights:IncX primeU A p h u
 estimate : ‖(pilasters L p o A).1-Ψ.1‖≤ v ∧ ‖(pilasters L p o A).2-Ψ.2‖*h^2≤v
 zeroish (i:Scree.Hub (mid N B))(p:i.val.1≠ node o) : A i=0
namespace AxStamp
variable {o:Site (mid N B)}{M F:RegBudget (mid N B)}{Φ Ψ:ArcΦ}
variable (H:AxStamp L' C o M Φ h u v)(Z: AxStamp L' C o F Ψ h w p)
include H Z
lemma adds_P (k:1≤h) :AxStamp L' C o (M+F) (Φ+Ψ) h (u+w) (v+p):=by
 have he:pilasters L' C o (M+F)=pilasters L' C o M +pilasters L' C o F:=by
    unfold pilasters; rw [←sum_add_distrib]; obtain ⟨A,t,u⟩:= H.rights.weight; obtain ⟨G,v,h'⟩:= Z.rights.weight; exact sum_congr rfl fun i p=> Pill_F o C h i _ _ (t _) (v _) (zero_le_one.trans k)
 refine ⟨Larch.add_v C _ _ H.rights Z.rights,?_,fun i p=> ?_⟩
 · rw [he]; let p':= H.estimate; let q:= Z.estimate; simp only [Prod.fst_add,Prod.snd_add, add_sub_add_comm]; exact ⟨(norm_add_le ..).trans (add_le_add p'.1 q.1),(mul_le_mul_of_nonneg_right (norm_add_le ..) (sq_nonneg _)).trans ((add_le_add p'.2 q.2).trans' (add_mul ..).le)⟩ -- syntax
 rw [Pi.add_apply,H.zeroish i p,Z.zeroish i p,add_zero]
omit Z
lemma scaleP (x:ℂ)(k:0≤h): AxStamp L' C o (x • M) (x • Φ) h (‖x‖*u) (‖x‖*v):=by
 obtain ⟨G,g,hv⟩:=H.rights.weight
 have he:pilasters L' C o (x • M) = x • pilasters L' C o M:=by
    unfold pilasters; rw [Finset.smul_sum]; exact sum_congr rfl fun i v=> stress_ζ x o i _ C _ (g i) k
 refine ⟨?_,?_,fun i d=> by rw [Pi.smul_apply,H.zeroish i d,smul_zero]⟩
 · refine ⟨⟨‖x‖ • G,fun i=> súe _ _ (g i) _,fun i=>?_⟩,fun _ w=> w.elim⟩
   refine le_trans ?_ (mul_le_mul_of_nonneg_left (hv i) (norm_nonneg _)); rw [mul_sum]; refine sum_le_sum fun i _=>?_ ; simp [mul_ite,BudgetPoint.mass,mul_left_comm]
 let K:=pilasters L' C o M; rw [he]; change ‖x • K.1-x • Φ.1‖≤_ ∧ ‖x • K.2 - x • Φ.2‖*h^2 ≤ _; rw [←smul_sub,norm_smul,←smul_sub,norm_smul,mul_assoc]; exact ⟨mul_le_mul_of_nonneg_left H.estimate.1 (norm_nonneg _),mul_le_mul_of_nonneg_left H.estimate.2 (norm_nonneg _)⟩
lemma riseV {a b:ℝ}(e:u≤a)(p:v≤b) : AxStamp L' C o M Φ h a b:=by obtain ⟨W,Q,v⟩:=H.rights.weight; exact ⟨⟨⟨W,Q,fun i=> (v i).trans e⟩,H.rights.face⟩,⟨H.estimate.1.trans p,H.estimate.2.trans p⟩,H.zeroish⟩
omit H
abbrev Ρpost (p:BudgetPoint)(u:ℝ):= (1+2*Moto.peka_H p.power)*u
lemma simple (A:IncX primeU M C h u)(p:1 ≤ h)(v:∀ i,i.val.1≠ Cube.node o→ M i=0) : AxStamp L' C o M 0 h u (Ρpost C u):=by
 obtain ⟨K,Z,Hv⟩:= A.weight; let G := univ.filter fun X:Scree.Hub θ=> X.val.1=node o; let F:Scree.Hub θ→ Scree.Hub θ:=id; let V:= univ.filter fun X:Scree.Hub θ=> X.val.1=node o∧ Moto.chose L' C X
 have he:G= univ.filter (fun X:Scree.Hub θ=> node o=X.val.1):= by ext; simp [G,eq_comm]
 have hx:(∑ j∈G,C.mass j.val.2 (K j)) ≤ u:=by rw [he,Finset.sum_filter]; exact Hv _
 have hq(j:Scree.Hub θ)(v:j∈G): (F j).val.1=node o:=(mem_filter.mp v).2
 obtain ⟨p',t'⟩:= quest_B o C h G F M K u (fun i _=>Z i) hq p hx V (fun i v=> mem_filter.mpr ⟨mem_univ _, (mem_filter.mp v).2.1⟩); let U:= pilasters L' C o M
 have ht: 0 ≤ Moto.peka_H C.power:=by unfold Moto.peka_H Hove.κP Haro.ξP; have h':= Hove.mpe true; have hv:= Hove.mpe false; unfold Hove.pruneQ; positivity -- tune
 have hp: 0≤u:= (norm_nonneg _).trans p'
 refine ⟨A,?_,v⟩; unfold pilasters; rw [Prod.fst_sum,Prod.snd_sum]; change ‖_-0‖ ≤ (1+2*_)*_ ∧ ‖_-0‖* _≤ _; rw [sub_zero,sub_zero]; exact ⟨p'.trans (le_mul_of_one_le_left hp (le_add_of_nonneg_right (mul_nonneg zero_le_two ht))),t'.trans (by unfold Ρpost; rw [add_mul]; exact le_add_of_nonneg_left (by linarith))⟩
end AxStamp
-- Mark hardware + post-processing Earnings.A
structure Drill (P:BudgetPoint)(q k L:ℕ)(o:Site (mid N B))(h s:ℝ)(F:Bag (mid N B))(Φ:ArcΦ)(a b c:ℝ) : Prop where
  yard:Barrage P q (grooveB k P (node o)) h F s a a
  stamp (U G: Aura (mid N B)→ ℝ)(t:Ids (mid N B))(p:∀ X,Flight P q X h (F X) (U X) (G X)): AxStamp L P o (singlePole t F p (node o)) Φ h b c -- shadow B. tune
namespace Drill
variable {X Y:Bag (mid N B)}{Ψ Φ:ArcΦ}{o:Site (mid N B)}{a b c d s t:ℝ} (A:Drill C q k L' o h s X Ψ a b c) (W:Drill C q k L' o h s Y Φ u v w)
include A W
lemma gain (p:1≤h): Drill C q k L' o h s (X+Y) (Ψ+Φ) (a+u) (b+v) (c+w):=by
 refine ⟨A.yard.plusR W.yard,?_⟩; intro B G t K; obtain ⟨Q,P,L,_⟩:=A.yard.price; obtain ⟨K',A',H,_⟩:=W.yard.price; rw [poles_up L t (node o) H K]; exact (A.stamp Q P t L).adds_P (W.stamp K' A' t H) p
omit W
lemma sizes (z:ℂ)(p:1≤h):Drill C q k L' o h s (z • X) (z • Ψ) (‖z‖*a) (‖z‖ *b) (‖z‖*c) :=by refine ⟨A.yard.swell z,?_⟩; intro F G t K; obtain ⟨Q,P,L,_⟩:=A.yard.price; rw [pole_scale L t (node o) z K]; exact (A.stamp Q P t L).scaleP z (zero_le_one.trans p)
lemma raiseP(z:a≤u)(p:b≤v)(t:c≤w):Drill C q k L' o h s X Ψ u v w:= ⟨A.yard.bigR z z,fun S V x q=>(A.stamp S V x q).riseV p t⟩
lemma downP (e:p≤ s): Drill C q k L' o h p X Ψ a b c:= ⟨A.yard.lessR e,A.stamp⟩
omit A
lemma stampS (T:Barrage C q (grooveB k C (node o)) h X s a t)(x: t≤a)(h':1≤h)(p:C.supportExponent+8/(C.B:ℝ) ≤ s)(v':3 ≤ C.B) (e:Nor.reserveT C.power C.order C.B (C.B:ℝ)⁻¹* |t|≤ u): Drill C q k L' o h s X 0 a u (AxStamp.Ρpost C u):=by
 obtain ⟨V,D,r,k,L,M⟩:=T.price; refine ⟨T.bigR le_rfl x,?_⟩; intro J A t z; rw [booth_one r t _ z t]; let W:=fun (_:Fin 1) i=> r i; apply AxStamp.simple _ h' (fun i g=>station _ _ _ W t _ (0:Fin 1) i g); apply protoInc _ W t (0:Fin 1) _ v' (zero_le_one.trans h') (le_trans (voyage_π ?_ p) M) e; intro i; obtain ⟨y,h,_⟩:= (r i).forms; exact h.price
end Drill
end YM.CF.Vow.TreasuryFog
