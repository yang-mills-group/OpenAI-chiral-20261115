import YM.CF.Stax.Horizon
import YM.SU5.Interaction.Kerosene.Embering
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
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
lemma AuraOp.addP (p:AuraOp P X D F h v)(q:AuraOp P X D G h w):AuraOp P X D (F+G) h (v+w):=by
 have ht(b:Bool): AuraOp P X D (if b then F else G) h (if b then v else w):= by cases b; exact q; exact p
 simpa [Fintype.sum_bool] using (AuraOp.sumR h (univ:Finset Bool) (fun b=> if b then F else G) (fun b=>if b then v else w) (fun i _=> ht i))
lemma AuraOp.realCross (p:AuraOp P X D F h v)(q:AuraOp P X D G h w)(hv:0 ≤ v):AuraOp P X D (F*G) h (v*w):=by
 obtain ⟨A,e,a,c⟩:= p; obtain ⟨B,f,b,d⟩:= q
 let C (i j:Finset (Dwell n)):= ∑ r: Finset (Dwell n),A i r*B r j
 refine ⟨⟨C,fun i j=>sum_nonneg fun _ _=> mul_nonneg (e ..) (f ..),fun i=>?_, fun U p Z q i j=>?_⟩⟩
 · unfold C; rw [mul_assoc]; refine le_trans ?_ (mul_le_mul_of_nonneg_left (b i) hv); simp_rw [mul_sum]; rw [sum_comm]; apply sum_le_sum; intro j _; simp_rw [←mul_assoc, ←sum_mul]; exact mul_le_mul_of_nonneg_right (a j) (f j i)
 let V(y:tangD n):=((pressQ P Z U.1 y,U.2):Orbit n); refine Pence.germ (Pence.money (G:=fun r=>fun y=>F (V y) i r* G (V y) r j) (fun r (_:r∈Finset.univ)=> (c U p Z q i r).twice (d U p Z q r j))) (Eventually.of_forall fun y=>?_); rw [Finset.sum_apply]; exact (Matrix.mul_apply ..).symm
lemma Crate.sumF (p: Crate P X D Y F)(q:Crate P X D Y G):Crate P X D Y (F+G):=by
 refine ⟨p.cog.add q.cog, fun i=>(p.body i).add (q.body i), fun i j e f g t=> congrArg₂ (·+·) (p.same _ _ e f g t) (q.same _ _ e f g t),fun i t h=>?_⟩
 exact (congrArg₂ (·+·) (p.gauge _ _ h) (q.gauge _ _ h)).trans (Sault.flare ..).symm
lemma Crate.crossF (p: Crate P X D Y F)(q:Crate P X D Y G):Crate P X D Y (F*G):=by
 refine ⟨p.cog.mul q.cog, fun i=>(p.body i).mul (q.body i), fun i j e f g t=> congrArg₂ (·*·) (p.same _ _ e f g t) (q.same _ _ e f g t),fun i t h=>?_⟩
 exact (congrArg₂ (·*·) (p.gauge _ _ h) (q.gauge _ _ h)).trans (@singm _ _ _ _ _ _ _).symm
lemma Crate.weig (p: Crate P X D Y F)(t:ℂ):Crate P X D Y (t • F):=by
 refine ⟨p.cog.const_smul _,fun i=> (p.body i).scale _,fun i j a b c d=>congrArg (t • ·) (p.same _ _ a b c d),fun i s h=>?_⟩
 rw [Pi.smul_apply,p.gauge i s h]; rw [Pi.smul_apply,sauce]; change t • twist _ _ = twist _ (t • _); exact (twist_scalar ..).symm
lemma AuraOp.scalar (p:AuraOp P X D F h v)(t:ℂ):AuraOp P X D (t • F) h (‖t‖*v):=by
 obtain ⟨A,h,a,p⟩:=p
 refine ⟨⟨fun i j=> ‖t‖* A i j, fun i j=>mul_nonneg (norm_nonneg _) (h i j),fun i=>?_,fun i v Z q x y=> (p i v _ q x y).σ t⟩⟩
 simp_rw [mul_left_comm (_ ^ _) ‖t‖, ←mul_sum, mul_assoc]; exact mul_le_mul_of_nonneg_left (a i) (norm_nonneg _)
-- require Turf.X only on D=∅ when σX. Lease.N.suite
structure Title (P:BudgetPoint)(h:ℝ)(δ:ℕ)(F:Firing n)(X:Aura n)(c:ℝ):Prop where
 valid: ∀ i:Orbit n, Fock.Sector (camp X.val) false (F i)
 scope: ∀ Y:Aura n,X.val ⊆ Y.val→∀ D⊆ Y.val, halo δ D ⊆ Y.val→ Marque P Y X D F h c
 clean: ∀ (Y:Aura n)(p:X.val ⊆ Y.val)(i:Orbit n), i.1∈σX P Y ∅→∀ j:Ids n,F i=F (i.1,j)
 pay: 0≤ c
lemma Title.republish (p:Title P h δ F X c)(t:c ≤ s)(hv:0≤ h): Title P h δ F X s:=by
 refine {p with pay:=p.pay.trans t,scope:=fun Y k D q l=>?_}; let v:=p.scope _ k _ q l; obtain ⟨A,a,b,d⟩:=v.vet; exact {v with vet:=⟨A,a,fun i=> (b i).trans (mul_le_mul_of_nonneg_right t (by unfold Rail; positivity)),d⟩}
lemma Title.broaden (p:Title P h δ F X c)(t:X.val⊆ Y.val): Title P h δ F Y c:=by
 have ht:camp X.val⊆ camp (n:=n) Y.val:=fun i k=> mem_filter.mpr ⟨mem_univ _,t (mem_filter.mp k).2⟩
 exact ⟨fun i=>lift_v (p.valid i) ht, fun Z u D w q=> {(p.scope Z (t.trans u) D w q) with body:=fun i=>lift_v (p.valid i) ht},fun U h=>p.clean U (t.trans h),p.pay⟩
lemma Title.piggyback (p:Title P h δ F X c)(q:Title P h δ G X s):Title P h δ (F*G) X (c*s):= by
 refine ⟨fun i=> (p.valid i).mul (q.valid i),fun T' u D r v=>?_ ,fun U x i e j=> congrArg₂ (·*·) (p.clean U x i e j) (q.clean U x i e j),mul_nonneg p.pay q.pay⟩
 let v1:=p.scope _ u _ r v; let v2:=q.scope _ u _ r v; exact ⟨v1.toCrate.crossF v2.toCrate,(show AuraOp P T' D (F*G) h (c*s) from AuraOp.realCross ⟨v1.vet⟩ ⟨v2.vet⟩ p.pay).pay⟩
lemma Title.sumP {ι:Type*}(s:Finset ι)(F:ι→Firing n)(v:ι→ℝ)(hX:∀ i∈s,Title P h δ (F i) X (v i)): Title P h δ (∑ i∈s,F i) X (∑ i∈s,v i):= by
 refine ⟨fun i=>by rw [Finset.sum_apply]; exact Sector.sumS _ _ fun k v=> (hX _ v).valid i,fun Y a D b c=> Marque.tiltR h s F v fun i p=> (hX i p).scope _ a _ b c,fun U t i f H=> by simp_rw [Finset.sum_apply]; exact sum_congr rfl fun j v=>(hX _ v).clean _ t i f H, sum_nonneg fun i p=> (hX _ p).pay⟩
lemma Title.coinF (p:Title P h δ F X c)(t:ℂ): Title P h δ (t • F) X (‖t‖ * c):= by
 refine ⟨fun i=> (p.valid i).scale t,fun Y v D u g=>?_ ,fun U x i e j=> congrArg (t • ·) (p.clean U x i e j),mul_nonneg (norm_nonneg _) p.pay⟩
 let H:=p.scope _ v _ u g; exact ⟨H.toCrate.weig t,(show AuraOp P Y D (t • F) h (‖t‖*c) from (AuraOp.scalar ⟨H.vet⟩ t)).pay⟩
lemma Title.free : Title P h δ (fun _:Orbit n=>0) X 0:=by
 let s:Finset (Orbit n) := ∅; let p:= Title.sumP (P:=P) (X:=X) (δ:=δ) (h:=h) s (fun _ _: Orbit n=> (0: FC (Dwell n))) (fun _=>0) (by simp [s]); rw [show s=∅ from rfl,sum_empty,sum_empty] at p; exact p
lemma Title.parallel (p:Title P h δ F X c)(q:Title P h δ G X s): Title P h δ (F+G) X (c+s):=⟨fun i=>(p.valid i).add (q.valid i), fun Y v D r h'=>by let v1:=p.scope _ v _ r h'; let v2:=q.scope _ v _ r h'; exact ⟨v1.toCrate.sumF v2.toCrate,(show AuraOp P Y D (F+G) h (c+s) from AuraOp.addP ⟨v1.vet⟩ ⟨v2.vet⟩).pay⟩,fun U t i v j=> congrArg₂ (·+·) (p.clean U t i v j) (q.clean U t i v j), add_nonneg p.pay q.pay⟩
lemma Title.dither (p:Title P h δ F X c)(q:Title P h δ G X s): Title P h δ (F-G) X (c+s):= by simpa [sub_eq_add_neg] using p.parallel (q.coinF (-1))
end YM.CF.Sour
#print axioms YM.CF.Sour.Title.parallel
