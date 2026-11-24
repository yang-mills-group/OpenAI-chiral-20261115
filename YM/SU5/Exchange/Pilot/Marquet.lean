import YM.CF.Sour.Seal
import YM.CF.Vow.Move
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

-- extra angular toll API for stencil kernels on P, retaining Crate.Beyond.H
variable {h a b:ℝ}
local notation "J"=>Finset (Dwell n)
namespace AuraOp
lemma multR (f:AuraOp P X D V h a) (p:AuraOp P X D W h b)(w:0≤a):AuraOp P X D (V*W) h (a*b):=by
 obtain ⟨L,hL,hB,hT⟩:= f.pay; obtain ⟨M,hM,hR,hS⟩:=p.pay
 refine ⟨⟨fun i j=> ∑ k:J,L i k*M k j,fun i j=>sum_nonneg fun _ _=>mul_nonneg (hL ..) (hM ..),?_,?_⟩⟩
 · intro i; dsimp only; simp_rw [mul_sum]; rw [sum_comm,mul_assoc]; apply le_trans _ (mul_le_mul_of_nonneg_left (hR i) w); rw [mul_sum]; apply sum_le_sum; intro j p; simp_rw [←mul_assoc,←sum_mul]; exact mul_le_mul_of_nonneg_right (hB j) (hM j i)
 intro v u S t i j
 dsimp only [Pi.mul_apply, Matrix.mul_apply]; apply Pence.germ (Pence.money (G:=fun k y=> (V (pressQ P S v.1 y,v.2) i k)*(W (pressQ P S v.1 y,v.2) k j)) (fun (k:J) (_:k∈univ)=> (hT _ u _ t _ k).twice (hS _ u _ t k j))); filter_upwards with a; rw [Finset.sum_apply]
lemma addR (f:AuraOp P X D V h a) (p:AuraOp P X D W h b): AuraOp P X D (V+W) h (a+b):=by
 obtain ⟨L,hL,hB,hT⟩:= f.pay; obtain ⟨M,hM,hR,hS⟩:=p.pay
 refine ⟨⟨L+M,fun i j=>add_nonneg (hL i j) (hM i j),fun j=>?_,fun v u _ t i j=> (hT _ u _ t i j).add (hS _ u _ t i j)⟩⟩ -- Agrees
 simp [mul_add,sum_add_distrib,add_mul]; exact add_le_add (hB j) (hR j) -- `simp` changes `_ ≤ _`
lemma scalarR (y:ℂ):AuraOp P X D (y • 1:Firing n) h ‖y‖:=by
 let H:= AuraOp.sat (n:=n) (P:=P) (D:=D) (X:=X) h (fun _=> y) (1:FC (Dwell n)) (Ark.one _) (norm_nonneg _) (fun _ _ _ _=> Pence.const ..)
 rw [mul_one] at H; exact H
lemma bigger (f:AuraOp P X D V h a)(w:0≤h)(g:a≤b):AuraOp P X D V h b:=by
 obtain ⟨L,hL,hB,hT⟩:= f.pay; exact ⟨L,hL,fun i=> (hB i).trans (mul_le_mul_of_nonneg_right g (pow_nonneg w _)),hT⟩
end AuraOp

namespace Marque
lemma multR (f:Marque P X Y D V h a) (p:Marque P X Y D W h b)(w:0≤a):Marque P X Y D (V*W) h (a*b):=by
 refine ⟨⟨f.cog.mul p.cog, fun i=> (f.body i).mul (p.body i), fun x y u v l n=> congrArg₂ (·*·) (f.same x y u v l n) (p.same x y u v l n),fun i t u=>?_⟩,(AuraOp.multR ⟨f.vet⟩ ⟨p.vet⟩ w).pay⟩
 simp only [Pi.mul_apply, singm]; rw [f.gauge i t u,p.gauge i t u]
lemma riseSup (f:Marque P X Y D V h a)(w:Y.val⊆ Z.val) : Marque P X Z D V h a :=⟨⟨f.cog,fun i=> lift_v (f.body i) fun j t=> mem_filter.mpr ⟨mem_univ _,w (mem_filter.mp t).2⟩,f.same,f.gauge⟩,f.vet⟩
lemma scalarR (y:ℂ):Marque P X Y D (y • 1:Firing n) h ‖y‖:=by
 refine ⟨⟨(show Measurable (fun _:Orbit n=> y • (1:FC (Dwell n))) from measurable_const), fun i=>Sector.one.scale y,fun _ _ _ _ _ _=>rfl,?_⟩,(AuraOp.scalarR y).pay⟩
 intro i t u; change y • 1= sauce false false (tradew n t) (y • (1:FC (Dwell n)))
 rw [sauce,singT,win_c,win_i,twist_scalar,map_one]; rfl
lemma noR : Marque P X Y D 0 h 0:=by simpa only [zero_smul,norm_zero] using (scalarR (h:=h) (X:=X) (P:=P) (Y:=Y) (D:=D) 0)
lemma scR (f:Marque P X Y D V h a)(y:ℂ):Marque P X Y D (y • V) h (‖y‖*a):=by
 let H:= (scalarR y).multR f (norm_nonneg y); rw [Algebra.smul_mul_assoc, one_mul] at H; exact H
lemma negR (f:Marque P X Y D V h a):Marque P X Y D (-V) h a:=by simpa only [neg_smul,one_smul,norm_neg,norm_one,one_mul] using f.scR (-1)
lemma addR (f: Marque P X Y D V h a)(p: Marque P X Y D W h b): Marque P X Y D (V+W) h (a+b):=by
 let F(i:Bool):= if i then V else W; let G(i:Bool):= if i then a else b
 have hv(i:Bool): Marque P X Y D (F i) h (G i):=by cases i; exact p; exact f
 have H:= tiltR h univ F G (fun i _=> hv i); simp only [F,G,Fintype.sum_bool,ite_true,Bool.false_eq_true,ite_false] at H; exact H
lemma bigger (f:Marque P X Y D V h a)(w:0≤h)(g:a≤b):Marque P X Y D V h b:=⟨f.toCrate,(AuraOp.bigger ⟨f.vet⟩ w g).pay⟩
end Marque

-- Mask needs no extra enlargement of support here:
-- inside lit visibility on footprint X all of its answer is determined by D.
lemma pingFix {S:Support (More n)} {i:Orbit n} (u:S⊆ X.val)(p:i.1∈ σX P X D) : pingS P.threshold S i.1 ↔ Disjoint S D:=by
 constructor
 · intro h; exact Disjoint.mono (le_refl _) (show D⊆_ from p.2) (ping_le h)
 intro t v w; apply p.1 v; contrapose! w; exact Disjoint.mono (show S⊆X.val\D from fun j q=>mem_sdiff.mpr ⟨u q,Finset.disjoint_left.mp t q⟩) (le_refl _) w
lemma whileLit {Z:Support (More n)}{i:Orbit n}(p:i.1∈σX P X D): ∀ᶠ a:tangD n in 𝓝 (0:tangD n), (pressQ P Z i.1 a)∈σX P X D:=by
 apply ContinuousAt.eventually_mem (f:=pressQ P Z i.1) ?c ((open_l ..).mem_nhds _); swap
 · rw [pressQ,smul_zero,YM.CF.Forge.born]; exact p
 let L:tangD n→L[ℝ] tangD n:=P.threshold • ContinuousLinearMap.id ℝ _
 exact ((Forge.stickU (Rill.unrest Z P.B) i.1).comp L.continuous).continuousAt
abbrev pingMask (P:BudgetPoint)(S:Support (More n)):= {i:Orbit n|pingS P.threshold S i.1}
def capR (P: BudgetPoint) (S:Support (More n)) (V:Firing n):Firing n:= (pingMask P S).indicator V
namespace AuraOp
lemma capMask (f:AuraOp P X D V h a)(S:Support (More n))(g:S⊆ X.val): AuraOp P X D (capR P S V) h a:=by
 obtain ⟨L,hL,hB,hT⟩:= f.pay; refine ⟨L,hL,hB,?_⟩; intro v u Z t i j; by_cases k:Disjoint S D
 · refine Pence.germ (hT _ u _ t i j) ?_; filter_upwards [whileLit (Z:=Z) u] with a hp; let w:Orbit n:=(pressQ P Z v.1 a,v.2); rw [capR,Set.indicator_of_mem (show w∈ pingMask P S from (pingFix (i:=w) g hp).mpr k)] -- tune
 refine Pence.germ (show Pence P.order (fun _:tangD n=> (0:ℂ)) 0 (L i j) from ⟨(Pence.const _ _).smooth,(Pence.const (k:=P.order) (0:tangD n) (0:ℂ)).earned.trans ((norm_zero.le).trans (hL i j))⟩) ?_
 filter_upwards [whileLit (Z:=Z) u] with a hp; let w:Orbit n:=(pressQ P Z v.1 a,v.2); rw [capR,Set.indicator_of_notMem (show w∉ pingMask P S from mt (pingFix (i:=w) g hp).mp k)]; rfl
end AuraOp
lemma Marque.capMask (f:Marque P X Y D V h a)(S:Support (More n))(g:S⊆ X.val):Marque P X Y D (capR P S V) h a:=by
 refine ⟨⟨f.cog.indicator (measurable_fst ping_o.measurableSet),fun i=>?_,fun i j p q u v=>?_,fun i t u=>?_⟩,(AuraOp.capMask ⟨f.vet⟩ S g).pay⟩
 · by_cases u:i∈ pingMask P S; · rw [capR,Set.indicator_of_mem u]; exact f.body i
   rw [capR,Set.indicator_of_notMem u]; exact Sector.zero _
 · by_cases k:Disjoint S D
   · rw [capR,Set.indicator_of_mem (show i∈_ from (pingFix g p).mpr k),Set.indicator_of_mem (show j∈ _ from (pingFix g q).mpr k)]; exact f.same i j p q u v
   rw [capR,Set.indicator_of_notMem (show i∉ _ from mt (pingFix g p).mp k),Set.indicator_of_notMem (show j∉ _ from mt (pingFix g q).mp k)]
 let U:Orbit n:=(Lattice.gauge t i.1, threadG t i.2); by_cases p:i∈ pingMask P S; · rw [capR,Set.indicator_of_mem (show U∈_ from (pingB i.1 t).mpr p),Set.indicator_of_mem p]; exact f.gauge i t u
 rw [capR,Set.indicator_of_notMem (show U∉_ from mt (pingB i.1 t).mp p),Set.indicator_of_notMem p]; rw [sauce,singT,win_z,map_zero]
end YM.CF.Sour
