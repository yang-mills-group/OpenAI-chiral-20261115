import YM.SU5.Exchange.Pilot.Herb
import YM.CF.Leaf.Milt
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

open Rill Branch Tenant Drapes Leaf
-- gathering Aura. budgets for SINGLE source, then later plume at arbitrary count. Trace weighted
variable {q k:ℕ}{h a b d e s:ℝ}
abbrev voyageB (V:Aura n→ℝ)(k:ℕ)(s:ℝ):ℝ:=∑ i:Aura n,V i*tact s k i
lemma tact_para (t:a≤b)(i:Aura n): tact a k i≤ tact b k i:= Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right t (show 0 ≤ widthK _ k _ from Nat.cast_nonneg _))
lemma tact_αK (h:0 ≤ s){I J:Aura n}(t:J ∈ Cadre.blaze I) : tact s k (αK I J) ≤ tact s k I * tact s k J:=by
 simpa only [loom_v,zero_mul,sub_zero] using Tax_R.meet_K _ (vigor n k) s 0 0 (by rw [zero_mul,sub_zero]; exact h) I J t
lemma voyage_π {V:Aura n→ℝ}(g:0 ≤ V)(h:a ≤ b):voyageB V k a ≤ voyageB V k b:=sum_le_sum fun i _=>mul_le_mul_of_nonneg_left (tact_para h i) (g _)
lemma voyage_sum{ι:Type*}(U:ι→Aura n→ℝ)(S:Finset ι)(k:ℕ)(s:ℝ): voyageB (∑ i∈S,U i) k s=∑ i∈S,voyageB (U i) k s:=by simp_rw [voyageB,Finset.sum_apply,sum_mul]; rw [sum_comm]
lemma voyage_plus(U V:Aura n→ℝ): voyageB (U+V) k s=voyageB U k s+voyageB V k s:=by simp_rw [voyageB, Pi.add_apply,add_mul,sum_add_distrib]
lemma voyage_scale(U:Aura n→ℝ)(a:ℝ):voyageB (fun j=>a*U j) k s=a*voyageB U k s:=by simp only [voyageB,mul_sum,mul_assoc]
variable {U J:Aura n→ℝ}
lemma voyage_le (p:U≤J): voyageB U k s ≤ voyageB J k s:=sum_le_sum fun i _=> mul_le_mul_of_nonneg_right (p _) (Real.exp_pos _).le
-- cost of one convolution with an incidence partner. pay card through B-order Slack.
lemma shelf_pay (p:0 < e)(X:Aura n): (X.val.card:ℝ)*tact s k X ≤ (spanV k *e⁻¹)*tact (s+e) k X:=by
 let W:=widthK n k X; have h':0 ≤ spanV k:=Nat.cast_nonneg _
 have hv:= show e*W ≤ Real.exp (e*W) from le_trans (le_add_of_nonneg_right zero_le_one) (Real.add_one_le_exp _)
 have hu: W ≤ e⁻¹*Real.exp (e*W):=(le_inv_mul_iff₀ p).mpr hv
 refine (mul_le_mul_of_nonneg_right ((vigor n k).rate X|>.trans (mul_le_mul_of_nonneg_left hu h')) (Real.exp_pos _).le).trans_eq ?_
 unfold tact; rw [add_mul,Real.exp_add]; unfold W; ring
lemma voyage_tw (p:0 ≤ s)(v:0 < e)(u:0 ≤ U)(j:0 ≤ J)(x:∀ i:Seat n,nook (J*tact s k) i ≤ b)(w:0 ≤ b): voyageB (Ktw (fun X Y=>U X* J Y)) k s ≤ spanV k* e⁻¹ *voyageB U k (s+e) * b:=by
 unfold voyageB Ktw; simp_rw [sum_mul]; rw [sum_comm, mul_sum, sum_mul]; apply sum_le_sum; intro X hg
 let I:= Cadre.blaze X; rw [sum_comm]; simp_rw [ite_mul,zero_mul]
 have hp(Y:Aura n)(l:Y∈I) : (∑ Z:Aura n,if Z=αK X Y then U X*J Y * tact s k Z else 0) ≤ U X*tact s k X*(J Y*tact s k Y) :=by
    simp only [sum_ite_eq',sum_ite_eq,mem_univ,ite_true]; exact (mul_le_mul_of_nonneg_left (tact_αK p l) (mul_nonneg (u _) (j _))).trans_eq (by ring)
 apply (sum_le_sum hp).trans; rw [←mul_sum]; let H:=tact s k X; have hm:= Cadre.beam X (J*tact s k) (fun i=> mul_nonneg (j i) (Real.exp_pos _).le) b (fun i _=>x i); refine (mul_le_mul_of_nonneg_left hm (mul_nonneg (u X) (Real.exp_pos _).le)).trans ?_
 rw [←mul_assoc]; apply mul_le_mul_of_nonneg_right _ w; have he:=(shelf_pay (k:=k) (s:=s) v X); linarith only [mul_le_mul_of_nonneg_left he (u X)] -- tune

-- composable ticket: dictionary already anchored at requested core A; erase empty letters in u cost as needed.
structure Barrage (P:BudgetPoint)(q:ℕ)(A:Support (More n))(h:ℝ)(V:Bag n)(s a b:ℝ):Prop where
 price : ∃ Q J:Aura n→ℝ,(∀ X:Aura n,Flight P q X h (V X) (Q X) (J X)) ∧
    (∀ X:Aura n, ¬A⊆ X.val → V X=0 ∧ Q X=0∧ J X=0) ∧ voyageB Q P.B s≤a ∧ voyageB J P.B s≤b
namespace Barrage
variable {A:Support (More n)}{V W:Bag n}(p:Barrage P q A h V s a b)(r:Barrage P q A h W s d e)
lemma zeroR: Barrage P q A h 0 s 0 0:=⟨0,0,fun _=>Flight.zeroR,fun _ _=>⟨rfl,rfl,rfl⟩,by simp [voyageB]⟩
lemma single (X:Aura n)(F:Firing n)(t:Flight P q X h F a b)(x:A⊆ X.val):Barrage P q A h (fun i:Aura n=> if i=X then F else 0) s (a*tact s P.B X) (b*tact s P.B X):=by
 refine ⟨fun i=> if i=X then a else 0,fun i=> if i=X then b else 0,fun Y=>?_ ,fun i v=>by dsimp only; rw [if_neg (fun hx:i=X=> v (hx.symm ▸ x)),if_neg (fun hx:i=X=>v (hx.symm ▸ x)),if_neg (fun hx:i=X=>v (hx.symm ▸ x))]; exact ⟨rfl,rfl,rfl⟩,by simp [voyageB,ite_mul]⟩
 dsimp only; split_ifs with p; exact p.symm ▸ t; exact Flight.zeroR
include p r
lemma plusR: Barrage P q A h (V+W) s (a+d) (b+e):=by
 obtain ⟨Q,J,z,t,u,v⟩:= p.price; obtain ⟨L,N,H,T,hs,hc⟩:=r.price; refine ⟨Q+L,J+N,fun X=> (z X).addR (H X),?_,?_⟩
 · intro X p; simp only [Pi.add_apply,(t X p).1,(T X p).1, (t X p).2.1,(T X p).2.1,(t X p).2.2,(T X p).2.2,zero_add,and_self]
 rw [voyage_plus,voyage_plus]; exact ⟨add_le_add u hs,add_le_add v hc⟩
omit r
lemma lessR(k:d ≤ s): Barrage P q A h V d a b:=by
 obtain ⟨Q,J,z,t,u,v⟩:= p.price; refine ⟨Q,J,z,t,(voyage_π (fun i=>(z i).tube.price) k).trans u,(voyage_π ?_ k).trans v⟩
 intro i; obtain ⟨w,g,_⟩:=(z i).forms; exact g.price
lemma bigR (hh:d≥a)(w:e≥b): Barrage P q A h V s d e:=by obtain ⟨Q,J,z,t,u,v⟩:=p.price; exact ⟨Q,J,z,t,u.trans hh,v.trans w⟩ -- '_' tune
lemma swell (y:ℂ): Barrage P q A h (y • V) s (‖y‖*a) (‖y‖*b):=by
 obtain ⟨Q,J,z,t,u,v⟩:=p.price
 refine ⟨fun X=> ‖y‖* Q X,fun X=>‖y‖*J X,fun X=> (z X).scR y,?_,?_⟩
 · intro X p; simp only [Pi.smul_apply,(t X p).1,(t X p).2.1,(t X p).2.2,mul_zero,smul_zero,and_self]
 rw [voyage_scale,voyage_scale]; exact ⟨mul_le_mul_of_nonneg_left u (norm_nonneg _),mul_le_mul_of_nonneg_left v (norm_nonneg _)⟩
lemma negR :Barrage P q A h (-V) s a b:=by simpa only [neg_one_smul,norm_neg,norm_one,one_mul] using p.swell (-1)
lemma fresh (Z:Support (More n))(u:Z⊆A):Barrage P q A h (fun i=> capR P Z (V i)) s a b:=by
 obtain ⟨Q,J,z,t,hu,v⟩:=p.price; have hw(X:Aura n)(k:¬A⊆ X.val): capR P Z (V X)=0:=by rw [(t X k).1,capR]; exact Set.indicator_zero ..  -- tune
 refine ⟨Q,J,fun i=>?_,fun i p=> ⟨hw i p,(t i p).2⟩,hu,v⟩
 by_cases p:A⊆ i.val; exact (z i).mask _ (u.trans p); rw [hw i p,(t i p).2.1,(t i p).2.2]; exact Flight.zeroR
omit p
lemma whole{ι: Type*}(S:Finset ι)(V:ι→ Bag n)(a b:ι→ℝ)(u:∀ i∈S,Barrage P q A h (V i) s (a i) (b i)):Barrage P q A h (∑ i∈ S,V i) s (∑ i∈ S,a i) (∑ i∈ S,b i):=by
 induction S using Finset.induction_on with
 |empty=> rw [sum_empty,sum_empty,sum_empty]; exact zeroR
 |insert i S v ih=> rw [sum_insert v,sum_insert v,sum_insert v]; exact (u i (mem_insert_self ..)).plusR (ih fun x h=>u x (mem_insert_of_mem h))
end Barrage

end YM.CF.Sour
