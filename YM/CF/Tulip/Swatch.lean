import YM.CF.Tulip.Stem
set_option autoImplicit false
noncomputable section
namespace YM.CF.Tulip
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I G Y D : Type*}[Fintype Y][DecidableEq Y][TopologicalSpace D][Fintype I][DecidableEq I]
def panel (i j:I)(A:Op Slot): Op (I×Slot):= Matrix.of fun x y=> if x.1=i ∧ y.1=j then A x.2 y.2 else 0
def reed (i j:I)(r:ℝ): Toll (I×Slot):= fun x y=> if x.1=i ∧ y.1=j then r else 0
variable {b:Stage Y (I×Slot) D G}{s t:Branch.Tag b}{p q:G→ I →UNI Slot}
lemma panel_ticket {L: License D}{p q:G→ I →UNI Slot}(hp:∀ g,(s.run g).val=jump (Equiv.refl _) fun i=>(p g i).val)(hq:∀ g,(t.run g).val=jump (Equiv.refl _) fun i=>(q g i).val)(i j:I) (S:Seal Y)(w:ℝ)(K:D→Op Slot)(hx:Grove b.F S)
    (h1:∀ k,b.home (i,k)∈S)(h2:∀ k,b.home (j,k) ∈ S)(h3:∀ g x,K (b.drive g x)*(q g j).val=(p g i).val*K x)
    (hc:0≤w)(hm: L.all K)(hd:Continuous K)(hv:∀ x, ‖K x‖≤w)(he:∀ x y, ‖K x - K y‖≤w*b.eval S x y):
    Suite L s t S (reed i j w) (fun x=> panel i j (K x)):=by
  refine ⟨⟨fun g x=>?_,fun ⟨a,k⟩ ⟨c,l⟩=>?_⟩,fun ⟨a,k⟩ ⟨c,l⟩=>?_⟩
  · rw [hp,hq]; ext ⟨a,k⟩ ⟨c,l⟩
    simp only [Matrix.mul_apply,Fintype.sum_prod_type,jump_apply,Equiv.refl_apply, panel,Matrix.of_apply]; by_cases h:a=i <;> by_cases hh:c=j
    · subst a c; simp only [true_and,and_true,and_self,mul_ite,ite_mul]; simp; have hk:= Matrix.ext_iff.mpr (h3 g x) k l; simpa [Matrix.mul_apply,Slot,Fintype.sum_prod_type] using hk -- tune
    all_goals simp [h,hh,ite_mul,mul_ite]
  · by_cases h:a=i∧c=j; swap
    · simp only [panel,reed,h,Matrix.of_apply,if_false]; exact nothing ..
    obtain ⟨rfl,rfl⟩:=h; simp only [panel,reed,and_self,Matrix.of_apply,ite_true]; refine ⟨hc,fun _=> ⟨hx,h1 _,h2 _⟩,fun d=>(norm_entry ..).trans (hv d),fun d x=>(norm_entry (K d-K x) _ _).trans (he d x),hd.matrix_elem _ _⟩
  by_cases h:a=i∧c=j
  · simpa only [panel,h,and_self,Matrix.of_apply,ite_true] using hm k l
  simp only [panel,h, Matrix.of_apply,if_false]; exact L.con _

variable {N:Side}(e:ℝ)(he:0<e)
-- field track endpoint twig, including analytic estimate
include he in
lemma gage (x y:Site N×SpinIdx)(p:Walk)(h:stop (node x.1) p=node y.1)(c:ℂ)(hh:e≤1):
 let V:=(p.length+1:ℝ)*((1+e)^p.length)
 let S:=traceP (node x.1) p
 Suite (badge _) (bail N e) (bail N e) S (reed x y (V*‖c‖)) (fun z=> panel x y (c • (track z.val (node x.1) p).1)) :=by
  intro V S
  let o:=node x.1; let f(z:Openc (More N) e):Op Slot:=c • (track z.val o p).1
  have ht: Differentiable ℂ (fun z=> c • (track z o p).1):=(track_d o p).fst.const_smul c
  have hg:= he.le
  refine panel_ticket (p:=fun g i=>matter (g (node i.1))) (q:=fun g i=>matter (g (node i.1))) (fun _=>rfl) (fun _=> rfl) x y S _ f (trace_g ..) (fun _=>trace_source ..) (fun _=>show node y.1∈ S from h ▸ trace_last ..) ?_ (by unfold V; positivity) ?_ ?_ ?_ ?_
  · intro g z
    let J:= (matter (g (node y.1))).val
    change c • (track (relayg g z.val) o p).fst * J=(matter (g o)).val*f z
    rw [track_g,h]
    change (c • ((matter (g o)).val* _ * star J))*J=_
    unfold f; rw [Matrix.smul_mul,mul_assoc _ (star J), show star J*J=1 from (matter _).property.1,mul_one, Matrix.mul_smul]
  · intro k l; apply honors (f:=fun z=> (c • (track z o p).1) k l); exact (differentiable_pi.mp (differentiable_pi.mp (by exact ht) _) _).differentiableOn -- probably transport topology
  · exact ht.continuous.comp continuous_subtype_val
  · intro d
    unfold f; rw [norm_smul,mul_comm V]; refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _); apply le_trans (norm_fst_le ..); apply le_trans (track_size e he.le o p d.val d.property); unfold V; exact le_mul_of_one_le_left (by positivity) (by simp)
  intro d d'
  unfold f; rw [← smul_sub,norm_smul]; change _≤_* (fare S d.val d'.val /|e|)
  rw [mul_comm V,mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine le_trans (norm_fst_le (track d.val o p-track d'.val o p)) ?_
  apply le_trans (track_vol _ he.le o p d.val d'.val d.property d'.property);
  rw [abs_of_pos he,←mul_assoc]; unfold V; gcongr; exact fare_t ..;  · simp
  exact le_div_self (fare_t ..) he hh
end YM.CF.Tulip
