import YM.CF.Spark.Atone
set_option autoImplicit false
noncomputable section
namespace YM.CF.Spark
open Function Filter Metric Finset NormedSpace Lattice Laurent Lat Tulip Rush Cube Tenant Mir Mir.Trip Phase Phase.Sample Branch Vale MeasureTheory RG Wilson WilsonStartup RP Nova Kea Ave Fock SU CF.Jet Broc Petal Spire
open scoped Topology BigOperators Matrix MatrixOrder ContDiff InnerProductSpace Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n m B: Side}{e a C:ℝ}
local notation "n'"=> Domain m B
-- unwind on every small Grove, CPF uses all anchors.
variable (z: Candle)
def hovel(z:Candle)(x:Cover):TF:=⟨fun f=>∑ i:Axis,(x i:ℝ)*(z i).val f,(by
 rw [sum_comm]; apply sum_eq_zero; intro i _; rw [←mul_sum,(z i).property,mul_zero])⟩
def axisL(z:Candle)(x:Cover):= waveG (hovel z x)
lemma axis_q(x:Cover)(j:Axis) : axisL z (x+Lattice.step j)=axisL z x*waveG (z j):=by
 unfold axisL; rw [tax_mul]; congr 1; apply Subtype.ext; funext f; unfold hovel; dsimp only [Pi.add_apply]; simp_rw [step_apply,Int.cast_add,apply_ite (fun j:ℤ=>(j:ℝ)),add_mul, sum_add_distrib]; simp
lemma warm(S:Support n)(x:Site n)(l:ℕ)(p:2*(l+1)< n.val)(q:∀ y∈S,separation y x ≤ l): ∃ t:Site n→ group.El, Agrees S (Lattice.gauge t (Kea.tax z)) (1:Config group n) :=by
 let t(y):= axisL z (Lattice.lift (y-x)); refine ⟨t,?_⟩; intro i h w; let v:=Lattice.lift (i.1-x); have he:Lattice.lift (i.1+Lattice.step i.2-x)=v+Lattice.step i.2:=by
    apply lift_eq_iff.mpr; refine ⟨(by unfold v; rw [map_add,wrap_step,wrap_lift]; abel),fun j=>?_⟩; have hp:(v j).natAbs ≤ l:= le_trans (component_le ..) (q _ h); simp only [Pi.add_apply,Lattice.step_apply]; split_ifs <;> omega
 change axisL z v * waveG (z i.2)* (axisL z (Lattice.lift _))⁻¹=1; rw [he,axis_q,mul_inv_cancel]
lemma gspan{Y:Type}[DecidableEq Y]{b:Branch.Field Y}{S:Finset Y}(h:Grove b S):S.Nonempty:=by cases h<;>simp
-- zero chosen via TF. avoid typography
abbrev pole(m B:Side)(p:0≤e) (z:Candle) : Briar m B e:=⟨Kea.tax z,tax_guard z (Domain m B) _ p⟩ -- tune
abbrev slate:Candle:= fun _=>⟨0,(by simp)⟩
lemma plank (m B:Side)(p:0≤e): (pole m B p slate).val= (1: Config group (Domain m B)):=by
 funext i; change waveG ⟨(0:F→ℝ),_⟩=1; apply Subtype.ext; apply Subtype.ext; change Matrix.diagonal (fun _:F=>pw 0)= (1: Matrix F F ℂ); simp_rw [phase_z]; rfl
lemma eC(m B:Side):(Domain m B).val=4*m.val*B.val:=by change m.val*2*B.val*2= _; ring
lemma lull(m B:Side)(i j:ℕ)(g:i≤ m.val)(p:4≤ m.val)(l:j≤B.val*(i+1)):2*(j+1)< (Domain m B).val:=by rw [eC m B]; have hp: 1≤ B.val:= B.property; have ht:= Nat.mul_le_mul_left B.val g; have he:= Nat.mul_le_mul_left B.val p; rw [Nat.mul_comm B.val m.val] at ht he; simp only [Nat.mul_assoc] at *; rw [Nat.mul_comm B.val i] at ht; rw [Nat.mul_add,Nat.mul_one,Nat.mul_comm B.val i] at l; omega
-- stamp orientation
lemma pupil (S:Acres m)(f:Briar m B e→ℂ)(w:ℝ)(p:0≤e)(q:Petal.Token (moneyW m B e) S f w (Grove (terr _)))(g:w≠0)(l:S.card≤ m.val)(u:4≤ m.val): f (pole m B p z)= f (pole m B p slate):=by
 have hz:=q.shape g; obtain ⟨x,h⟩:=gspan hz; obtain ⟨t,T⟩:= warm z (mount m B S) (Cube.address m B x) (B.val*(S.card+1)) (lull m B S.card _ l u le_rfl) (by intro y hy; obtain ⟨i,v,hA⟩:=mem_biUnion.mp hy; have ht:=room_span hA; have he:= hz.lim i v x ‹_›; have hp:= (distance_addr_iff (B:=B) i x S.card).mp he.le; exact (separation_triangle y (Cube.address m B i) _).trans ((add_le_add ht hp).trans_eq (by ring)))
 change (moneyW m B e).rule t (f (pole m B p z))=_; rw [q.dress]; refine q.locality ?_; change Agrees (mount m B S) _ (pole m B p slate).val; rw [plank]; exact T
lemma tune_f(S:Seal (Site (Domain m B)))(f:Briar m B e→ℂ)(w:ℝ)(p:0≤e)(q:Peak (soar m B e) S f w)(g:w≠0)(l:S.card≤ m.val)(u:4≤ m.val): f (pole m B p z)= f (pole m B p slate):=by
 have hz:=q.travel g; obtain ⟨x,h⟩:=gspan hz; obtain ⟨t,T⟩:= warm z S x S.card (lull m B S.card S.card l u (by have he:=B.property; nlinarith only [Nat.mul_le_mul_right S.card (show 1≤B.val from B.property),he])) fun y v=> le_of_lt (show separation y x<S.card from hz.lim y v x h)
 rw [← q.gauge (pole m B p z) t]; refine q.reads _ _ ?_; change Agrees S _ (pole m B p slate).val; rw [plank]; exact T
-- Payer from aggregate
variable {Y:Type*}[DecidableEq Y][Fintype Y]
lemma cum(K:Seal Y→ℝ)(h:∀ i,hitE a K i≤C)(hp:∀ i,0≤K i)(q:∀ i,K i≠0→i.Nonempty) : ∑ i:Seal Y,Branch.rent a i*K i≤Fintype.card Y*C:=by
 refine le_trans ?_ ((sum_le_sum (s:=univ) (fun i _=> h i)).trans_eq (by rw [sum_const,card_univ,nsmul_eq_mul])); unfold hitE hit0; simp_rw [sum_filter]; rw [sum_comm]; apply sum_le_sum; intro i hi; by_cases v:K i=0; · simp [v]
 obtain ⟨x,hx⟩:= q _ v; calc
   _=(if x∈i then Branch.rent a i*K i else 0):=(if_pos hx).symm
   _ ≤ _:=single_le_sum (f:=fun x=> if x∈i then Branch.rent a i*K i else 0) (fun j _=> by split; exact mul_nonneg (rent_pos ..).le (hp i); rfl) (mem_univ _)
lemma faultX(m: ℕ)(U V:Seal Y→ℂ)(K:Seal Y→ℝ)(h:∀ i,hitE a K i≤C)(hp:∀ i,0≤K i)(q:∀ i,K i≠0→i.Nonempty)(he:0<a)(P:∀ i,‖U i‖ ≤ K i)(W:∀ i,‖V i‖≤ K i)(L:∀ i,K i≠0→i.card≤ m→U i=V i): ‖(∑ i,U i)-(∑ i,V i)‖ ≤ Real.exp (-a*m)* (2*(Fintype.card Y*C)):=by
 rw [←sum_sub_distrib]; refine le_trans (norm_sum_le ..) ?_; let x:=Real.exp (-a*m); have hx:0≤x:=(Real.exp_pos _).le
 apply le_trans _ (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (cum _ h hp q) (by norm_num)) hx); rw [Finset.mul_sum,Finset.mul_sum]; apply sum_le_sum; intro i _; by_cases g:K i=0
 · exact (norm_sub_le ..).trans (by simpa only [g,mul_zero,add_zero] using (show ‖U i‖+‖V i‖ ≤ 0+K i from add_le_add ((P i).trans_eq g) (W i))) -- syntactic rhs
 have hv:0<K i:= lt_of_le_of_ne (hp _) (Ne.symm g); have hK:0<Branch.rent a i:= rent_pos ..
 by_cases u:i.card ≤ m
 · rw [L i g u,sub_self,norm_zero]; positivity
 have hy:1≤x*Branch.rent a i:=by unfold x Branch.rent; rw [← Real.exp_add]; apply Real.one_le_exp; have t: (m:ℝ) ≤ i.card:=(by exact_mod_cast Nat.le_of_not_ge u); nlinarith
 change _ ≤ x*_
 calc
   _ ≤ K i + K i:= (norm_sub_le ..).trans (add_le_add (P i) (W i))
   _ ≤ x * Branch.rent a i * (K i+K i):=le_mul_of_one_le_left (by positivity) hy
   _ = _:=by ring
end YM.CF.Spark
