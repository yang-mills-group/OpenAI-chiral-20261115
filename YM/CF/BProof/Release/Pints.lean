import YM.CF.BProof.Release.Small

/- Apt slots for a column. One Euclidean plan. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Release.Pub
open Function MeasureTheory Filter RG Wilson Lattice Precision Law Set Metric Finset
open scoped BigOperators Topology Classical ENNReal Matrix.Norms.Frobenius
variable {G:Gauge}{I: Type} [Fintype I]
variable (T:Pub G)(R g:ℝ)(A:I→ G.El)
abbrev Stamp (G:Gauge)(I:Type):= I× G.ColorIndex → ℝ
abbrev Hall (G:Gauge)(I:Type):= I→ G.El
def den := Set.univ.pi (fun i=> near R (A i))
lemma den_m : MeasurableSet (den R A):=MeasurableSet.univ_pi fun i=> near_m ..
abbrev key (a:Stamp G I)(i:I) := curry a i
def vault (a:Stamp G I):= ∀ i,key a i∈ T.soft R g (A i)
abbrev ticket (a : Stamp G I):= ∏ i,T.fee R g (A i) (key a i)
def stamp (a : Stamp G I) := fun i=> unlock g (A i) (key a i)
def law := volume.withDensity (fun a => ENNReal.ofReal (T.ticket R g A a))
lemma ticket_v {a : Stamp G I}(p:0<g): T.ticket R g A a ≠0 ↔ T.vault R g A a :=by
 constructor; intro h i; by_contra q; apply h; apply prod_eq_zero (mem_univ i); exact if_neg q
 intro q; apply ne_of_gt; exact Finset.prod_pos fun i _=> T.fee_holds R g (A i) (q i) p
lemma den_v (a:Stamp G I) : stamp g A a∈ den R A ↔ (∀ i,unlock g (A i) (key a i)∈near R (A i)):= ⟨fun h i=> h i (Set.mem_univ _),fun h i _=> h i⟩
lemma vault_v (a:Stamp G I) (h:∀ i,key a i∈ T.input g): T.vault R g A a ↔ stamp g A a∈ den R A:=⟨fun k=>(den_v ..).2 fun i=>(k i).1,fun k i=> ⟨(den_v ..).1 k i,h i⟩⟩
lemma ticket_nn (p:0<g)(a:Stamp G I): 0≤T.ticket R g A a:= prod_nonneg fun i _=> T.fee_nn R g _ p _
lemma ticket_m : Measurable (T.ticket R g A):= Finset.measurable_prod _ fun i _=> (fee_c ..).comp (g:=T.fee R g (A i)) (f:=fun a : Stamp G I=>key a i) (by unfold key Function.curry; fun_prop)
@[fun_prop] lemma stamp_m : Measurable (stamp g A):= by unfold stamp key Function.curry; fun_prop
abbrev lobby (G:Gauge)(I:Type)[Fintype I] := Measure.pi fun _:I=> G.probHaar
lemma arrange (K:Chart G)(p:0<g)(u:R≤K.radius)(v: K.C*R≤T.radius): MeasurePreserving (stamp g A) (T.law R g A) ((lobby G I).restrict (den R A)):= by
 let μ (i:I):= T.time R g (A i); have hk(i):= T.install K R g (A i) p u v; haveI : ∀ i,SigmaFinite (μ i):= fun i=> SigmaFinite.withDensity_ofReal _
 let e := MeasurableEquiv.curry I G.ColorIndex ℝ; let U : Stamp G I→ ℝ≥0∞ := fun a=> ENNReal.ofReal (T.ticket R g A a)
 let m(i:I)(a:Atom G):= ENNReal.ofReal (T.fee R g (A i) a); let W(x:I→ Atom G):=∏ i,m i (x i); have he(i:I): Measurable (m i):= (T.fee_c R g (A i)).ennreal_ofReal
 have hx:U=W ∘ e:= funext fun a=> by unfold U ticket; rw [ENNReal.ofReal_prod_of_nonneg (fun i _=> T.fee_nn R g _ p (key a i))]; rfl
 have hd := measurePreserving_pi _ _ hk
 have hw: ((lobby G I).restrict (den R A))=Measure.pi (fun i=> G.probHaar.restrict (near R (A i))):= Measure.restrict_pi_pi ..
 rw [hw]; refine hd.comp (f:=e) (μa:=T.law R g A) ?_
 unfold law; rw [show (fun a=>ENNReal.ofReal _)=_ from hx]; change MeasurePreserving _ _ (Measure.pi fun i=> volume.withDensity (m i)); rw [←Work.F05.piDensity (fun _:I=>volume) m he]
 exact MP.fund (f:=e) MP.volume_curry W (Finset.measurable_prod _ (fun i _=> (he i).comp (measurable_pi_apply _))) -- tune
-- log Jacob
abbrev angDim (G:Gauge)(I:Type) [Fintype I]:= Fintype.card I*G.lieDim
abbrev base (T:Pub G)(I:Type)[Fintype I] (g:ℝ):= T.Q.scale ^ Fintype.card I * g^angDim G I
def dust (a:Stamp G I):= ∑ i, Real.log (T.Q.J (grant g (key a i)))
lemma base_pos (I:Type)[Fintype I](p:0<g) : 0<T.base I g:=by unfold base; have := T.actual.scale; positivity
lemma ticket_c (a:Stamp G I)(p:0<g)(h:T.vault R g A a) : T.ticket R g A a=T.base I g*Real.exp (T.dust g a):=by
 unfold ticket dust; rw [Real.exp_sum]; have hx:T.base I g=∏ _:I,g^many G*T.Q.scale:=by simp only [Finset.prod_const, Finset.card_univ,mul_pow]; unfold base angDim many; rw [mul_comm (Fintype.card I),_root_.pow_mul,mul_comm]
 rw [hx,← Finset.prod_mul_distrib]; refine prod_congr rfl fun i _=>?_; rw [fee,if_pos (h i), Real.exp_log (T.actual.pos _ (h i).2)]; unfold bare; ring
lemma dust_c (a:Stamp G I)(u:ℝ)(v:∀ i, ‖grant g (key a i)‖ ≤ u) (p:u≤T.radius) : |T.dust g a| ≤ Fintype.card I*(T.C*u):=by
 refine (Finset.abs_sum_le_sum_abs ..).trans ((sum_le_sum (g:=fun _=>T.C*u) (fun i _=>?_)).trans_eq (by simp [nsmul_eq_mul])); exact (T.log_tariff _ ((v i).trans p)).trans (mul_le_mul_of_nonneg_left (v i) T.cost)
lemma dust_m : Measurable (T.dust (I:=I) g):= by unfold dust; apply Finset.measurable_sum; intro i hi; apply Measurable.log; have h:=T.actual.borel; apply h.comp; unfold key Function.curry; fun_prop -- tune
end YM.CF.BProof.Release.Pub
