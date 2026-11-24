import GaugeFieldConstruction.Tress
/- Data model Lift tape -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 130000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {K d v t r u c h a b h0:ℝ}{j k:ℕ}{m B n:Side}{X:Type}[NormedAddCommGroup X][NormedSpace ℝ X] [MeasurableSpace X][BorelSpace X][SecondCountableTopology X]
namespace MastTin
open Shield Echo Ledger Jet
local notation "GS"=> SU.group
abbrev Hubber(n:Side):= Support (More n)
abbrev Micro {n:Side}(p:BudgetPoint)(R:Support (More n))(A:Pane n→ X)(c:ℝ): Prop:=0 ≤ c ∧ Envelope A ∧ LocalOn R A ∧∀ U: Pane n,pingS p.threshold R U → Allows p.order (A ∘ Shield.solo p.threshold U) 0 c
variable {R S:Hubber n}{U V:Pane n→X}{p:BudgetPoint}
lemma micro_e (q:Micro p R U c)(u:c≤d):Micro p R U d:= ⟨q.1.trans u,q.2.1,q.2.2.1,fun W h=> (q.2.2.2 W h).mono u⟩
lemma micro_spin (q:Micro p R U c)(u:R⊆S):Micro p S U c:=⟨q.1,q.2.1,fun i j v=> q.2.2.1 i j (agrees_mono v u),fun W h=>q.2.2.2 W fun i g=> h i (fun p=> g (disjoint_of_subset_left u p))⟩
lemma micro_Z : Micro p R (0:Pane n→X) 0:=⟨le_rfl,by
 exact ⟨measurable_const,0,fun _=> norm_zero.le⟩,fun _ _ _=>rfl,fun i _=> allows_const (0:tangD n) (norm_zero.le)⟩
lemma micro_a (q:Micro p R U c)(Q:Micro p R V d): Micro p R (U+V) (c+d):=by
 refine ⟨add_nonneg q.1 Q.1,?_,fun i j v=> congrArg₂ (· + ·) (q.2.2.1 _ _ v) (Q.2.2.1 _ _ v),fun i p=> (q.2.2.2 i p).add (Q.2.2.2 i p)⟩ -- syntax use by refine
 obtain ⟨v,a⟩:=q.2.1.cost; obtain ⟨b,H⟩:= Q.2.1.cost; exact ⟨q.2.1.meas.add Q.2.1.meas,v+b,fun i=> (norm_add_le ..).trans (add_le_add (a i) (H i))⟩
variable [ProperSpace X]
lemma micro_l {Y:Type} [NormedAddCommGroup Y][NormedSpace ℝ Y][MeasurableSpace Y][BorelSpace Y][SecondCountableTopology Y] (L:X→L[ℝ]Y)(u:‖L‖≤v)(q:Micro p R U c): Micro p R (L ∘ U) (v*c):=⟨mul_nonneg (le_trans (norm_nonneg _) u) q.1,Girt.pole_w U L L.continuous q.2.1,fun i j p=>congrArg L (q.2.2.1 _ _ p),fun i p' => (q.2.2.2 i p').linear L u⟩ -- k nat modify
local instance (I:Type)[Fintype I][DecidableEq I]:MeasurableSpace (Op I):=borel _
local instance (I:Type)[Fintype I][DecidableEq I]:BorelSpace (Op I):=⟨rfl⟩
abbrev Lit(n:Side):= Pane n→ℂ
lemma micro_ms {f:Lit n}(r:Micro p R f c)(x:ℂ):Micro p R (x • f) (‖x‖*c):=by
 let L:= x • (ContinuousLinearMap.id ℝ ℂ); refine micro_l L ?_ r; exact (norm_smul x (ContinuousLinearMap.id ℝ ℂ)).le.trans (mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le)
lemma micro_rot {f:Lit n}(r:Micro p R f c)(x:ℝ):Micro p R (x • f) (|x| *c):=by
 have hx:=micro_ms r (Complex.ofReal x); simpa only [Complex.coe_smul,Complex.norm_real,Real.norm_eq_abs] using hx
lemma micro_m (Z:Pane n→ℝ) {F:Lit n}(q:Micro p R Z c)(H:Micro p R F d) : Micro p R (fun i=> Z i • F i) (2^p.order*c*d):=by
 let Y:=ContinuousLinearMap.lsmul ℝ ℝ (E:=ℂ) -- tune name
 refine ⟨mul_nonneg (mul_nonneg (by positivity) q.1) H.1, Env.scale q.2.1 H.2.1,fun i j v=> congrArg₂ _ (q.2.2.1 _ _ v) (H.2.2.1 _ _ v),fun i v=>?_⟩
 have he:= (q.2.2.2 i v).bilinear Y (H.2.2.2 i v) ContinuousLinearMap.opNorm_lsmul_le; rw [mul_one] at he; exact he
lemma micro_sum {I:Type*}(f: Finset I)(A:I→Lit n)(C:I→ℝ) (p:BudgetPoint)(u:Hubber n)(h:∀ i∈f,Micro p u (A i) (C i)) : Micro p u (∑ i∈f,A i) (∑ i∈f,C i):=by induction f using Finset.induction_on with | empty=>simp only [sum_empty]; exact micro_Z| @insert i f v ih => simp_rw [sum_insert v]; exact micro_a (h i (mem_insert_self ..)) (ih fun j p=> h j (mem_insert_of_mem p))
abbrev Pairs (n:Side): Type := Bool × Single n × Single n
abbrev Wa (n:Side): Type:= Option (Pairs n)
abbrev Paper (n:Side): Type:= Wa n → Lit n
def papW (n:Side)(h:ℝ): Wa n→ ℝ
| none=>1
| some _ => h^2
def DomainP {n:Side} (X:Hubber n) : Wa n → Prop
| none=>True
| some ⟨_,i,j⟩=>aptK i ∈X ∧ aptK j∈X
private lemma Dom_tr(u:R⊆S){i:Wa n}(w:DomainP R i): DomainP S i:=by cases i with|none=>trivial|some a=> exact ⟨u w.1,u w.2⟩
abbrev TrackD (p:BudgetPoint)(R:Hubber n)(h:ℝ)(A:Paper n)(C:ℝ): Prop:= ∃ L: Wa n→ℝ,(∀ i, Micro p R (A i) (L i)∧(¬ DomainP R i → A i=0))∧ ∑ i,papW n h i*L i ≤ C
def dot_Q {n:Side}: Wa n→ FC (Single n)
| none=>1
| some ⟨true,i,j⟩=>put i*takeF j
| some ⟨false,i,j⟩=>takeF i*put j
variable {A B':Paper n}
def marketD (A:Paper n)(i:Pane n): FC (Single n):=∑ j:Wa n,A j i • dot_Q j
lemma papW_v(i:Wa n) :0≤ papW n h i:=by cases i with|none=>exact zero_le_one|some v=> exact sq_nonneg _
lemma val_T (r:TrackD p R h A c):Envelope (marketD A):=by
 obtain ⟨V,q,-⟩:=r; exact Env.total (univ:Finset (Wa n)) fun i=> Girt.pole_w (A i) (· • dot_Q i) (continuous_id.smul continuous_const) (q i).1.2.1
abbrev val_mark(A:Paper n) : marker0 n:=marketD A -- should abbrev
lemma track_pos(u:TrackD p R h A c):0 ≤ c:=by obtain ⟨V,p,h⟩:=u; exact le_trans (sum_nonneg fun i _=>mul_nonneg (papW_v i) (p i).1.1) h
lemma track_zero : TrackD p R h (0:Paper n) 0:=⟨0,fun _=> ⟨micro_Z,fun _=>rfl⟩,by simp⟩
lemma track_p(u:TrackD p R h A c)(v:c≤d):TrackD p R h A d:=by obtain ⟨V,p,s⟩:=u; exact ⟨V,p,s.trans v⟩
lemma track_o(u:TrackD p R h A c)(v:R⊆ S):TrackD p S h A c:=by
 obtain ⟨V,p,s⟩:=u; exact ⟨V,fun i=> ⟨micro_spin (p i).1 v,fun l=>(p i).2 (mt (Dom_tr v) l)⟩,s⟩
lemma track_a(u:TrackD p R h A c)(v:TrackD p R h B' d): TrackD p R h (A+B') (c+d):=by
 obtain ⟨V,t,z⟩:=u; obtain ⟨S,q,k⟩:=v; refine ⟨fun i=> V i+ S i,fun i=> ⟨micro_a (t i).1 (q i).1, fun p=>?_⟩,?_⟩
 · rw [Pi.add_apply,(t i).2 p,(q i).2 p,add_zero]
 simp_rw [mul_add, sum_add_distrib]; exact add_le_add z k
lemma track_h(u:TrackD p R h A c)(k:ℂ): TrackD p R h (k • A) (‖k‖*c):=by
 obtain ⟨V,q,s⟩:=u; refine ⟨fun i=> ‖k‖*V i,fun i=> ⟨micro_ms (q i).1 k,fun v=>?_⟩,?_⟩
 · rw [Pi.smul_apply,(q i).2 v,smul_zero]
 simp_rw [mul_left_comm (papW _ _ _), ← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left s (norm_nonneg k) -- placeholder ..
lemma track_sum {ι:Type*}(s:Finset ι)(f:ι→Paper n)(C:ι→ℝ)(u:∀ i∈s,TrackD p R h (f i) (C i)) : TrackD p R h (∑ i∈s,f i) (∑ i∈s,C i):=by induction s using Finset.induction_on with|empty=> simp only [sum_empty]; exact track_zero| @insert i t p ih=> simp_rw [sum_insert p]; exact track_a (u i (mem_insert_self ..)) (ih fun j p=>u j (mem_insert_of_mem p))
lemma conn_a(A B:Paper n): marketD (A+B)=marketD A+marketD B:=funext fun i=>by unfold marketD; simp only [Pi.add_apply,add_smul,sum_add_distrib]
lemma conn_h(A:Paper n)(V:ℂ): marketD (V • A)=V • marketD A:=funext fun i=>by unfold marketD; simp only [Pi.smul_apply, smul_eq_mul,mul_smul, Finset.smul_sum]
lemma conn_Z: marketD (0:Paper n)=0:=funext fun i=>by simp [marketD]
lemma conn_X {I:Type*}(A:I→ Paper n)(s:Finset I): marketD (∑ i∈s,A i)=∑ i∈s,marketD (A i):=by induction s using Finset.induction_on with|empty=> simp only [sum_empty]; exact conn_Z|@insert i s p ih=> simp only [sum_insert p,conn_a,ih]
abbrev Flounces (n:Side):= Hubber n→Paper n
abbrev Torches (n:Side):Type:= Paper n× Flounces n
def Ion {n:Side}(S:Torches n): marker0 n:= marketD S.1+marketD (∑ i:Hubber n,S.2 i)
abbrev Dock(o:Seat n)(X:Hubber n):Prop:=o∈ X∧ Grove (Tenant.terr _) X
abbrev TraceD (p:BudgetPoint)(o:Seat n)(h a:ℝ)(X:Flounces n)(c:ℝ):Prop:= ∃ V:Hubber n→ℝ,(∀ i,TrackD p i h (X i) (V i) ∧ (¬ Dock o i→X i=0)) ∧(∑ i:Hubber n,rent a i*V i) ≤ c
abbrev Inscribe (p:BudgetPoint)(o:Seat n)(h a:ℝ)(X:Torches n)(c d:ℝ):Prop:= TrackD p (Pach o) h X.1 c ∧ TraceD p o h a X.2 d
variable {o:Seat n}{X U:Flounces n}
lemma trace_pos(u:TraceD p o h a X c): 0≤c:=by obtain ⟨V,p,h⟩:=u; exact le_trans (sum_nonneg fun i _=>mul_nonneg (Real.exp_pos _).le (track_pos (p i).1)) h
lemma trace_p(u:TraceD p o h a X c)(v:d≤a)(z:c≤r): TraceD p o h d X r:=by obtain ⟨V,t,h⟩:=u; exact ⟨V,t,(sum_le_sum (fun i _=>mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_right v (by positivity))) (track_pos (t i).1))).trans (h.trans z)⟩ -- tune
lemma trace_Z: TraceD p o h a (0:Flounces n) 0:=⟨0,fun i=> ⟨track_zero,fun _=>rfl⟩,by simp⟩
lemma trace_u(u:TraceD p o h a X c)(v:TraceD p o h a U d): TraceD p o h a (X+U) (c+d):=by
 obtain ⟨V,t,z⟩:=u; obtain ⟨A,q,f⟩:=v; refine ⟨fun i=> V i+A i, fun i=> ⟨track_a (t i).1 (q i).1,fun p=>?_⟩,?_⟩
 · rw [Pi.add_apply,(q i).2 p,(t i).2 p,add_zero]
 simp_rw [mul_add,sum_add_distrib]; exact add_le_add z f
lemma trace_m(u:TraceD p o h a X c)(k:ℂ): TraceD p o h a (k • X) (‖k‖*c):=by
 obtain ⟨V,t,z⟩:=u; refine ⟨fun i=> ‖k‖*V i,fun i=> ⟨track_h (t i).1 k,fun v=>?_⟩,?_⟩
 · rw [Pi.smul_apply, (t i).2 v, smul_zero]
 simp_rw [mul_left_comm (rent _ _), ←mul_sum]; exact mul_le_mul_of_nonneg_left z (norm_nonneg k)
lemma trace_sum {ι:Type*}(s:Finset ι)(f:ι→Flounces n)(C:ι→ℝ)(u:∀ i∈s,TraceD p o h a (f i) (C i)) : TraceD p o h a (∑ i∈s,f i) (∑ i∈s,C i):=by induction s using Finset.induction_on with|empty=> simp only [sum_empty]; exact trace_Z| @insert i t p ih=> simp_rw [sum_insert p]; exact trace_u (u i (mem_insert_self ..)) (ih fun j p=>u j (mem_insert_of_mem p))
end MastTin
end YM.CF.XGarden
end
