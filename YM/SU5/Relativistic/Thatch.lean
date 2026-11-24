import YM.SU5.Relativistic.Demi
import YM.SU5.Relativistic.Lord
import YM.CF.BPress.Law
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Papyrus.Mosaic
open Function Finset Filter MeasureTheory Lattice Wilson Fixed.Pivots GaugeFlux
open scoped Matrix BigOperators
variable {N C: Side}(L:Ratio C N)
local notation "W_"=> L.count
local notation "T_"=> Site C
local notation "F_"=> Site N
local notation "P_"=> Site L.count
open scoped Topology BigOperators Matrix.Norms.Frobenius InnerProductSpace
open RG RG.PathData Work.F03 Pharos
local notation "J"=> Link N
local notation "O"=> Face (Per N)
local notation "V"=> Site C
-- book cardinal

def losers (A:Finset (Site C)):= A.biUnion (brick L)
def meter(A:Finset (Site C)) := wires L∪ losers L A
lemma lows_ss(A:Finset (Site C)): losers L A⊆ batchIn L:=by intro i h; obtain ⟨j,w,t⟩:= mem_biUnion.mp h; exact brick_b L _ t
lemma meter_ss(A:Finset (Site C)):meter L A ⊆ vivo L:=union_subset sdiff_subset ((lows_ss ..).trans (batch_in L))
lemma meter_card(A:Finset (Site C)): (meter L A).card=(wires L).card + A.card*(livelies W_).card:=by
 unfold meter; rw [card_union_of_disjoint (Finset.disjoint_left.mpr fun {x} t y=> (mem_sdiff.mp t).2 (lows_ss _ _ y)),losers,card_biUnion]; · simp [brick,card_image_of_injective _ (rise_b ..)]
 intro i p j q e; exact (mitt_d L i j e).mono (brick_in L i) (brick_in L j)
lemma meter_m(A: Finset V)(p:V)(v:p∉A) : Disjoint (mitt L p) (meter L A):=Finset.disjoint_left.mpr fun {i} t q=> (mem_union.mp q).elim (fun u=> Finset.disjoint_left.mp (wire_d L p) t u) (fun h=> by obtain ⟨j,k,x⟩:=mem_biUnion.mp h; exact Finset.disjoint_left.mp (mitt_d L p j (fun i=> v (i.symm ▸ k))) t (brick_in L j x))
-- walruses
variable (h:2≤ C.val)
def tradeH(x:J):O:= if v: how L x then (pays L h x v).choose else (0, ⟨(0,1),by decide⟩)
lemma sold (i:J)(p:i∈vivo L): i∈support (tradeH L h i)∧∀ j∈ support (tradeH L h i), j≠i→ how L j→ ranking L j<ranking L i:=by unfold tradeH; rw [dif_pos (show how L i from (mem_filter.mp p).2)]; exact (pays L h i ((mem_filter.mp p).2)).choose_spec
lemma trading:Set.InjOn (tradeH L h) (↑(vivo L)):=by
 intro i p j q e; by_contra g; have hp:=sold L h i p; have hq:=sold L h j q; have hv:= hq.2 _ (e ▸ hp.1) g (mem_filter.mp (show i∈vivo L from p)).2; exact not_lt_of_gt hv (hp.2 _ (e.symm ▸ hq.1) (Ne.symm g) (mem_filter.mp (show j∈vivo L from q)).2)
variable (G:Gauge)
local notation "Q"=> Config G N
def parties(U:Q)(s:J):= faceValue U (tradeH L h s)
lemma wheelPres {i:J}(s: i∈ vivo L)(U:Q)(x:2≤N.val): MeasurePreserving (fun v:G.El=> parties L h G (Function.update U i v) i) G.probHaar G.probHaar:=by
 have ht:= (sold L h i s).1
 unfold parties; generalize tradeH L h i=b at *; obtain ⟨y,⟨⟨p,b⟩,e⟩⟩:= b
 simp only [Fixed.Pivots.support, window,mem_singleton,mem_insert] at ht; unfold faceValue; simp only []; simp_rw [square_formula G]; have he:p≠b:=e.ne; have hp:y≠y+step p:=step_dist x y p; have hx:y≠y+step b:=step_dist x y b
 have hu(a m n:G.El):a*m*n=a*(m*n):=mul_assoc ..
 rcases ht with rfl|rfl|rfl|rfl
 · simp only [update_self,update_of_ne (show (y+step p,b)≠ (y,p) by simp [he.symm]),update_of_ne (show (y+step b,p)≠ (y,p) by simp [hx.symm]),update_of_ne (show (y,b)≠(y,p) by simp [he.symm]),hu]; exact measurePreserving_mul_right ..
 · simp only [update_self,update_of_ne (show (y,p)≠ (y+step p,b) by simp [he]),update_of_ne (show (y+step b,p)≠(y+step p,b) by simp [he]),update_of_ne (show (y,b)≠(y+step p,b) by simp [hp]),show ∀ (l m n o:G.El),l*m*n*o=l*m*(n*o) from fun _ _ _ _=> mul_assoc ..]; exact G.preserve_two_sided ..
 · simp only [update_self,update_of_ne (show (y,p)≠(y+step b,p) by simp [hx]),update_of_ne (show (y+step p,b)≠(y+step b,p) by simp [he.symm]),update_of_ne (show (y,b)≠(y+step b,p) by simp [he.symm])]; exact (G.preserve_two_sided ..).comp G.preserve_inv
 simp only [update_self,update_of_ne (show (y,p)≠ (y,b) by simp [he]),update_of_ne (show (y+step p,b)≠(y,b) by simp [hp.symm]),update_of_ne (show (y+step b,p)≠(y,b) by simp [he])]; exact (measurePreserving_mul_left ..).comp G.preserve_inv

def spun(A:Finset J): Q→ Q:= Fixed.Pivots.batch A (fun i x=> parties L h G x i)
lemma spun_orig (A:Finset J)(p:A⊆ vivo L)(e:2 ≤ N.val) : MeasurePreserving (spun L h G A) (prior G N) (prior G N):=by
 apply Fixed.Pivots.batch_preserves _ A (fun i (x:Q)=> parties L h G x i) (fun i _=> (by unfold parties faceValue; fun_prop)) (ranking L)
 · intro i k j g x he u c; unfold parties; apply face_unique; intro a v; apply update_of_ne; intro r; subst a; exact not_lt_of_ge x ((sold L h j (p g)).2 i v he (mem_filter.mp (p k)).2)
 intro i u t; exact wheelPres L h G (p u) t e

variable (W:PathData G)(D:ℕ)
def tray (i: T_)(U:Q): Config G W_ := U ∘ raise L i
lemma tray_pres (i:T_):MeasurePreserving (tray L G i) (prior G N) (prior G W_):= BPress.Law.keys G.probHaar (raise L i) (rise_b L i)
lemma tray_loc (i: T_)(B:Clip)(t s:ℝ)(U T:Q)(p:∀ j∈ mitt L i,U j=T j): localPay G W D B t s (tray L G i U)=localPay G W D B t s (tray L G i T):=by
 let x:=tray L G i U; let y:=tray L G i T; have he(j:Link W_)(h:indoors j):x j=y j:=p _ (mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _,h⟩))
 have hx(j:Face (Per W_))(t:j∈ ort W_): girth G x j= girth G y j:= congrArg G.chord (face_unique G x y j (fun i h=> he i (here_in _ (mem_filter.mp t).2 _ h)))
 have hg: x∈ Mild W_ G t↔ y∈ Mild W_ G t:= by unfold Mild; simp only [Set.mem_setOf_eq]; constructor<;> intro k n v; rw [←hx n v]; exact k n v; rw [hx n v]; exact k n v
 have hD:crateB G x=crateB G y:=sum_congr rfl fun j t=> congrArg (fun g:ℝ=>g^2) (hx j t)
 have hb: boxE G W D B x= boxE G W D B y:=by
    unfold boxE; rw [hD]; congr 1 -- tune congr
    apply sum_congr rfl; intro k u; rw [small_g x y k D (show deep D k.1 from (mem_filter.mp u).2) he W]
 unfold localPay; change (Mild W_ G t).indicator _ x= (Mild W_ G t).indicator _ y; by_cases v:x∈ Mild W_ G t; · rw [Set.indicator_of_mem v,Set.indicator_of_mem (hg.mp v),hb]
 rw [Set.indicator_of_notMem v,Set.indicator_of_notMem (mt hg.mpr v)]

lemma payP (u:Config G N)(p:Clip)(k t:ℝ): 0 ≤ localPay G W D p k t u:=by
 unfold localPay; by_cases v:u∈ Mild N G k; · rw [Set.indicator_of_mem v]; exact (Real.exp_pos _).le
 rw [Set.indicator_of_notMem v]
lemma patS (u:Config G N)(p:Clip)(k t:ℝ)(h:0≤t): localPay G W D p k t u ≤1 :=by
 unfold localPay; by_cases v:u∈ Mild N G k; · rw [Set.indicator_of_mem v]; exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by linarith) (box_pos ..)) zero_le_two)
 rw [Set.indicator_of_notMem v]; exact zero_le_one
-- piecing
lemma marksProd (S:Finset J)(f g: Q→ℝ)(p:Measurable f)(q:Measurable g)(u:∀ U T, (∀ i∈ S,U i=T i)→ f U=f T)(v:∀ U T, (∀ i∉ S,U i=T i)→ g U=g T):
 (∫ i:Q,f i*g i∂prior G N)=(∫ i,f i∂prior G N)*∫ i,g i∂prior G N:=by
 let V':= prior G N; let F(U:Q):= f U*g U; let X(s:Q × Q):= BPress.Law.rep S s.1 s.2; have ht:MeasurePreserving X (V'.prod V') V':= BPress.Law.splice ..
 have hy:(∫ i,F i∂V')=∫ s:Q × Q,F (X s)∂V'.prod V':=by have hx := (integral_map (φ:=X) (f:=F) ht.aemeasurable ((p.mul q).aestronglyMeasurable)); rw [ht.map_eq] at hx; exact hx
 refine hy.trans ?_; rw [show (fun s:Q×Q=> F (X s))=(fun s:Q×Q=> f s.1*g s.2) from funext fun s=>congrArg₂ (·*·) (u _ _ fun i t=> BPress.Law.rep_L S s.1 s.2 i t) (v _ _ fun i t=> BPress.Law.rep_R S s.1 s.2 i t), integral_prod_mul]

variable {p:Clip}{σ C' Λ:ℝ}(B: W.Bounds p σ C' Λ) (A:Finset (Site C))
def glory(P:Finset (Site C))(B:Clip)(t k:ℝ)(x:Q):= ∏ i∈P,localPay G W D B t k (tray L G i x)
include B in
lemma goldMeas (t k:ℝ): Measurable (glory L G W D A p t k):= by unfold glory; exact Finset.measurable_fun_prod _ fun i _=> (local_meas G W D B ..).comp (tray_pres ..).measurable
include B in
lemma goldEarn(t k:ℝ) : ∫ i:Q,glory L G W D A p t k i ∂ prior G N=(∫ x:Config G W_, localPay G W D p t k x∂prior G W_)^A.card :=by
 induction A using Finset.induction_on with
 | empty=> simp [glory]
 | @insert a s x ih=>
    let f:= localPay (W:=W_) G W D p t k; let M:= fun i=> f (tray L G a i); let S:= mitt L a
    have hf:(∫ i,M i∂prior G N)=∫ i,f i∂prior G W_:=by rw [← (tray_pres L G a).map_eq]; exact (integral_map (tray_pres L G a|>.aemeasurable) (local_meas G W D B t k|>.aestronglyMeasurable)).symm
    rw [show glory L G W D (insert a s) p t k=(fun i:Q=> M i*glory L G W D s p t k i) from funext fun i=> by unfold glory; rw [prod_insert x] <;> try rfl,marksProd G S M _ ((local_meas G W D B t k).comp (tray_pres L G a).measurable) (goldMeas L G W D B s t k) ?_ ?_, hf,ih]; -- tune
    · rw [card_insert_of_notMem x,pow_succ]; apply mul_comm
    · exact fun i j e=> tray_loc L G W D _ _ _ _ i j e
    intro i j e; exact prod_congr rfl fun v pS=> tray_loc L G W D _ _ _ _ i j (fun w hv=> e _ (fun t=> Finset.disjoint_left.mp (mitt_d L v a fun h=>x (h ▸ pS)) hv t))

include B in
lemma wheelBill (t k:ℝ) (f:G.El→ℝ)(mf:Continuous f)(g:2≤N.val) :
 (∫ i:Q, (∏ j∈ meter L A,f (parties L h G i j))*glory L G W D Aᶜ p t k i∂prior G N)=(∫ x:G.El,f x∂G.probHaar)^(meter L A).card * (∫ x:Config G W_,localPay G W D p t k x∂prior G W_)^Aᶜ.card:=by
 let S:= meter L A; let F(u:Q):=∏ i∈S,f (u i); let P:= glory L G W D Aᶜ p t k; let E(u:Q):= F u*P u
 have hx:Measurable F:=(continuous_finsetProd _ (fun i _=> mf.comp (continuous_apply i))).measurable; have hy:Measurable P:= goldMeas L G W D B _ t k; have hr(U T:Q)(p:∀ i∉S,U i=T i): P U=P T:= prod_congr rfl fun j e=> tray_loc L G W D _ _ _ _ U T fun k h=> p k fun v=> Finset.disjoint_left.mp (meter_m L A j (mem_compl.mp e)) h v
 let q:=spun L h G S; have hp:= spun_orig L h G S (meter_ss L A) g
 rw [show (fun i:Q=>(∏ j∈_,f (parties L h G i j))*_)= E ∘ q from ?_]; swap
 · funext i; exact congrArg₂ (·*·) (prod_congr rfl (fun j w=> congrArg f (if_pos w).symm)) (hr _ _ (fun j p=> (if_neg p).symm)) -- tune if
 have he: (∫ i:Q,E (q i)∂prior G N)= (∫ i:Q,E i∂prior G N):= (integral_map (f:=E) hp.aemeasurable (hx.mul hy|>.aestronglyMeasurable)).symm.trans (by rw [hp.map_eq])
 change (∫ i:Q,E (q i)∂prior G N)=_; rw [he]; refine (marksProd G S F P hx hy ?_ hr).trans ?_
 · intro i j h; exact prod_congr rfl fun v k=> congrArg f (h v k)
 unfold F P; rw [integral_pivots G S (fun _=> f), goldEarn L G W D B]; simp [S]
end YM.CF.Papyrus.Mosaic
#print axioms YM.CF.Papyrus.Mosaic.wheelBill
