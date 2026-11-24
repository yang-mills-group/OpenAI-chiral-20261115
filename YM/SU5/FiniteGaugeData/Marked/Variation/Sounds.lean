import YM.SU5.FiniteGaugeData.Marked.Variation.Public

set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Satin
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Py Py.Rate LocalLimit Preparation Journey Vale VolumeCape
section
variable {S X:Type*}[PseudoMetricSpace X](u v:ℕ→ℕ)(gate:ℕ→ℕ)(Us:ℕ→ℕ→Prop)(A:S→ ℕ→ℕ→X)(g:Set S)(F:S→ℕ→X)(G:S→X)
-- sequencing assumptions on arbitrary normalized values
structure Honors : Prop where
 v_t : Tendsto v atTop atTop
 u_t : Tendsto u atTop atTop
 legal (p:ℕ→ℕ)(q:∀ᶠ i in atTop,Us i (p i)) : (∀ᶠ i:ℕ in atTop,gate (u i) ≤ v (p i)) ∧ Tendsto (fun i=>v (p i)) atTop atTop
 supply (r:ℕ) : ∃ t,Us r t
 reads(x:S)(p:x∈g): Couplet u v (A x) (F x) (G x) (fun r=>∀ᶠ j in atTop,Us j (r j))
 premium : ∃ i₀:ℕ,∀ ε:ℝ, 0< ε → ∃ Z:Finset S, ↑Z⊆g ∧ ∃ k₀:ℕ,∀ s∈ g, ∃ t∈Z, ∀ i≥i₀,∀ k≥ k₀, gate i ≤ k → dist (A s i k) (A t i k)< ε

structure Zoom:Prop where
 spring :∀ᶠ i:ℕ in atTop,∀ ε:ℝ,0< ε → ∀ᶠ k:ℕ in atTop,∀ s∈g, dist (A s i (v k)) (F s i) < ε
 spectrum (ε:ℝ):0<ε→∀ᶠ r:ℕ in atTop,∀ s∈g,dist (F s (u r)) (G s)<ε
 public_ (ε:ℝ):0<ε→∀ᶠ r:ℕ in atTop,∀ s∈g, ∀ k, Us r k → dist (A s (u r) (v k)) (G s)<ε
namespace Honors
variable (h: Honors u v gate Us A g F G)
private lemma split_t{S:Type*}{f:Filter ℕ}(A:Finset S)(p:S→ℕ→Prop)(h:∀i∈A,∀ᶠ t:ℕ in f,p i t): ∀ᶠ i:ℕ in f,∀ t∈ A,p t i:= (eventually_all_finset A).mpr h
include h
-- convert Couplet paths to one late threshold on all indices (still in same sequences)
lemma course (s:S)(e:s∈g) (δ:ℝ)(p:0<δ):∀ᶠ r:ℕ in atTop,∀ k,Us r k → max (gate (u r)) 0 ≤ v k ∧ dist (A s (u r) (v k)) (G s)< δ:=by
 let P(r k:ℕ):= max (gate (u r)) 0 ≤ v k ∧ dist (A s (u r) (v k)) (G s)< δ
 let y(r:ℕ):= if x:∃ k,Us r k∧¬P r k then Classical.choose x else Classical.choose (h.supply r)
 have m(r):Us r (y r):=by
    unfold y; split
    next z=>exact (Classical.choose_spec z).1
    next=>exact Classical.choose_spec _
 have t:= (h.reads s e).paths y (Eventually.of_forall m)
 filter_upwards [(h.legal y (Eventually.of_forall m)).1,Metric.tendsto_nhds.mp t δ p] with r i m'
 intro k z; by_contra! t'
 have l:∃ k,Us r k∧ ¬P r k:= ⟨_,z,fun x=>lt_irrefl _ (x.2.trans_le (t' x.1))⟩ -- x.1 max maybe t' reduced
 have hp:P r (y r):= ⟨by simpa using i,m'⟩
 unfold y at hp; exact ((Classical.choose_spec l).2 (by simpa [dif_pos l] using hp))
lemma late (b:ℕ): ∀ᶠ r in atTop,∀ k,Us r k→ max b (gate (u r))≤ v k:=by
 let y(r:ℕ):= if x:∃ k,Us r k∧v k < max b (gate (u r)) then Classical.choose x else Classical.choose (h.supply r)
 have m(r):Us r (y r):=by
    unfold y; split
    next z=> exact (Classical.choose_spec z).1
    next=> exact Classical.choose_spec _
 obtain ⟨E,F⟩:= h.legal y (Eventually.of_forall m)
 filter_upwards [E,F.eventually_ge_atTop b] with r z p
 intro k u'; by_contra! e
 have l:∃ k,Us r k∧v k < max b (gate (u r)):=⟨k,u',e⟩
 have hv:max b (gate (u r)) ≤ v (y r):= max_le p z
 unfold y at hv; exact ((Classical.choose_spec l).2.not_ge (by simpa only [dif_pos l] using hv))
lemma filmed:Zoom u v Us A g F G:=by
 obtain ⟨i₀,q⟩:=h.premium
 have ship(s t:S)(u':s∈g)(p:t∈g)(ε:ℝ)(k₀:ℕ)(q:∀ i≥i₀,∀ k≥ k₀, gate i ≤ k → dist (A s i k) (A t i k)< ε):
    (∀ i≥i₀, dist (F s i) (F t i) ≤ ε)∧ dist (G s) (G t) ≤ ε:=by
    have e(i:ℕ)(e:i₀ ≤ i):dist (F s i) (F t i) ≤ ε:=by
       apply le_of_tendsto (((h.reads s u').inner i).dist ((h.reads t p).inner i))
       filter_upwards [h.v_t.eventually_ge_atTop k₀,h.v_t.eventually_ge_atTop (gate i)] with a b c
       exact (q i e _ b c).le
    exact ⟨e,le_of_tendsto ((h.reads s u').periods.dist (h.reads t p).periods) ((h.u_t.eventually_ge_atTop i₀).mono fun r E=>e (u r) E)⟩
 constructor
 · filter_upwards [eventually_ge_atTop i₀] with i p
   intro e t; let δ:= e/4; obtain ⟨Y,P,k₀,d⟩:=q δ (by dsimp [δ]; linarith)
   filter_upwards [split_t Y (fun a k=>dist (A a i (v k)) (F a i)<δ) (fun a u=>Metric.tendsto_nhds.mp ((h.reads a (P u)).inner i) δ (by dsimp [δ]; linarith)),h.v_t.eventually_ge_atTop (gate i),h.v_t.eventually_ge_atTop k₀] with k G' m x
   intro s g'; obtain ⟨z,n,e'⟩:=d s g'; have hp':=e' i p (v k) x m; have hk:= (ship s z g' (P n) _ _ e').1 i p; have hy:=G' z n
   have h':=dist_triangle_right (A s i (v k)) (F s i) (F z i); have hh:=dist_triangle (A s i (v k)) (A z i (v k)) (F z i); unfold δ at *; linarith
 · intro e t; let δ:= e/4; obtain ⟨Y,P,k₀,d⟩:=q δ (by dsimp [δ]; linarith)
   filter_upwards [h.u_t.eventually_ge_atTop i₀,split_t Y (fun a r=>dist (F a (u r)) (G a)<δ) (fun a q=>Metric.tendsto_nhds.mp ((h.reads a (P q)).periods) δ (by dsimp [δ]; linarith))] with r u' T
   intro s g'; obtain ⟨z,n,e'⟩:=d s g'; obtain ⟨p',L⟩:= ship s z g' (P n) _ _ e'; have hp':=p' _ u'; have hy:=T z n
   have h':=dist_triangle_right (F s (u r)) (G s) (G z); have hh:=dist_triangle (F s (u r)) (F z (u r)) (G z); unfold δ at *; linarith
 intro e t; let δ:= e/4; have E:0<δ:=by dsimp [δ]; linarith
 obtain ⟨Y,P,k₀,d⟩:=q δ E
 filter_upwards [split_t Y _ (fun a q=> h.course u v gate Us A g F G a (P q) δ E),h.late u v gate Us A g F G k₀,h.u_t.eventually_ge_atTop i₀] with r T J u'
 intro s g' k w; obtain ⟨z,n,e'⟩:=d s g'; have hp:=J k w; have hk:=e' _ u' _ ((le_max_left ..).trans hp) ((le_max_right ..).trans hp); have hy:=(ship s z g' (P n) _ _ e').2; have ht:= (T z n k w).2
 have h':=dist_triangle_right (A s (u r) (v k)) (G s) (G z); have hh:=dist_triangle (A s (u r) (v k)) (A z (u r) (v k)) (G z); unfold δ at *; linarith
end Honors
end
#check eventually_all_finset
attribute [local instance] opCStarAlgebra
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1 ≤ Λ.x){i k:ℕ→ℕ}
variable (a:StrictMono i)(b:StrictMono k)
local notation "K"=>tent Y H
variable {I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(Q:Universal Y H i k I E)(S:Finset Cover)(s:ℕ)
variable (u:Chorus)(v:Bracket S u)
local notation "Q₀" f=> note (tent Y H) f u
include Q v
lemma fleece:
 Zoom i k (fun x z=> legacy Y (i x) (k z)) (fun (x:Purse S) n v'=> sharp Y H s n v' (Q₀ x.val)) (Tower Λ l S) (fun x=>I s (Q₀ x.val)) (fun x=> E s (Q₀ x.val)) := by
 refine Honors.filmed i k (fun i=> (Y.voyage i).kick) (fun m n=> legacy Y _ _) _ _ _ _ ?_
 constructor
 · exact Q.pick.grow_k.tendsto_atTop
 · exact Q.pick.grow_i.tendsto_atTop
 · intro p q; exact ⟨q.mono fun r h=> Q.pick.ticket r (p r) h, Cabinet.walks Y H Q.pick q⟩
 · exact fun r=> (((Y.uv_grows.comp Q.pick.grow_k).tendsto_atTop.eventually_ge_atTop ((Y.ir (i r)).val^5))).exists
 · exact fun x _=> Q.together s _ ⟨⟨S,v.harmony ▸ note_t K u x.property v.tines⟩,fun _=>by contradiction⟩
 simpa only [dist_eq_norm] using patrons Y S s u H v
#check @Honors.filmed
-- positively homogeneous rescale -- including the cash-null case where normalization on sphere doesn't apply.
omit Q v in
protected lemma pool {M:Type*} (A:M→ℂ)(T:M→ℝ)(h:0≤T)(p:∀ a:M,∀ (z:ℝ),0 ≤ z → ∃ u, T u=z*T a ∧ ‖A u‖= z*‖A a‖) (ε:ℝ)(e:∀a,T a≤ 1→ ‖A a‖<ε)(x:M):‖A x‖ ≤ ε*T x:=by
 rcases (show (0:ℝ)≤T x from h x).eq_or_lt with s|s
 · rw [←s,mul_zero]; by_contra! t; let v:= |ε| / ‖A x‖; obtain ⟨w,m,u⟩:=p x v (by unfold v; positivity); rw [←s,mul_zero] at m; have h:=e _ (by rw [m]; norm_num); rw [u,show v*‖A x‖=|ε| from div_mul_cancel₀ _ t.ne'] at h; linarith [le_abs_self ε]
 obtain ⟨w,m,u⟩:=p x (T x)⁻¹ (by positivity); rw [inv_mul_cancel₀ s.ne'] at m; have t:=e w (by rw [m]); rw [u,mul_comm,←div_eq_mul_inv,div_lt_iff₀ s] at t; exact t.le

def hue (x:Purse S)(c:ℂ):Purse S:=⟨c • x.val,⟨fun _=>by contradiction,Girt.kitE (fun _ :PairsC=>c) _ (fun (a b:ℂ)=> a • b) (by exact continuous_fst.smul continuous_snd) (Girt.rite_c _) x.property.env,fun i j p t=>congrArg (fun (i:ℂ)=>c • i) (x.property.locus i j p t)⟩⟩
omit Q v in
private lemma note_hue (x:Purse S)(c:ℂ): note K (hue S x c).val u=c • note K x.val u:=by funext m z; rw [note_v,Pi.smul_apply,Pi.smul_apply,note_v,show (hue S x c).val _=c*_ from rfl,mul_smul]
-- can evaluate homogeneity in unfinanced corner too; no integrability req
lemma hues (x:Purse S)(c:ℂ) : price Λ l S (hue S x c).val= ‖c‖*price Λ l S x.val ∧ ((∀i k,sharp Y H s i k (Q₀ (hue S x c).val)=c*sharp Y H s i k (Q₀ x.val)) ∧ (∀n,I s (Q₀ (hue S x c).val) n=c*I s (Q₀ x.val) n) ∧ E s (Q₀ (hue S x c).val)=c*E s (Q₀ x.val)):=by
 constructor
 · unfold price Touch Common.touch Common.amount; rw [mul_sum]; refine sum_congr rfl fun i _=>?_ ; unfold hue; simp_rw [Pi.smul_apply,norm_smul,integral_const_mul]
 have p(i k):sharp Y H s i k (Q₀ (hue S x c).val)=c*sharp Y H s i k (Q₀ x.val):=by
    simp only [note_hue]
    let m:=momentm Y i s; let t:= send Y H i s (note K x.val u m); have he: send Y H i s (c • note K x.val u m) = c • t:= castScale (terrain Y H (Y.ir i) s) c _
    unfold sharp Journey.listen Journey.compass; rw [Pi.smul_apply,he,mark_smul,mul_div_assoc]
 have e(x:Purse S):= Q.together s (Q₀ x.val) (show TestFamily K true (Q₀ x.val) from ⟨⟨S,v.harmony ▸ note_t K u x.property v.tines⟩,fun _=>by contradiction⟩)
 have t(n):= tendsto_nhds_unique ((e (hue S x c)).inner n) (((e x).inner n).const_mul c|>.congr' (Eventually.of_forall fun i=> (p n _).symm))
 exact ⟨p,t,tendsto_nhds_unique ((e (hue S x c)).periods) (((e x).periods.const_mul c).congr' (Eventually.of_forall fun i=> (t _).symm))⟩
where
 castScale {m n:Side}(h:m=n)(a:ℂ)(f:Mark m): (show Mark n from h▸ (a • f)) = a • (show Mark n from h ▸ f):=by subst m; rfl
local notation "T"=> plaza (Λ:=Λ) S
local notation "cap"=> price Λ l S
local notation "Φ"=> sharp Y H s
-- public version relative to this L1 norm
lemma relatives :
    (∀ᶠ n:ℕ in atTop, ∀ δ:ℝ, 0<δ→∀ᶠ k':ℕ in atTop,∀ f:PairsC→ℂ, Coeff true S f→
      ‖Φ n (k k') (Q₀ f) - I s (Q₀ f) n‖ ≤ δ*cap f) ∧
    (∀ δ:ℝ,0<δ→∀ᶠ r:ℕ in atTop,∀ f:PairsC→ℂ,Coeff true S f→
      ‖I s (Q₀ f) (i r)- E s (Q₀ f)‖ ≤ δ*cap f ∧ ∀ m:ℕ, legacy Y (i r) (k m)→
      ‖Φ (i r) (k m) (Q₀ f) - E s (Q₀ f)‖ ≤ δ*cap f):=by
 let p:= fleece Y H Q S s u v
 let c₀ (x:Purse S):ℝ:= cap x.val
 have ht(a b:Purse S→ℂ)(z:∀ x y, a (hue S x y)= y*a x)(t:∀ x y,b (hue S x y)= y*b x)(δ:ℝ)(g:∀ x∈ Tower Λ l S,dist (a x) (b x)<δ):∀j,dist (a j) (b j)≤ δ*c₀ j:=by
    simp_rw [dist_eq_norm] at *; exact Satin.pool (fun x=>a x-b x) c₀ (fun i=>touch_pos ..) (fun a₀ r w=>⟨hue S a₀ r,(hues Y H Q S s u v a₀ r).1.trans (by rw [Complex.norm_real,Real.norm_of_nonneg w]),by rw [z,t,←mul_sub,norm_mul,Complex.norm_real,Real.norm_of_nonneg w]⟩) _ g
 constructor
 · filter_upwards [p.spring] with n q; intro δ y; filter_upwards [q δ y] with k q; intro f g
   have h0:= ht (fun x=>Φ n _ (Q₀ x.val)) (fun x=> I s (Q₀ x.val) n)
     (fun x y=> (hues Y H Q S s u v x y).2.1 ..) (fun x y=> (hues Y H Q S s u v x y).2.2.1 ..) _ q ⟨f,g⟩
   simpa only [dist_eq_norm] using h0
 intro δ y; filter_upwards [p.spectrum _ y,p.public_ _ y] with r z t
 intro f g; let F(x:Purse S):= E s (Q₀ x.val); have he(x y): F (hue S x y)= y* F x:= (hues Y H Q S s u v x y).2.2.2
 refine ⟨?_,fun j a=>?_⟩
 · have h:= ht (fun x=> I s (Q₀ x.val) (i r)) F (fun x y=> (hues Y H Q S s u v x y).2.2.1 ..) he _ z ⟨f,g⟩
   simpa only [dist_eq_norm] using h
 have h:= ht (fun x=>Φ (i r) (k j) (Q₀ x.val)) F (fun x y=> (hues Y H Q S s u v x y).2.1 ..) he _ (fun x y=> t x y j a) ⟨f,g⟩
 simpa only [dist_eq_norm] using h
end YM.CF.Buffered.Afterglow.Satin
#print axioms YM.CF.Buffered.Afterglow.Satin.relatives
