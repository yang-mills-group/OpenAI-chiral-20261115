import YM.SU5.FiniteGaugeData.KernelP.Fort
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
set_option quotPrecheck false
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
local notation "Kₜ"=> tent Y h
local notation "N₁" i:max s:max=> side Y i s
local notation "Wₐ" i:max s:max => (Y.voyage i).CapeT s
local notation "D₀"=> aliasLaw Λ
local notation "D₁"=> distanceLaw l
local notation "L₁"=> Λ.R.L
local notation "C₀"=> (VolumeCape.Dream.plot l).C
local notation "Xᵣ" i:max k:max=> (Y.voyage i).X (Y.uv k)
local notation "Tᵣ" i:max k:max s:max=> ((Y.voyage i).X (Y.uv k)).gram s
variable (S T: Finset Cover)(s i k:ℕ)
open Nacre Heat Charm Chrono SalonG Journey Hills Playlist Show
namespace KernelP
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
variable (W':Universal Y h u v I E)(R:Rolled Y h u v J P)(A:∀ a:Axis,Repertory Y h W' R a)
variable {Φ:ℕ→ Charm.W (tent Y h)→ₗ[ℂ]ℂ}(S':Sphere Y h W' R A Φ)
variable (a:Axis)(z:ℤ)(d n:ℕ)
variable (p:Actors Y h a W' R (A a))(α:p.val.X)(C ε:ℝ) (y:Decko Y h a)
local notation "F"=> Camera Y h a W' R (A a)
local notation "d'"=> energyS Λ d n
local notation "W₁"=> seriesQ Λ l S n
local notation "B" S:max=> Catalog S
local notation "T'"=> hour Kₜ T a d'
local notation "S₁"=> refract a 0 T
local notation "Z" s:max=> issueH Y h s a W' R (A a) p α
-- cap usage at ROOM: lens f.Adv (W.Elected sharp `Pension`)
variable (t:Locator (tent Y h) y.val T)
abbrev volumeP := refract a 0 T∪(seriesQ Λ l S n ∪ hour Kₜ T a (energyS Λ d n))
local notation "V"=> volumeP Y h S T a d n
abbrev stampH (T₀:Charm.W (tent Y h)):Charm.W (tent Y h):= helve Kₜ a y.val (Swing Kₜ a (energyS Λ d n) T₀ y.val)
-- support assembled.Quasi.
def portP : Catalog (seriesQ Λ l S n)→L[ℂ] Catalog (volumeP Y h S T a d n):= (timesQ Kₜ subset_union_left (D:=V) subset_union_right (reading Kₜ S₁ (fire Kₜ a 0 y.val) (locate_cold Kₜ T a 0 t))).comp ((timesQ Kₜ (D:=W₁ ∪ T') subset_union_left subset_union_right).flip (reading Kₜ T' (clockW Kₜ a (energyS Λ d n) y.val) (loc_tic _ T _ _ t)))
lemma portPs (g: Catalog (seriesQ Λ l S n))(f:W (tent Y h))(v:composeQ Kₜ (seriesQ Λ l S n) g=f.val):
    composeQ Kₜ (V) (portP Y h S T a d n y t g)= (stampH Y h a d n y f).val:=by
 let U':= (timesQ Kₜ (D:=W₁∪T') subset_union_left subset_union_right).flip; let x:= reading Kₜ T' (clockW Kₜ a d' y.val) (loc_tic Kₜ T _ _ t); unfold portP; rw [ContinuousLinearMap.comp_apply,timesQ_id,ContinuousLinearMap.flip_apply,timesQ_id,reading_p,reading_p,v]; rfl -- transparency?
variable (f:W (tent Y h)) (e:Locator (tent Y h) f S)
abbrev risingH := stampH Y h a d n y (Passenger Y h S s i k n f e)
local notation "R1" i:max k:max=> risingH Y h S s i k a d n y f e
lemma travel_q : composeQ Kₜ (V) (portP Y h S T a d n y t (Pension Y h S s i k n (reading Kₜ S f e)))= (risingH Y h S s i k a d n y f e).val:= portPs Y h S T a d n y t _ (Passenger Y h S s i k n f e) rfl
include t in
lemma land_q : Locator Kₜ (risingH Y h S s i k a d n y f e) (volumeP Y h S T a d n):=by unfold Locator; rw [← travel_q Y h S T s i k a d n y t]; exact compose_t ..
include W' R in
lemma resolveW (p:Plan Y h a d f)(v:0<d):
    E (s+n) (composeQ Kₜ (V) (portP Y h S T a d n y t (streamQ s S P n (reading Kₜ S f e))))=
     inner ℂ (store Y h (s+n) W' R a (A a) y) ((Wedge Y h s a d W' R (A a) p v) (store Y h (s+n) W' R a (A a) y)):=by
 rw [wedge_plus,lawStore,appointed_val]; exact congrArg (E _) (portPs Y h S T a d n y t _ (ascended Y h s W' R n f) (ascend_cert ..|>.symm))
def stepInk : Catalog S→L[ℂ] ℂ := (mkForm Y h (V) (s+n) i k).comp ((portP Y h S T a d n y t).comp (Pension Y h S s i k n))
def farewell : Catalog S→L[ℂ] ℂ := (singer Y h (V) (s+n) W').comp ((portP Y h S T a d n y t).comp (streamQ s S P n))
include W' R t
omit R t
private lemma stageBuy (p:ℕ→ℕ)(e:eligiblePath Y u v p) : Tendsto (fun i=>mkForm Y h S s (u i) (v (p i))) atTop (𝓝 (singer Y h S s W')):= by
 refine (Metric.tendsto_nhds («α»:= Catalog S→L[ℂ]ℂ)).mpr fun ε he=>?_
 filter_upwards [e,boutique_P Y h S s W' (ε/2) (by positivity)] with i hy q; rw [dist_eq_norm (mkForm Y h S s (u i) (v (p i)))]; exact ((q.2 (p i) hy).2).trans_lt (by linarith)
omit W'
private lemma pstage {U U' U'':Type}[NormedAddCommGroup U][NormedSpace ℂ U][NormedAddCommGroup U'][NormedSpace ℂ U'][NormedAddCommGroup U''][NormedSpace ℂ U'']
    (A:U' →L[ℂ] U'')(P Q:ℕ→ℕ→ U→L[ℂ] U')(L:ℕ→ℕ→U''→L[ℂ]ℂ)(F':U→L[ℂ]U')(G:U''→L[ℂ]ℂ)
    (u v:ℕ→ℕ)(t:StrictMono v)(p:∀ k:ℕ→ℕ,eligiblePath Y u v k→ Tendsto (fun i=>P (u i) (v (k i))) atTop (𝓝 F'))(e:∀ k:ℕ→ℕ,eligiblePath Y u v k→ Tendsto (fun i=>L (u i) (v (k i))) atTop (𝓝 G))(q:0<ε):
     ∀ᶠ i in atTop,∀ k, legacy Y (u i) (v k)→ ‖(L (u i) (v k)).comp (A.comp (P (u i) (v k))) - G.comp (A.comp F')‖≤ε:= by
    let S':=fun i k=>(L i k).comp (A.comp (P i k)); let O:= G.comp (A.comp F')
    have he(k:ℕ→ℕ)(c:eligiblePath Y u v k): Tendsto (fun i=>S' (u i) (v (k i))) atTop (𝓝 O):= tendSL (e k c) (tendSL (tendsto_const_nhds (x:=A)) (p k c));
    exact (path_budget (T:=U→L[ℂ]ℂ) (z:=O) (A:=S') Y t he ε q).mono fun i h k p=> (h k p).le.trans_eq' (dist_eq_norm _ O)
include W' R t
lemma income_linear (v':0<ε):∀ᶠ i in atTop, ∀ k,legacy Y (u i) (v k)→ ‖stepInk Y h S T s (u i) (v k) a d n y t-farewell (P:=P) Y h S T s W' a d n y t‖≤ ε:=by
 unfold stepInk farewell; exact pstage Y ε (portP Y h S T a d n y t) (fun i k=> Pension Y h S s i k n) (fun i k=> Pension Y h S s i k n) (mkForm Y h V (s+n)) _ _ _ _ W'.pick.grow_k (streamG Y h S s n W' R) (stageBuy Y h V (s+n) W') v'
-- uniform support budgets explicitly on controls. Also requiring `projectR` guaranteed at legacy. Native Ω recipe. Charge norms.
variable (w: Studio a 0 (yard (tent Y h) d) (reserve Λ l) S) (v₁:0<d)
local notation "A1"=> (A a)
local notation "y₁"=> store Y h (s+n) W' R a (A a) y
abbrev costX : ℝ := ‖portP Y h S T a d n y t‖*(bridgesK Y h S s n*C)
include w v₁
lemma studioRight (z:0≤C)(e:0<ε): ∀ᶠ r in atTop,∀ k,legacy Y (u r) (v k)→ projectR Y S s (u r) (v k) n ∧ MarkGate Y (s+n) (u r) (v k) ∧
    ∀ (f:W (tent Y h))(e:Locator (tent Y h) f S), ‖reading Kₜ S f e‖≤ C→
    let g:= risingH Y h S s (u r) (v k) a d n y f e
    dist (sharp Y h (s+n) (u r) (v k) g.val) (inner ℂ (y₁) (Wedge Y h s a d W' R (A a) (f:=f) ⟨S,w,e⟩ v₁ (y₁))) ≤ ε∧ ∃ p:Locator Kₜ g (volumeP Y h S T a d n), ‖reading Kₜ _ g p‖≤ costX Y h S T s a d n C y t := by
 let Z':= ε/(C+1); have hC : C < C+1 := by linarith
 have h':0 < Z':=div_pos e (z.trans_lt hC)
 filter_upwards [income_linear Y h S T s W' R a d n Z' y t h', streams Y h S s n W' R Z' h', boutique_P Y h (V) (s+n) W' ε e] with i p q g k v'
 refine ⟨(q _ v').1,(g.2 _ v').1,?_⟩; rintro X t₁ ht Z₁; let v₀:= u i; let i':=v k; let x:= reading Kₜ S X t₁; specialize p k v'; have he:=le_trans (((stepInk Y h S T s v₀ i' a d n y t)-(farewell Y h S T s W' (P:=P) a d n y t)).le_of_opNorm_le p x) ((mul_le_mul_of_nonneg_left (ht.trans hC.le) h'.le).trans_eq (div_mul_cancel₀ _ (z.trans_lt hC).ne'))
 have hp:composeQ Kₜ (V) _= Z₁.val:=travel_q Y h S T s v₀ i' a d n y t X t₁
 let u':= land_q Y h S T s v₀ i' a d n y t X t₁
 constructor
 · unfold Z₁; rw [dist_eq_norm, ←hp, ←resolveW Y h S T s W' R A a d n y t X t₁,← singer_eval Y h (V) (s+n) W', ← mk_read Y h (V) (s+n) _ _ (g.2 _ v').1]; exact he
 refine ⟨u',?_⟩; rw [show reading Kₜ (V) Z₁ u'= _ from compose_inj (V) Kₜ ((reading_p Kₜ (V) Z₁ u').trans hp.symm)]; exact ((portP Y h S T a d n y t).le_opNorm _).trans (mul_le_mul_of_nonneg_left ((ContinuousLinearMap.le_of_opNorm_le ((Pension Y h S s v₀ i' n)) (bridge_width ..) x).trans (mul_le_mul_of_nonneg_left ht (bridgesK_nn ..))) (norm_nonneg (portP Y h S T a d n y t)))
#print axioms studioRight
end KernelP
end YM.CF.Buffered.Afterglow.Hierarchy
