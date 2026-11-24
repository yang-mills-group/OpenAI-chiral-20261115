import YM.SU5.FiniteGaugeData.Chrono.Method
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
variable {v u:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
namespace Chrono
open Nacre Heat Charm Playlist Show
variable (R:Universal Y h u v I E)(L:Rolled Y h u v J P)(a j:Axis)
local notation "η"=> reserve Λ l
variable (A:Repertory Y h R L a) (x:Decko Y h a)(w:Vect Y h a 0)
local notation "G" i:max=> store Y h i R L a A
local notation "V"=> Vect Y h a 0
local notation "H"=> A.space
variable (c:StripS)(y: Decko Y h a)(ε:ℝ)
open scoped NNReal ENNReal
local notation "G'"=> tempo_aux Y h R L a A
section
variable (p:Locator (tent Y h) (browser Y h s a c x y) S)
local notation "B"=>browser Y h s a c x y
local notation "C"=> ‖reading Kₜ S (B) p‖
-- paid on all phase-critical supports exactly seeing the signed functional (not a free / eventually numeric ledger) enough for these new probes. 
structure Rewards : Prop where
 age:Roomy S (side Y (u i) s)
 admitted (j:ℕ): AtSupport false (region S (side Y j s)) (sold Y h s j (browser Y h s a c x y).val)
 coat (j:ℕ) (z:Fields (side Y j s)): ‖(sold Y h s j (browser Y h s a c x y).val) z‖ ≤ duration S * ‖reading (tent Y h) S (browser Y h s a c x y) p‖
 period: ‖urn Y h S s (u i) R -singer Y h S s R‖ ≤ ε/(‖reading (tent Y h) S (browser Y h s a c x y) p‖+1)
 uv : ∀ᶠ k:ℕ in atTop, MarkGate Y s (u i) (v k) ∧ ‖mkForm Y h S s (u i) (v k)- urn Y h S s (u i) R‖ ≤ ε/(C+1)
 joint(k:ℕ)(q:legacy Y (u i) (v k)): MarkGate Y s (u i) (v k) ∧ ‖mkForm Y h S s (u i) (v k)- singer Y h S s R‖ ≤ ε/(C+1)
include R p
lemma rewarded (b:0<ε): ∀ᶠ i:ℕ in atTop, Rewards Y h S s i R a x c y ε p:=by
 have he:0< ε/(C+1):= by positivity
 filter_upwards [boutique_P Y h S s R _ he,R.pick.grow_i.tendsto_atTop.eventually (boutique_urn Y h S s R), ((momentum Y s).comp R.pick.grow_i.tendsto_atTop).eventually (roomy_sides S Kₜ)] with i up i' w -- binder u collision.I shifts during t
 refine ⟨(by rw [show side Y _ s=(Kₜ).c _ from (terrain Y h _ _).symm]; exact w),fun i=> sold_affair Y h _ _ i p,fun j y=>?_, up.1,?_,up.2⟩
 · let Z:=reading _ _ _ p; have hz : composeQ Kₜ S Z=(B).val:= reading_p _ _ _ p; rw [← hz]; exact sold_q_bound ..
 filter_upwards [gate_often Y h s (u i) R, (Metric.tendsto_nhds (α:=Catalog S →L[ℂ] ℂ)).mp i' _ he] with k uQ vc; exact ⟨uQ,(vc.le).trans_eq' (dist_eq_norm (mkForm Y h S s (u i) (v k)) _) ⟩ -- dims implicit ?
variable (Z':Rewards Y h S s i R a x c y ε p)
include Z'
local notation "I'"=> I s (browser Y h s a c x y).val
omit R p Z' in
private lemma owed (ε:ℝ)(b:0≤ε) {A:Type*}[NormedAddCommGroup A][NormedSpace ℂ A](x:A) (P Q:A→L[ℂ] ℂ) (h:‖P-Q‖ ≤ ε/(‖x‖+1)): ‖P x-Q x‖ ≤ ε:= ((P-Q).le_opNorm x).trans ((mul_le_mul h (by linarith : ‖x‖≤ ‖x‖+1) (norm_nonneg _) (by positivity)).trans_eq (div_mul_cancel₀ ε (by have he:= norm_nonneg x; linarith : ‖x‖+1 ≠ 0)))
lemma totals (b:0≤ε): ‖(I s (browser Y h s a c x y).val (u i))- E s (browser Y h s a c x y).val‖ ≤ ε∧
    (∀ᶠ k in atTop, ‖sharp Y h s (u i) (v k) (browser Y h s a c x y).val- I s (browser Y h s a c x y).val (u i)‖≤ ε) ∧
    (∀ k, legacy Y (u i) (v k)→ ‖sharp Y h s (u i) (v k) (browser Y h s a c x y).val- E s (browser Y h s a c x y).val‖≤ε):=by
 let T':=reading _ _ _ p; let P:=singer Y h S s R; let Q:=urn Y h S s (u i) R; have bt:P T'=E s (B).val:=by unfold P; rw [singer_eval,reading_p] -- T'
 have gt:Q T'=I s (B).val (u i):= by unfold Q; rw [urn_eval,reading_p]
 have qt(k:ℕ)(e:MarkGate Y s (u i) (v k)): mkForm Y h S s (u i) (v k) T'=sharp Y h s (u i) (v k) (B).val:=by rw [mk_read _ _ _ _ _ _ e, reading_p]
 rw [← bt,←gt]; refine ⟨owed ε b _ Q P Z'.period,Z'.uv.mono (fun k v=>?_),fun k h₁=>?_⟩
 · rw [← qt k v.1]; exact owed ε b _ _ _ v.2
 obtain ⟨e,h⟩:= Z'.joint k h₁; rw [← qt k e]; exact owed ε b _ _ _ h
end
variable (T':ℝ)(P':ℝ≥0)
abbrev latticeFieldEstimates (T':ℝ)(P':ℝ≥0):= (reachH (tempo_aux Y h R L a A) T' P')
lemma sensor (z:A.space): latticeFieldEstimates Y h R L a A T' P' z= (realAxis Y h R L a A).translation T' (rail Y h R L a A P' z):=rfl
-- these are `store` data on a common level, any set of mixed polynomial vectors is just such data (collapse with `Arrive`). 
theorem wisdom (F:Finset (Decko Y h a))(r:0<ε): ∃ c:StripS, ‖team (tempo_aux Y h R L a A) c‖≤1+ε ∧
    (∀ x∈F, dist (store Y h s R L a A (bat Y h s a c x)) ((latticeFieldEstimates Y h R L a A T' P') ((G s) x))< ε) ∧
    (∀ f:Decko Y h a,∀ x∈F, dist (E s (browser Y h s a c f x).val)
      (inner ℂ ((G s) f) (((realAxis Y h R L a A).translation T') (rail Y h R L a A P' ((G s) x)))) ≤ ‖(G s) f‖*ε) ∧
    (∀ f x:Decko Y h a,∃ S:Finset Cover,∃ p: Locator (tent Y h) (browser Y h s a c f x) S,∀ᶠ i:ℕ in atTop, Rewards Y h S s i R a f c x ε p) := by
 classical
 obtain ⟨c,hp,t⟩:= reachH_seed (tempo_aux Y h R L a A) (F.image (store Y h s R L a A)) T' P' ε r
 refine ⟨c,hp,fun i v=>?_,fun f i e=> ?_,fun i f=>?_⟩
 · rw [gather_B]; exact t _ (mem_image_of_mem (store Y h s R L a A) v)
 · let v:=store Y h s R L a A i; let q:=t _ (mem_image_of_mem (store Y h s R L a A) e); let A':= latticeFieldEstimates Y h R L a A T' P'; let C:= team (tempo_aux Y h R L a A) c
   rw [browser_e Y h s R L a A f i c, dist_eq_norm,← inner_sub_right,← sensor]; exact (norm_inner_le_norm ..).trans (mul_le_mul_of_nonneg_left (show ‖C v-A' v‖≤ε by rw [←dist_eq_norm]; exact q.le) (norm_nonneg _))
 obtain ⟨b,p⟩:= testimony Kₜ (browser Y h s a c i f); exact ⟨_,p,rewarded Y h b s R a i c f ε p r⟩
-- for sequence choose sufficiently late periods AFTER ε, S via (rewarded...). charges in this catalog. 
theorem ladder (x y:ℕ→Decko Y h a) (S:ℕ→Finset Cover)(s:ℕ→ℕ)(c:ℕ→StripS)(p:ℕ→ℝ)(q:∀ i,0<p i)(v:∀ i,Locator (tent Y h) (browser Y h (s i) a (c i) (x i) (y i)) (S i)): ∃ w:ℕ→ℕ,StrictMono w ∧ ∀ i,∀ j, w i ≤ j → ∀ k≤ i, Rewards Y h (S k) (s k) j R a (x k) (c k) (y k) (p i) (v k):=by
 have hv(i):∃ n, ∀ j, n≤j → ∀ k ≤ i, Rewards Y h (S k) (s k) j R a (x k) (c k) (y k) (p i) (v k):=by
    apply eventually_atTop.mp; simp_rw [show ∀ k:ℕ,k ≤ i ↔ k ∈ Finset.Iic i from fun k=>mem_Iic.symm]; exact (eventually_all_finset _).mpr fun k _=>rewarded Y h _ _ R _ _ _ _ (p i) (v k) (q i)
 choose n h using hv
 let f:= Nat.rec (motive:=fun _=>ℕ) (n 0) fun i t=> n (i+1)+t+1; refine ⟨f,strictMono_nat_of_lt_succ (fun i=> by change f i < n (i+1)+f i+1; omega),fun i j v=>?_⟩; cases i with
 | zero=> exact h _ j v
 | succ k=> exact h (k+1) j (le_trans (by change n (k+1)≤ n (k+1)+f k+1; omega) v)
#print axioms wisdom
end Chrono
end YM.CF.Buffered.Afterglow.Hierarchy
