import YM.SU5.FiniteGaugeData.Tower.StationMaster
-- Strengthened op pricing. Cp8.a. Follow PowerCap/EndTrain/StationRide, but get the NEW constant for actual mosaic pricing.
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5900
set_option maxHeartbeats 390000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
local notation "L₀"=>Λ.R.L.val
local notation "m" n:max s:max=>momentm Y n s
local notation "T₀" n:max s:max=> Journey.side Y n s
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}{a b:ℕ→ℕ}(Q:Coherent (i:=i) (k:=k) (E:=E) Y H D a b)
variable (j:Axis){w:ℕ}{f:Family (tent Y H)}{S:Finset Cover}(t:InTest (tent Y H) true S false f)(hB:Between (tent Y H) j 0 (ruler Λ.block*w) S)
local notation "Z" u:max n:max k:max=> train Y H s u n k S f
local notation "π" r:max=>i (a r)
local notation "ζ" r:max=> k (b r)
local notation "W" t:max=> volumeAround Λ l t S
local notation "uM" t:max=> (L₀^t*w)
include Q hB V
-- uniform in f!
lemma estate_drop (r:ℕ): ∀ᶠ e:ℕ in atTop, ∀ F, InTest K true S false F → ∀ (n:ℕ)(v:ℤ), 2*(ruler Λ.block*w*n) ≤ (((T₀ (π e) s).val:ℕ):ℤ)→
 sharp Y H (s+r) (π e) (ζ e) (banner j (uM r) ((L₀:ℤ)^r*v) n (train Y H s r (π e) (ζ e) S F))=sharp Y H s (π e) (ζ e) (banner j w v n F):=by
 induction r with
 | zero=> exact Eventually.of_forall fun n g t v p' k=>by simp [train]
 | succ r ih=>
    have hM:Tendsto (fun r=>π r) atTop atTop:= V.pick.grow_i.tendsto_atTop.comp Q.growsA.tendsto_atTop
    let X:=W (r+1); let S0:=W r
    let A:=s+r
    have ht:∀ᶠ e in atTop,Tivoli X ((K).c (m (π e) (A+1))) :=hM.eventually (turning Y H (A+1) X)
    filter_upwards [ih,Q.finance (s+r+1),ht] with e he ae hh f₁ t₁ n q v
    let M':ℕ:=π e; let k':ℕ:= ζ e
    let F:=train Y H s r M' k' S f₁
    have hs:InTest K true S0 false F := prepared_train Y H s S r _ _ t₁
    have Hs: Between K j 0 (ruler Λ.block * ((L₀:ℤ)^r*w)) S0 :=by rw [mul_left_comm]; exact expands_shape Y H hB r
    have he₁:legalAt Y A M' k':=⟨ae.depth,ae.enters⟩
    let F':=block Y H A M' k' S0 F
    have hx:Delivered Y H A M' k' F F':=⟨aux_test hs,aux_test (booked ..),reserved Y H A S0 M' k' he₁ hs hh⟩
    let U:ℤ:= (L₀:ℤ)^r
    have hy:2*(ruler Λ.block * (U*w) * n) ≤ (((T₀ M' A).val:ℕ):ℤ):=by
       unfold A; rw [refine_side,Nat.cast_mul,Nat.cast_pow]; have ht:0≤U:=by positivity
       rw [show 2*(ruler Λ.block *(U*w)*n)=U*(2*(ruler Λ.block*w*n)) from by ring]; exact mul_le_mul_of_nonneg_left v ht
    have hp:=delivering Y H A M' k' he₁ (bulk_lift Y H A M' k' j he₁ hx n ((L₀:ℤ)^r*q) hs Hs (by positivity) hy)
    rw [← he f₁ t₁ n q v,←Nat.add_assoc s r, train_step]
    convert hp using 2 <;> push_cast <;> rw [pow_succ'] <;> congr 1 <;> ring
variable (R:ℕ→Family (tent Y H))(U: BQueue S R f)
include V Q U
omit hB
lemma loftQ (r:ℕ):BQueue (W r) (fun e=>train Y H s r (π e) (ζ e) S (R e)) (stream Y H D s r f):=by
 obtain ⟨C,hv,v⟩:= fares Y H s Q S r; obtain ⟨B,d,hx,e⟩:=U.bdd
 let L:= stream Y H D s r
 have sub(x y:Family K)(t:InTest K true S false x)(u:InTest K true S false y):stream Y H D s r (x-y)=L x-L y:=by
    unfold L; clear L hv C v
    induction r with | zero=> rfl | succ r h=>
       rw [stream_step,stream_step,stream_step,h, D_sub Y H Q (aux_test (proceeds Y H Q.circuit s r t).1) (aux_test (proceeds Y H Q.circuit s r u).1)]
 refine ⟨fun i=>prepared_train Y H s S r _ _ (U.whereTo i),(proceeds Y H Q.circuit s r U.landing).1, ⟨C*B,mul_pos hv d, ((v 1 zero_lt_one).exists.choose_spec _ U.landing B hx).1, ?_⟩, fun p t =>?_⟩
 · filter_upwards [e,v 1 zero_lt_one] with i q b using (b _ (U.whereTo i) B q).2.1
 let k:=p/(B+C); have hk:0<k:=div_pos t (add_pos d hv)
 filter_upwards [e,v k hk,U.saved k hk] with i z q y
 have h:= (q _ (U.whereTo i) B z).2.2.1
 have he:pay (L (R i)-L f) (C*k):=by rw [←sub (R i) f (U.whereTo i) U.landing]; exact (q _ (InTest.subOp (U.whereTo i) U.landing) k y).1
 intro n x
 apply (norm_sub_le_norm_sub_add_norm_sub _ (stream Y H D s r (R i) n x) (stream Y H D s r f n x)).trans
 refine (add_le_add (h n x) (he n x)).trans_eq ?_
 change k* B + C*k= p
 have ht:k*(B+C)=p:=div_mul_cancel₀ _ (add_pos d hv).ne'; nlinarith only [ht]
-- high bill
local notation "b₀"=>ruler Λ.block
variable (C:ℝ)
-- W-multiple. Applicant duration positive, constants may small; pay +1 for transfer.
omit Q V U
structure MastC : Prop where
 one : 0 < C
 consumes : ∀ᶠ e in atTop, ∀ n : ℕ, 0<n → 2*(b₀*w*n) ≤ (((T₀ (π e) s).val:ℕ):ℤ)→(((T₀ (π e) s).val:ℕ):ℤ) ≤ (4*(b₀*w*n))→
   ∀v:ℤ, ‖hot Y H s (π e) (ζ e) (banner j w (↑w*v) n (R e))‖ ≤ C^(2*n)
include hB Q V U
variable (hw:0 < w)(Qt : Clipped Y H (i∘a) (k∘b))(M:MastC (i:=i) (k:=k) (a:=a) (b:=b) Y H s j (w:=w) R C)
include M hw Qt
open Analysis
lemma sprinkle(r:ℕ):
 ∀ᶠ e:ℕ in atTop,∀ n:ℕ, 0<n→2*(b₀*w*n) ≤ (((T₀ (π e) s).val:ℕ):ℤ)→(((T₀ (π e) s).val:ℕ):ℤ) ≤ (4*(b₀*w*n))→ ∀ v:ℤ,
 ‖hot Y H (s+r) (π e) (ζ e) (banner j (uM r) ((uM r)*v) n (train Y H s r (π e) (ζ e) S (R e)))‖ ≤ (C+3)^(2*n):=by
 obtain ⟨x,hx,_,g⟩:= U.bdd
 obtain ⟨A,p₀,Tp⟩:=fares Y H s Q S r
 have he:= mul_nonneg p₀.le hx.le
 filter_upwards [M.consumes, Tp 1 zero_lt_one,plate Y H V Q Qt s x hx.le, plate Y H V Q Qt (s+r) (A*x) he,estate_drop Y H V s Q j hB r,g] with i z a b₁ b₂ g y n Hn P E' v
 let c' := (T₀ (π i) s).val
 let F := banner j (uM r) ((uM r)*v) n (train Y H s r (π i) (ζ i) S (R i)); let f' := banner j w ((w:ℤ)*v) n (R i)
 have hr: 1≤ b₀*w:= by have hv:0<(w:ℤ):=by exact_mod_cast hw
                       have hf:=ruler_gene Λ.block; nlinarith
 have hu₁:n ≤ c':=by
    change _ ≤ (c':ℤ) at P; zify; nlinarith [mul_le_mul_of_nonneg_right hr (show 0≤(n:ℤ) by positivity)]
 have hu₂:n ≤ (T₀ (π i) (s+r)).val :=hu₁.trans (by unfold c'; rw [refine_side Y]; exact Nat.le_mul_of_pos_left _ (pow_pos Λ.R.L.property r))
 let t:=U.whereTo i; have hp: pay (R i) x:=y
 obtain ⟨c₀,k₁⟩:= main_bill j w ((w:ℤ)*v) n (aux_test t) hp
 obtain ⟨g₀,k₂⟩:=main_bill j (uM r) ((uM r)*v) n (aux_test (prepared_train Y H s S r (π i) (ζ i) t)) ((a (R i) t _ hp).2.1)
 let G:= hot Y H s (π i) (ζ i) f'
 let g':=hot Y H (s+r) (π i) (ζ i) F
 have hb:=b₁ _ hu₁ _ c₀ k₁; have hB':=b₂ _ hu₂ _ g₀ k₂
 have hi: ‖g'‖ ≤ ‖G‖+1+1:=by
    have hz: sharp Y H (s+r) (π i) (ζ i) F=sharp Y H s (π i) (ζ i) f':=by have hh:=g (R i) t n ((w:ℤ)*v) P; unfold F; rw [mul_assoc ((↑L₀:ℤ)^r)]; exact hh
    have h₁:= norm_sub_norm_le (hot Y H (s+r) (π i) (ζ i) F) (sharp Y H (s+r) (π i) (ζ i) F)
    have h₂:= norm_sub_norm_le (sharp Y H s (π i) (ζ i) f') G
    rw [norm_sub_rev] at h₁
    have hg:=h₁.trans hB'; rw [hz] at hg
    have hh:=h₂.trans hb; change _-‖G‖ ≤1 at hh; unfold g'; linarith only [hg,hh]
 have ht:‖G‖ ≤ C^(2*n):= z _ Hn P E' v
 have hc : 0<C:= M.one
 exact hi.trans (by
    have A(k:ℕ):C^(k+1)+2 ≤ (C+3)^(k+1):= by induction k with
       | zero=> norm_num
       | succ k h=> rw [pow_succ C (k+1),pow_succ (C+3) (k+1)]; nlinarith only [h,mul_le_mul_of_nonneg_right h hc.le,hc,pow_nonneg hc.le (k+1)]
    have Y:= A (2*n-1); rw [show 2*n-1+1=2*n by omega] at Y; linarith)
end YM.CF.Buffered.Afterglow.Tower.SlabMark
