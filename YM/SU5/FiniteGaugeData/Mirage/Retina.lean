import YM.SU5.FiniteGaugeData.Brique.Sequoia
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 380000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Quest
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Heat Brique Window.Brique Journey Py Py.Rate LocalLimit Preparation FullBill Steam Vale
namespace Chaperone
section
variable {n B:Side} {K:Calibration}
local notation "N"=> K.c n
private lemma funnel (i:Axis)(k:ℕ){d:ℕ}(h:2^k*(d+addgap K) ≤ (N).val){S:Support (More N)}(w:rest K n S i d)(f:Mark (K.c n)) : ∃ T:Support (More N),∃ y:Mark (K.c n), Mirror K.B K.ℓ (K.c n) S f T y (2^k) ∧ ∀ j:Axis,j≠i→ ∀ d,rest K n S j d→ rest K n T j d:=by
 induction k generalizing d S f with
 | zero=> exact ⟨_,_,by simpa using Mirror.self (B:=K.B) (f:=f) (S:=S) (u:=K.ℓ),fun _ _ _ h=>h⟩
 | succ k ih=>
    obtain ⟨z,u,v,e⟩:= twice i w ((Nat.le_mul_of_pos_left _ (pow_pos two_pos _)).trans h)
    obtain ⟨A,B,q,t⟩:= ih (d:=2*d+addgap K) (by rw [pow_succ] at h; exact h.trans' (le_of_eq (by ring))) v (reflMark i (Heat.gaugeShift K.B z) f * f)
    exact ⟨_,_, pow_succ' 2 k ▸ Mirror.trans (Mirror.grow _ z u) q, fun j p d h=> t j p d (e j p d h)⟩
lemma plans (k:Axis→ℕ){d:Axis→ℕ}(h:∀ i:Axis,2^(k i)*(d i+addgap K)≤(N).val){S:Support (More N)}(w:∀ i,rest K n S i (d i))(f:Mark (K.c n)) : ∃ T y, Mirror K.B K.ℓ (K.c n) S f T y (∏ i:Axis,2^(k i)):=by
 have hf {S':Support (More N)}(F:Finset Axis)(w:∀ i∈ F, rest K n S' i (d i))(f:Mark (K.c n)): ∃ T y, Mirror K.B K.ℓ (K.c n) S' f T y (∏ i∈F,2^(k i)):=by
    induction F using Finset.induction_on generalizing S' f with
    | empty=> simp only [prod_empty]; exact ⟨_,_,Mirror.self⟩
    | @insert i R v ih=> obtain ⟨T,y,p,q⟩:=funnel i (k i) (h i) (w i (mem_insert_self ..)) f; obtain ⟨U,z,u⟩:=ih (fun j hj=> q j (fun x=>v (x ▸ hj)) (d j) (w j (mem_insert_of_mem hj))) y; rw [prod_insert v]; exact ⟨U,z,p.trans u⟩
 exact hf univ (fun i _=> w i) f
lemma transfer_size {s n: Side} (d k:Axis→ℕ)(K:Calibration)(a:n=K.c s)(S:Support (More n))(h:∀ i:Axis,2^(k i)*(d i+addgap K)≤n.val)(w:∀ i:Axis, ∃ b:ℤ,∀ x∈S,Chord b (d i) (x i))(f:Mark n) : ∃ T y, Mirror K.B K.ℓ n S f T y (∏ i:Axis,2^(k i)):= by
 subst n; exact plans k h w f
end
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1 ≤ Λ.x)
variable {g:ℝ}{u v:ℕ→ℕ} {I:ℕ→Family (tent Y h)→ℕ→ℂ} {E:ℕ→Family (tent Y h)→ℂ}
set_option quotPrecheck false
variable (K:Journey.Universal Y h u v I E)(s i k:ℕ)
local notation "Kx" => tent Y h
local notation "Ω" => side Y i s
local notation "V" => storeH Λ.V
local notation "S₀" => (Y.voyage i).CapeT s
local notation "Ψ" k:max => Journey.compass Y i k s
local notation "ξ" => zen (slopeF Λ.W g) (V).C
variable {D:Axis→ℕ}{m n w:ℕ}{C c ε α θ:ℝ}
section
private lemma densL {x y:ℕ}(h:0<y)(p:y≤x):∃ k:ℕ,2^k*y≤x∧x ≤ 2* (2^k)*y:=by
  have he : x < 2^x*y:= lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.le_mul_of_pos_right _ h)
  let P(k:ℕ):= x ≤ 2*(2^k)*y
  have ht: ∃ k,P k:=⟨x,by unfold P; linarith⟩
  refine ⟨Nat.find ht,?_,Nat.find_spec ht⟩
  generalize e:Nat.find ht=k
  cases k with
  | zero=> simpa using p
  | succ k=> have h:=Nat.find_min ht (by omega : k < Nat.find ht); change ¬ x ≤ 2*2^k*y at h; rw [pow_succ']; omega
abbrev capR (K:Calibration)(D:Axis→ℕ):ℝ:= (∏ i:Axis,(4:ℕ)*(D i+addgap K):ℕ)
local notation "M" d:max=> capR Kx d
abbrev Concertina (D:Axis→ℕ)(n:Side)(S:Support (More n)):=∀ i:Axis,∃ b:ℤ,∀ x∈S,Chord b (D i) (x i)
private lemma designL (D:Axis→ℕ)(H:∀ a:Axis,D a+addgap Kx≤(side Y i s).val) {T:Support (More (side Y i s))}(U:Concertina D (side Y i s) T) :∃ n:ℕ, 0<n∧ sites (side Y i s) ≤ n*M D ∧ ∀ f:Mark (side Y i s),∃ S y, Mirror Λ.block (reserve Λ l) (side Y i s) T f S y n:=by
 have hp:∀ a:Axis,∃ k:ℕ,2^k*(D a+addgap Kx)≤ (Ω).val∧ (Ω).val ≤ 2*2^k*(D a+addgap Kx):=fun a=>densL (lt_of_lt_of_le addgap_pos (Nat.le_add_left ..)) (H a)
 choose k g e using hp; refine ⟨_,Finset.prod_pos (s:=univ) (f:=fun i:Axis=>(2:ℕ)^(k i)) (by intros; positivity),?_, fun f=> transfer_size _ k Kx (terrain Y h (Y.ir i) s).symm T g U f⟩
 let F:= Ω; let r:= More F; have hv(a:Axis): r.val≤ 2^(k a)*(4*(D a+addgap Kx)):=by change F.val*2 ≤ _; calc
      _ ≤ (2* 2^(k a)*(D a+addgap Kx))*2:=by gcongr; exact e a
      _ = _:=by ring
 have hh:= prod_le_prod (s:=univ) (f:=fun _ :Axis=>r.val) (fun i _=> Nat.zero_le _) (fun i _=> hv i)
 simp_rw [prod_mul_distrib,prod_const,card_univ,show Fintype.card Axis=4 from card_fin _] at hh; change ((r.val:ℝ)^4 ≤ _* ↑(∏ i:Axis,((4*(D i+addgap Kx)):ℕ))); rw [prod_mul_distrib,prod_const,card_univ,show Fintype.card Axis=4 from card_fin _]; exact_mod_cast hh
-- Y.thaw does NOT have period delay? still powers prices need dependent-on-period thresholds. Fine.
private lemma metered (p: Ferry Y s i k) : Journey.Metered Kx (momentm Y i s) (deltaL Y h i s) (Journey.solder Y i k p.depth s ∘ ship (terrain Y h (Y.ir i) s)) (duetCharge Y s) := by
    have he:= boxprice Y h i k p.depth s p.fire p.enters
    rw [show (Journey.solder Y i k p.depth s ∘ ship (terrain Y h (Y.ir i) s))=collector Y h i k p.depth s from funext fun x=>(congrArg (Journey.solder Y i k p.depth s) (ship_eq (terrain Y h (Y.ir i) s) x))]; exact he
omit h in
private lemma frost_delta (A:ℝ)(p:0≤A)(ε:ℝ)(e:0<ε) :∀ᶠ k in atTop, ∀ v:(Y.voyage i).kick ≤ k, ∀ x:Mark Ω, Envelope x→ (∀ i,‖x i‖ ≤ A)→ ‖(Ψ k) x-Journey.solder Y i k v s x‖ ≤ ε:=by
 have hz:0<A+1:=by linarith
 filter_upwards [Y.thaw s (ε/(A+1)) (by positivity)] with k t H x f b
 let W : Envelope (x ∘ drawn (S₀)):= mark_pay ((Y.voyage i).ownership s).paid.bill f
 exact le_trans (t i H (x ∘ drawn (S₀)) (A+1) W.meas (fun x=> le_trans (b _) (by linarith))) (div_mul_cancel₀ _ hz.ne').le
variable (B':Club Y g s)(P:Master Y s i) (g0:0≤α)(Qa:Real.exp α+1 ≤ Λ.h)(v0:0≤C)(w0:ε+tailCost (storeH Λ.V).c (storeH Λ.V).C w≤Real.exp (-α))(e0:0≤ε)(p0:0 ≤ g)
include g0 Qa v0 w0 e0 B' P K p0
-- pay on every fit brick, one period, uniform in operator chosen post Male.
private lemma earnings (H:∀ a:Axis,D a+addgap Kx≤(side Y i s).val) {T:Support (More (side Y i s))}(U:Concertina D (side Y i s) T)(e:ℝ)(ht: lighting m α C*Real.exp (ξ*M D)<e): ∀ᶠ k:ℕ in atTop, ∀ p: s ≤ Y.uv (v k), ∀ f:Mark (side Y i s), AtSupport false T f → (∀ x, ‖f x‖ ≤ C) → Crater w (tailCost (V).c (V).C w) ε (posters Y s i (v k) P p w).bleed.peg T f m false → ‖(Ψ (v k)) f‖ ≤ e:=by
 let Y₀:= lighting m α C; have hy:0≤ Y₀:= bulb m α C v0; let u:=Y₀*Real.exp (ξ*M D); have hu:0≤u:=mul_nonneg hy (Real.exp_pos _).le
 obtain ⟨v',v'x,v'h⟩:= exists_between ht; let vκ:ℕ→ℕ:= v; have hv':0≤v':=hu.trans (show u ≤ v' from v'x.le); obtain ⟨n,q,l,Tt⟩:= designL Y h s i D H U; let a:= v'^n-u^n; let t:=e-v'
 have ha:0<a:=sub_pos.mpr (pow_lt_pow_left₀ (show u<v' from v'x) hu q.ne'); have he:0<t:=sub_pos.mpr v'h; have hξ:0 ≤ ξ:= zen_pos _ _ (by unfold slopeF; positivity) ((V).posse.value.le)
 have heu : Y₀^n*Real.exp (ξ* sites Ω) ≤ u^n := by
    unfold u; rw [mul_pow,←Real.exp_nat_mul]; apply mul_le_mul_of_nonneg_left _ (pow_nonneg hy _); apply Real.exp_monotone; linarith only [mul_le_mul_of_nonneg_left l hξ]
 filter_upwards [K.pick.grow_k.tendsto_atTop.eventually (frost_delta Y s i (C^n) (pow_nonneg v0 _) a ha),K.pick.grow_k.tendsto_atTop.eventually (frost_delta Y s i C v0 t he),K.pick.pass Y h s i] with k Dp Dx wκ -- omitted implicit
 intro W f F vF Tκ
 obtain ⟨S,y,U⟩:= Tt f; let H:=Journey.solder Y i (v k) wκ.depth s
 have hvw:‖H y‖-‖(Ψ (v k)) y‖ ≤ a:=(norm_sub_norm_le ..).trans ((by rw [norm_sub_rev]; exact Dp _ _ (U.covers F).env (U.cost vF))) -- tune inferred a
 have hh: ‖H f‖ ≤ v':= by
    refine le_of_pow_le_pow_left₀ (n:=n) q.ne' hv' ?_ -- tune
    have h:= (Mirror.heat (K:=Kx) (X:=H) (terrain Y h (Y.ir i) s).symm U (metered Y h _ _ _ wκ) F); have hy : ‖Journey.compass Y i (v k) s y‖ ≤ u^n:=(glacier_cost Y s i (v k) P B' W g0 Qa vF v0 w0 e0 Tκ F wκ.depth U).trans heu
    unfold a at hvw; linarith
 have hz: ‖(Ψ (v k)) f‖-‖H f‖≤t:= (norm_sub_norm_le ..).trans (Dx wκ.depth f F.env vF); unfold t at hz; linarith
end
private lemma ship_f {a b:Side}(p:a=b)(A:Mark a)(f:∀ x:Fields b, ‖ship p A x‖≤C):∀ x:Fields a, ‖A x‖≤ C:= by subst b; exact f
private lemma onward {S: Finset Cover}(q:∀ i:Axis,∃ p:ℤ,∀ x∈ S,p≤ x i∧x i ≤ p+D i): Concertina D (side Y i s) (region S (side Y i s)):=by
 intro a; obtain ⟨p,q⟩:= q a; refine ⟨p,fun i p'=>?_⟩; obtain ⟨u,b',rfl⟩:=mem_image.mp p'; exact ⟨_,(q u b').1,(q u b').2,(wrap_here ..).symm⟩
include K in
lemma wholesale (S:Finset Cover) (q:∀ i:Axis,∃ p:ℤ,∀ x∈S,p≤ x i∧x i ≤ p+D i)(g0:0≤g)(_A:Travels Λ)(B':Club Y g s)(u':Crags α Λ w ε)(hv:0≤C)(θ:ℝ)(t:lighting m α C* Real.exp (ξ*capR (tent Y h) D)<θ):
    ∀ᶠ i:ℕ in atTop, ∀ P:Master Y s (u i), ∀ᶠ k:ℕ in atTop, ∀ p:s ≤ Y.uv (v k), ∀ f:Family (tent Y h), InTest (tent Y h) true S false f → (∀ x, ‖sold Y h s (u i) f x‖ ≤ C) → ∀ A: Mark (side Y (u i) s), (∀ x, ‖A x‖≤ C) → AtSupport false (region S (side Y (u i) s)) A → (∀ x:Orbit _, A (drawn ((Y.voyage (u i)).CapeT s) x) = sold Y h s (u i) f (drawn ((Y.voyage (u i)).CapeT s) x)) →
      Crater w (tailCost (storeH Λ.V).c (storeH Λ.V).C w) ε (posters Y s (u i) (v k) P p w).bleed.peg (region S (side Y (u i) s)) A m false → ‖E s f‖ ≤ θ:=by
 obtain ⟨t',e₀,e⟩:= exists_between t; let D':=(θ-t')/(C+1); have hx:0<D':=div_pos (sub_pos.mpr e) (by positivity)
 filter_upwards [side_grows Y s h K.pick.grow_i ((univ:Finset Axis).sup D+addgap Kx), K.pick.grow_i.tendsto_atTop.eventually (solvent_often Y h S s), (boutique Y h K S s).2 _ hx] with i x T V₀
 intro P
 filter_upwards [earnings Y h K s (u i) B' P u'.hot u'.reserve hv u'.bill_R u'.budget g0 (fun a:Axis=> Nat.le_trans (Nat.add_le_add_right (le_sup (f:=D) (mem_univ a)) _) x) (onward Y s (u i) q) t' e₀, cadence Y v K.pick.grow_k (u i)] with k w vP p f M z B uB aB K_B L
 let K₀:= w p _ aB uB L -- shadow
 have hK_B: Journey.compass Y (u i) (v k) s (sold Y h s (u i) f) = Journey.compass Y (u i) (v k) s B:=by
    unfold Journey.compass; change Marks.ratio _ _ _ _ (sold Y h s (u i) f ∘ drawn ((Y.voyage (u i)).CapeT s)) = Marks.ratio _ _ _ _ (B ∘ _); exact congrArg _ (funext fun x=>(K_B x).symm)
 have α:= V₀ f M (momentm Y (u i) s) ((terrain Y h (Y.ir (u i)) s).symm ▸ solvent_lower Y S s T) _ (ship_f (terrain Y h (Y.ir (u i)) s) (f (momentm Y (u i) s)) z); have B₀:=α.2 k vP; rw [norm_sub_rev,sold_sharp,hK_B] at B₀; have hx₀: D'*C ≤ θ-t':= (mul_le_mul_of_nonneg_left (le_of_lt (lt_add_one C)) hx.le).trans (div_mul_cancel₀ _ (ne_of_gt (show 0<C+1 from by positivity))).le; linarith only [(norm_sub_norm_le ..).trans B₀, K₀,hx₀]

end Chaperone
end YM.CF.Buffered.Afterglow.Hierarchy.Quest
