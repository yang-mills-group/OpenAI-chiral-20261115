import YM.SU5.FiniteGaugeData.Brique.Ravine
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
variable {D m n w:ℕ}{C c ε α θ:ℝ}
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
local notation "M" d:max => ((4:ℝ)*(d+addgap Kx:ℕ))^4
private lemma designL (D:ℕ)(H:D+addgap Kx≤(side Y i s).val) {T:Support (More (side Y i s))}(U:octant Y s i D T) :∃ n:ℕ, 0<n∧ sites (side Y i s) ≤ n*M D ∧ ∀ f:Mark (side Y i s),∃ S y, Mirror Λ.block (reserve Λ l) (side Y i s) T f S y n:=by
 obtain ⟨k,g,e⟩:= densL (show 0<D+addgap Kx from lt_of_lt_of_le addgap_pos (Nat.le_add_left ..)) H; let P:=2^k; let Z:= Ω; let d:=D+addgap Kx; refine ⟨P^4,by unfold P; positivity,?_,fun f=> transfer_size D k Kx (terrain Y h (Y.ir i) s).symm T g U f⟩
 let r:= More Z; have hv:r.val ≤ P*(4*d):=by change Z.val*2≤_; calc
      _ ≤ (2* P*d)*2:=by gcongr
      _ = _:=by ring
 have hx:= pow_le_pow_left' hv 4; change ((r.val:ℝ)^4 ≤ (↑((P:ℕ)^4)*(4*(d:ℝ))^4 : ℝ)); exact_mod_cast calc r.val^4 ≤ (P*(4*d))^4:= pow_le_pow_left' hv 4
                                                           _ = _:=by ring
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
private lemma earnings (H:D+addgap Kx≤(side Y i s).val) {T:Support (More (side Y i s))}(U:octant Y s i D T)(e:ℝ)(ht: lighting m α C*Real.exp (ξ*M D)<e): ∀ᶠ k:ℕ in atTop, ∀ p: s ≤ Y.uv (v k), ∀ f:Mark (side Y i s), AtSupport false T f → (∀ x, ‖f x‖ ≤ C) → Crater w (tailCost (V).c (V).C w) ε (posters Y s i (v k) P p w).bleed.peg T f m false → ‖(Ψ (v k)) f‖ ≤ e:=by
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
-- combine norm approximation on the SAME streams. Hence can choose a mark even after all delays to this periods & cutoff; no error due to contour/slope variations.
structure Crags (α:ℝ)(Λ:Preparation)(w:ℕ)(ε:ℝ):Prop where
 hot : 0 ≤ α
 reserve : Real.exp α+1 ≤ Λ.h
 bill_R : ε+tailCost (storeH Λ.V).c (storeH Λ.V).C w ≤ Real.exp (-α)
 budget : 0≤ ε
private lemma ship_f {a b:Side}(p:a=b)(A:Mark a)(f:∀ x:Fields b, ‖ship p A x‖≤C):∀ x:Fields a, ‖A x‖≤ C:= by subst b; exact f
include K in
lemma buy (S:Finset Cover) (q:∀ i:Axis,∃ p:ℤ,∀ x∈S,p≤ x i∧x i ≤ p+D)(g0:0≤g)(_A:Travels Λ)(B':Club Y g s)(u':Crags α Λ w ε)(hv:0≤C)(θ:ℝ)(t:lighting m α C* Real.exp (ξ*((4:ℝ)*(D+addgap (tent Y h):ℕ))^4)<θ):
    ∀ᶠ i:ℕ in atTop, ∀ P:Master Y s (u i), ∀ᶠ k:ℕ in atTop, ∀ p:s ≤ Y.uv (v k), ∀ f:Family (tent Y h), InTest (tent Y h) true S false f → (∀ x, ‖sold Y h s (u i) f x‖ ≤ C) →
      Crater w (tailCost (storeH Λ.V).c (storeH Λ.V).C w) ε (posters Y s (u i) (v k) P p w).bleed.peg (region S (side Y (u i) s)) (sold Y h s (u i) f) m false → ‖E s f‖ ≤ θ:=by
 obtain ⟨t',e₀,e⟩:= exists_between t; let D':=(θ-t')/(C+1); have hx:0<D':=div_pos (sub_pos.mpr e) (by positivity)
 filter_upwards [side_grows Y s h K.pick.grow_i (D+addgap Kx), K.pick.grow_i.tendsto_atTop.eventually (solvent_often Y h S s), (boutique Y h K S s).2 _ hx] with i x T V₀
 intro P
 filter_upwards [earnings Y h K s (u i) B' P u'.hot u'.reserve hv u'.bill_R u'.budget g0 x (behind Y s (u i) q) t' e₀, cadence Y v K.pick.grow_k (u i)] with k w vP p f M z L
 let K₀:= w p _ (sold_affair Y h S s (u i) M) z L -- shadow
 have α:= V₀ f M (momentm Y (u i) s) ((terrain Y h (Y.ir (u i)) s).symm ▸ solvent_lower Y S s T) _ (ship_f (terrain Y h (Y.ir (u i)) s) (f (momentm Y (u i) s)) z); have B₀:=α.2 k vP; rw [norm_sub_rev,sold_sharp] at B₀; have hx₀: D'*C ≤ θ-t':= (mul_le_mul_of_nonneg_left (le_of_lt (lt_add_one C)) hx.le).trans (div_mul_cancel₀ _ (ne_of_gt (show 0<C+1 from by positivity))).le; linarith only [(norm_sub_norm_le ..).trans B₀, K₀,hx₀]
include K in
lemma wholesale (S:Finset Cover) (q:∀ i:Axis,∃ p:ℤ,∀ x∈S,p≤ x i∧x i ≤ p+D)(g0:0≤g)(_A:Travels Λ)(B':Club Y g s)(u':Crags α Λ w ε)(hv:0≤C)(θ:ℝ)(t:lighting m α C* Real.exp (ξ*((4:ℝ)*(D+addgap (tent Y h):ℕ))^4)<θ):
    ∀ᶠ i:ℕ in atTop, ∀ P:Master Y s (u i), ∀ᶠ k:ℕ in atTop, ∀ p:s ≤ Y.uv (v k), ∀ f:Family (tent Y h), InTest (tent Y h) true S false f → (∀ x, ‖sold Y h s (u i) f x‖ ≤ C) → ∀ A: Mark (side Y (u i) s), (∀ x, ‖A x‖≤ C) → AtSupport false (region S (side Y (u i) s)) A → (∀ x:Orbit _, A (drawn ((Y.voyage (u i)).CapeT s) x) = sold Y h s (u i) f (drawn ((Y.voyage (u i)).CapeT s) x)) →
      Crater w (tailCost (storeH Λ.V).c (storeH Λ.V).C w) ε (posters Y s (u i) (v k) P p w).bleed.peg (region S (side Y (u i) s)) A m false → ‖E s f‖ ≤ θ:=by
 obtain ⟨t',e₀,e⟩:= exists_between t; let D':=(θ-t')/(C+1); have hx:0<D':=div_pos (sub_pos.mpr e) (by positivity)
 filter_upwards [side_grows Y s h K.pick.grow_i (D+addgap Kx), K.pick.grow_i.tendsto_atTop.eventually (solvent_often Y h S s), (boutique Y h K S s).2 _ hx] with i x T V₀
 intro P
 filter_upwards [earnings Y h K s (u i) B' P u'.hot u'.reserve hv u'.bill_R u'.budget g0 x (behind Y s (u i) q) t' e₀, cadence Y v K.pick.grow_k (u i)] with k w vP p f M z B uB aB K_B L
 let K₀:= w p _ aB uB L -- shadow
 have hK_B: Journey.compass Y (u i) (v k) s (sold Y h s (u i) f) = Journey.compass Y (u i) (v k) s B:=by
    unfold Journey.compass; change Marks.ratio _ _ _ _ (sold Y h s (u i) f ∘ drawn ((Y.voyage (u i)).CapeT s)) = Marks.ratio _ _ _ _ (B ∘ _); exact congrArg _ (funext fun x=>(K_B x).symm)
 have α:= V₀ f M (momentm Y (u i) s) ((terrain Y h (Y.ir (u i)) s).symm ▸ solvent_lower Y S s T) _ (ship_f (terrain Y h (Y.ir (u i)) s) (f (momentm Y (u i) s)) z); have B₀:=α.2 k vP; rw [norm_sub_rev,sold_sharp,hK_B] at B₀; have hx₀: D'*C ≤ θ-t':= (mul_le_mul_of_nonneg_left (le_of_lt (lt_add_one C)) hx.le).trans (div_mul_cancel₀ _ (ne_of_gt (show 0<C+1 from by positivity))).le; linarith only [(norm_sub_norm_le ..).trans B₀, K₀,hx₀]
end YM.CF.Buffered.Afterglow.Hierarchy.Quest
