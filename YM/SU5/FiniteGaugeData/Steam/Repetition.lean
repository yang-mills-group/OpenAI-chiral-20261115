import YM.SU5.FiniteGaugeData.Steam.Valence
import YM.SU5.FiniteGaugeData.Hierarchy.Marble
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Heat
namespace Quest
section
variable (A:Set ℤ) (u:ℕ) {n B:Side} (K:Calibration)
local notation "N"=> K.c n
/-- copy specification independent of cutoff, with disjoint-room purchases.
    Therefore transfer even huge sup norms (after paying their own cutoff delay here).
    K copy uses all 4B planes; choose a brick+margin and reflect the WHOLE, supports may be full bodies padded before calls. 
 -/
inductive Mirror (B:Side)(u:ℕ) (n:Side): Support (More n)→ Mark n → (Support (More n)) → Mark n → ℕ → Prop
 | self {S f}: Mirror B u n S f S f 1
 | grow {S f} a z (h: S ⊆ band n a (Heat.gaugeShift B z) u): Mirror B u n S f ((S.image ((plane a (Heat.gaugeShift B z)).anon n))∪S) (reflMark a (Heat.gaugeShift B z) f*f) 2
 | trans {S T U f g h m k}: Mirror B u n S f T g m → Mirror B u n T g U h k → Mirror B u n S f U h (m*k)
variable {K A u} {S T:Support (More n)} {x y:Mark n}
lemma Mirror.covers {k:ℕ}(f: Mirror B u n S x T y k)(g:AtSupport false S x): AtSupport false T y:= by
 induction f with
 | self=>exact g
 | grow a z _=>exact ((g.refl ..).mono subset_union_left).mulM (g.mono subset_union_right)
 | trans _ _ ih ik=> exact ik (ih g)
-- monotone not actually conversion of membership with `le` direction: u enforces downstairs even when recon m= L older. keep.
lemma Mirror.cost {k:ℕ}(p: Mirror B u n S x T y k){C:ℝ}(h:∀ i,‖x i‖ ≤ C) :∀ i, ‖y i‖ ≤ C^k:=by
 induction p generalizing C with
 | self=> simpa using h
 | grow=> intro i; simp_rw [Pi.mul_apply,sq]; refine (norm_mul_le ..).trans (mul_le_mul ((theta_fee ..).trans_le (h _)) (h i) (norm_nonneg _) ((norm_nonneg _).trans (h i)))
 | trans _ _ ih ik=> simpa only [pow_mul] using ik (ih h)

private lemma funnel (i:Axis)(k:ℕ){d:ℕ}(h:2^k*(d+addgap K) ≤ (N).val){S:Support (More N)}(w:rest K n S i d)(f:Mark (K.c n)) : ∃ T:Support (More N),∃ y:Mark (K.c n), Mirror K.B K.ℓ (K.c n) S f T y (2^k) ∧ ∀ j:Axis,j≠i→ ∀ d,rest K n S j d→ rest K n T j d:=by
 induction k generalizing d S f with
 | zero=> exact ⟨_,_,by simpa using Mirror.self (B:=K.B) (f:=f) (S:=S) (u:=K.ℓ),fun _ _ _ h=>h⟩
 | succ k ih=>
    obtain ⟨z,u,v,e⟩:= twice i w ((Nat.le_mul_of_pos_left _ (pow_pos two_pos _)).trans h)
    obtain ⟨A,B,q,t⟩:= ih (d:=2*d+addgap K) (by rw [pow_succ] at h; exact h.trans' (le_of_eq (by ring))) v (reflMark i (Heat.gaugeShift K.B z) f * f)
    exact ⟨_,_, pow_succ' 2 k ▸ Mirror.trans (Mirror.grow _ z u) q, fun j p d h=> t j p d (e j p d h)⟩
lemma plans (k:ℕ){d:ℕ}(h:2^k*(d+addgap K)≤(N).val){S:Support (More N)}(w:∀ i,rest K n S i d)(f:Mark (K.c n)) : ∃ T y, Mirror K.B K.ℓ (K.c n) S f T y ((2^k)^4):=by
 have hf {S':Support (More N)}(F:Finset Axis)(w:∀ i∈ F, rest K n S' i d)(f:Mark (K.c n)): ∃ T y, Mirror K.B K.ℓ (K.c n) S' f T y ((2^k)^F.card):=by
    induction F using Finset.induction_on generalizing S' f with
    | empty=> simp only [card_empty,pow_zero]; exact ⟨_,_,Mirror.self⟩
    | @insert i R v ih=> obtain ⟨T,y,p,q⟩:=funnel i k h (w i (mem_insert_self ..)) f; obtain ⟨U,z,u⟩:=ih (fun j hj=> q j (fun x=>v (x ▸ hj)) d (w j (mem_insert_of_mem hj))) y; rw [card_insert_of_notMem v,pow_succ']; exact ⟨U,z,p.trans u⟩
 have ht:=hf univ (fun i _=> w i) f; rwa [show (univ:Finset Axis).card=4 from card_fin _] at ht
lemma transfer_size {s n: Side} (d k:ℕ)(K:Calibration)(a:n=K.c s)(S:Support (More n))(h:2^k*(d+addgap K)≤n.val)(w:∀ i:Axis, ∃ b:ℤ,∀ x∈S,Chord b d (x i))(f:Mark n) : ∃ T y, Mirror K.B K.ℓ n S f T y ((2^k)^4):= by
 subst n; exact plans k h w f
private lemma goldi {x y:ℕ}(h:0<y)(p:y≤x):∃ k:ℕ,2^k*y≤x∧x ≤ 2* (2^k)*y:=by
  have he : x < 2^x*y:= lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.le_mul_of_pos_right _ h)
  let P(k:ℕ):= x ≤ 2*(2^k)*y
  have ht: ∃ k,P k:=⟨x,by unfold P; linarith⟩
  refine ⟨Nat.find ht,?_,Nat.find_spec ht⟩
  generalize e:Nat.find ht=k
  cases k with
  | zero=> simpa using p
  | succ k=> have h:=Nat.find_min ht (by omega : k < Nat.find ht); change ¬ x ≤ 2*2^k*y at h; rw [pow_succ']; omega
lemma Mirror.gauge {k:ℕ} {F U:Mark (K.c n)} {S T: Support (More (K.c n))}(v:Mirror K.B K.ℓ (K.c n) S F T U k) {X: Mark (K.c n)→ℂ}{D:ℝ}{L:Loom _}(p:Journey.Metered K n L X D)(t:AtSupport false S F): ‖X F‖^k ≤ ‖X U‖:=by
 generalize hx:K.B=B at v
 generalize hy:K.ℓ=u at v
 induction v with
 | self=>simp
 | grow a z h=> subst B u; exact p.twiceX a z (t.mono h)
 | @trans _ _ _ f g u l s v w a b=> rw [pow_mul]; exact (pow_le_pow_left₀ (by positivity) (a t) _).trans (b (v.covers t))
-- variable data with casts. heat meets. 
lemma Mirror.heat {k:ℕ} {V:Side} {X: Mark V→ℂ}{D:ℝ}{S0 T0: Support (More V)}{F0 U0:Mark V}{L:Loom _}(s:V=K.c n)(v:Mirror K.B K.ℓ V S0 F0 T0 U0 k)(p:Journey.Metered K n L (X ∘ ship s.symm) D)(t:AtSupport false S0 F0):‖X F0‖^k ≤ ‖X U0‖:= by subst V; exact v.gauge p t -- type lambda CoeFun rfl?
end
open Journey Py Py.Rate LocalLimit Preparation FullBill Steam Vale
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1 ≤ Λ.x){r:ℝ}{v u:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→Family (tent Y h)→ℂ}
set_option quotPrecheck false
variable (C:Journey.Universal Y h v u I E) (s i k:ℕ)
local notation "Kʳ"=> tent Y h
local notation "N₁" i:max=> side Y i s
local notation "Capeq" i:max=> (Y.voyage i).CapeT s
local notation "Χ" i:max k:max=> ((Y.voyage i).X (Y.uv k)).gram s
local notation "Ζ" f:max=> sold Y h s i f
local notation "Ψ" i:max k:max=> Journey.compass Y i k s
local notation "Xₛ"=> hat Λ.R.L Λ.x s
variable {f:Family (tent Y h)}
include h
private lemma sing_α {k:ℕ}(F:Family Kʳ)(p:(Y.voyage i).kick ≤ k): hot Y h s i k F= Journey.solder Y i k p s (sold Y h s i F):=by rw [hot,dif_pos p,sold_v]; rfl
omit h in
private lemma melt (w:ℝ)(pw:0<w)(x:Mark (N₁ i))(p:Envelope x): ∀ᶠ k in atTop, ∀ H:(Y.voyage i).kick ≤ k, ‖(Ψ i k) x-Journey.solder Y i k H s x‖ ≤ w:=by
 let v:Marks.Tagged (side Y i s):= x ∘ drawn (Capeq i); let W: Envelope v:= mark_pay ((Y.voyage i).ownership s).paid.bill p; obtain ⟨a,h⟩:= W.cost; have hp:0 ≤ a := (norm_nonneg _).trans (h (1,Classical.arbitrary _)); have ha:0<a+1:=by linarith
 filter_upwards [Y.thaw s (w/(a+1)) (by positivity)] with k t H; exact (t i H v (a+1) W.meas (fun x=> (h x).trans (by linarith))).trans (div_mul_cancel₀ w ha.ne').le

variable {S₀:Finset Cover}(p:InTest (tent Y h) true S₀ false f)
include C p
private lemma hot_I: Tendsto (fun k=>hot Y h s i (u k) f) atTop (𝓝 (I s f i)):=by -- uses C p
 let g:TestFamily Kʳ true f:=⟨⟨S₀,p⟩,fun e=>by contradiction⟩
 have he:= C.pick.booked Y h s g
 rw [tendsto_nhds_unique ((C.together s f g).inner i) (he.2.inner i)]
 exact he.1.inner i
-- above not included p C
-- normalized limit at any sold mark. y doesn't need lift; use possibly many bad or many-mode toll. solely eventual UV WEAR here (therefore hot limit needs *same* UV cut selection etc). actual readings exact as always. Requirement Ferry etc already paid before applying.
include C p
lemma Mirror.distill {y T S n} (A:Mirror Λ.block (reserve Λ l) (side Y i s) S (Ζ f) T y n)(hp:AtSupport false S (Ζ f))(c:ℝ)(t:∀ᶠ k in atTop, ‖(Ψ i (u k)) y‖ ≤ c) : ‖I s f i‖^n ≤ c:=by -- param order
 apply le_of_forall_pos_le_add
 intro ε w
 apply le_of_tendsto ((hot_I Y h C s i p).norm.pow n)
 filter_upwards [t,C.pick.pass Y h s i,C.pick.grow_k.tendsto_atTop.eventually (melt Y s i ε w y (A.covers hp).env)] with k hz H T
 let m:= H.depth; have D:Journey.Metered Kʳ (momentm Y i s) (deltaL Y h i s) (Journey.solder Y i (u k) m s ∘ ship (terrain Y h (Y.ir i) s)) (duetCharge Y s):= by
    have he:= boxprice Y h i (u k) m s H.fire H.enters
    rw [show (Journey.solder Y i (u k) m s ∘ ship (terrain Y h (Y.ir i) s))=collector Y h i (u k) m s from funext fun x=>(congrArg (Journey.solder Y i (u k) m s) (ship_eq (terrain Y h (Y.ir i) s) x))] ; exact he
 let G:= Journey.solder Y i (u k) m s
 rw [sing_α Y h s i f m]; apply (Mirror.heat (K:=Kʳ) (X:=G) (terrain Y h (Y.ir i) s).symm A D hp).trans; have he:= T m
 rw [norm_sub_rev] at he; have hg: ‖G y‖-‖(Ψ i (u k)) y‖ ≤ ε:= (norm_sub_norm_le ..).trans he; linarith
omit p C
abbrev octant (d:ℕ) (T:Support (More (side Y i s))):=∀ a:Axis,∃ b:ℤ,∀ i∈T,Chord b d (i a)
-- define screen (large-size copies). vol ≤ copies*(4*D)^4. for cost want universal threshold independent h except addgap K which depends on Λ l. addgap K see Wood; actually depends b tol; not h.
-- brick may call in all layouts and want uniform in mark. hypot says any y images under Mirror. Basis closed T may larger than need. supports across mirror disjoint provided `reserve`. costs for field approximants chosen separately.
omit h in
def setback (w:ℝ) (St:Support (More (side Y i s))) (f:Mark (side Y i s)) (u:ℕ→ℕ) := ∀ (n:ℕ) y T, Mirror Λ.block (reserve Λ l) (side Y i s) St f T y n → ∀ᶠ k in atTop,Toll (w^n) Λ.W (((Y.voyage i).X (Y.uv (u k))).gram s) ((Y.voyage i).CapeT s) (hat Λ.R.L Λ.x s) (y ∘ drawn ((Y.voyage i).CapeT s))
-- want μ propagation meter to combine geometric regularity: N powers. 
include p C
local notation "ζ"=> slopeF Λ.W r
lemma meter_bill {St:Support (More (side Y i s))} (p':AtSupport false St (Ζ f)) {w:ℝ}(t:0≤w)(U:setback Y s i w St (Ζ f) u)(P:Club Y r s) (D:ℕ)(V:octant Y s i D St) (a:D+addgap Kʳ ≤ (N₁ i).val) (y:0≤r): ‖I s f i‖ ≤ w*Real.exp (ζ * ((4:ℝ)*(D+addgap Kʳ:ℕ))^4) := by
 have hξ:0≤ ζ:=by unfold slopeF; positivity
 obtain ⟨k,g,e⟩:= goldi (show 0<D+addgap Kʳ from lt_of_lt_of_le addgap_pos (Nat.le_add_left ..)) a
 obtain ⟨Ω,x,b⟩:= transfer_size D k Kʳ (terrain Y h (Y.ir i) s).symm St g V (Ζ f)
 let j:=(2^k:ℕ)^4; have ht: Mirror Λ.block (reserve Λ l) (N₁ i) St (Ζ f) Ω x j:= b
 let Z:= (side Y i s); let M:=Real.exp (ζ * sites Z)
 have hx := Mirror.distill Y h C s i p ht p' ((w^j)*M) (show ∀ᶠ k in atTop,‖Journey.compass Y i (u k) s x‖ ≤ (w^j)*M from (by
   filter_upwards [U j x Ω ht, C.pick.pass Y h s i] with k t' p; exact Club.toll P (x ∘ drawn ((Y.voyage i).CapeT s)) (pow_nonneg t _) p.depth p.enters t')) -- check order
 let d:= D+addgap Kʳ; have hs : sites Z ≤ j*((4:ℝ)*(d:ℝ))^4:=by -- val remove .val
    let r:= More Z; have hp:r.val ≤ (2^k)*(4*d):=by change Z.val*2≤_; calc
      _ ≤ (2* 2^k*d)*2:=by gcongr
      _ = _:=by ring
    have hy:= pow_le_pow_left' hp 4; rw [mul_pow,mul_pow 4] at hy
    change ((r.val:ℝ)^4 ≤ (↑((2^k:ℕ)^4)*(4*(d:ℝ))^4 : ℝ))
    exact_mod_cast calc r.val^4 ≤ ((2^k)*(4*d))^4:= pow_le_pow_left' hp 4
                        _= _:=by ring
 refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity:w*Real.exp (ζ*((4:ℝ)*(d:ℝ))^4)≥0) (n:=j) (by unfold j; positivity)).1 (le_trans hx ?_); rw [mul_pow,←Real.exp_nat_mul]; apply mul_le_mul_of_nonneg_left _ (by positivity); apply Real.exp_monotone; linarith only [mul_le_mul_of_nonneg_left hs hξ] -- d
-- relative explicit for rectangular coords.
omit p C h
lemma behind {S:Finset Cover}{d':ℕ}(b:∀ i:Axis,∃ p:ℤ,∀ x∈ S,p ≤ x i ∧ x i≤p+(d':ℤ)) : octant Y s i d' (region S (side Y i s)):=by
 intro a; obtain ⟨p,b⟩:=b a; refine ⟨p,fun i p'=>?_⟩; obtain ⟨u,b',rfl⟩:=mem_image.mp p'; exact ⟨_,(b u b').1,(b u b').2,(wrap_here ..).symm⟩
include C h p
lemma final_score {w:ℝ}(t:0≤w)(U:∀ᶠ i in atTop,setback Y s (v i) w (region S₀ (side Y (v i) s)) (sold Y h s (v i) f) u)(P:Club Y r s)(D:ℕ)(a:∀ i:Axis,∃ p:ℤ,∀ x∈ S₀,p ≤ x i ∧ x i ≤ p+D) (y:0≤r): ‖E s f‖ ≤ w*Real.exp (ζ * ((4:ℝ)*(D+addgap Kʳ:ℕ))^4) := by
 apply le_of_tendsto ((C.together s f (⟨⟨S₀,p⟩,fun e=>by contradiction⟩)).periods.norm)
 filter_upwards [U,((c_grows (tent Y h)).comp ((momentum Y s).comp C.pick.grow_i.tendsto_atTop))|>.eventually_ge_atTop (D+addgap (tent Y h))] with i u d
 have hd:D+addgap Kʳ ≤ (side Y (v i) s).val:= by rw [show side Y (v i) s = (tent Y h).c (momentm Y (v i) s) from (terrain Y h (Y.ir (v i)) s).symm]; exact d
 exact meter_bill Y h C s _ p (sold_affair Y h _ _ _ p) t u P D (behind Y s (v i) a) hd y
-- explicit size eventually in h. syntax precedence
omit p in
lemma fallback (w:ℝ)(t:Club Y r s) {S:Support (More (side Y i s))}{f:Mark (side Y i s)}(hY:∀ x, ‖f x‖ ≤ w): setback Y s i w S f u:=fun j x T v=> (C.pick.pass Y h s i).mono fun k b=> Toll.supplies (t.full i (u k) b.enters) (fun i=> v.cost hY _)
lemma ticket_limit {w:ℝ}(t:0≤w)(n:Side)(u: Satin.Hosp S₀ ((Kʳ).c n))(X:∀ x, ‖f n x‖ ≤ w)(P: Club Y r s)(D:ℕ)(a:∀ i:Axis,∃ p:ℤ,∀ x∈S₀,p ≤ x i∧x i≤p+D)(y:0≤r): ‖E s f‖ ≤ (duration S₀*w)*Real.exp (ζ*((4:ℝ)*(D+addgap Kʳ:ℕ))^4) := by
 let Q:= certifyAs S₀ (tent Y h) f p; have he: composeQ (tent Y h) S₀ Q=f:= Hierarchy.certified S₀ _ f p; have hQ:= offered_bound S₀ (tent Y h) Q u (show ∀ x, ‖composeQ (tent Y h) S₀ Q n x‖ ≤ w by rw [he]; exact X)
 exact final_score Y h C s p (mul_nonneg (duration_pos _).le t) (Eventually.of_forall fun i=> fallback Y h C s _ _ P fun x=> (congrArg (fun f=> ‖sold Y h s (v i) f x‖) he).ge.trans ((sold_q_bound Y h S₀ s (v i) Q _).trans (mul_le_mul_of_nonneg_left hQ (duration_pos _).le))) P D a y
end Quest
end YM.CF.Buffered.Afterglow.Hierarchy
