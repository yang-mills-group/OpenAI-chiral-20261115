import YM.SU5.LitCurrent.Coil
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.LitCurrent
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour
open Stax Skye Jet Scroll Finset Palot Cadre Vow RG Rive Nor Hake MeasureTheory
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel Swell StressExchange
variable {N:Side}{X Y:SOp N}{o:Seat N}{a b c d v:ℝ}{r:ℕ}
local notation "I" => Single N
open Buffered _root_.Zephyr.Chern
variable {B W:ℝ}

lemma paid_site_card (P:SOp N)(p:Soak o P a v d)(X:StemA N)(w:Oily a d B W)
    (t:Temper o X B) : let f:=fun t=>Matrix.trace (P (profile (petals X t)))
    Bud f ∧ ∀ i, ‖bud f i‖≤W*v:=by
 intro f; obtain ⟨F,C,h,u,q,s⟩:=p
 let M(S:Sa N)(x:Chin N):=if p:x∈Openc (More N) d then F S ⟨x,p⟩ else 0
 have he(S:Sa N)(x:Openc (More N) d): M S x.val= F S x:=dif_pos x.property
 have hx(S:Sa N): Piece d S (C S) (M S):=by
    have hp:= h S; rw [show F S= (fun x=> M S x.val) from funext fun x=>(he S x).symm] at hp; exact hp
 have hv(S:Sa N)(i j:Single N)(k:Fin 3): ‖wad (M S) X i j k‖ ≤ W*(Branch.rent a S * C S i j):=by
    by_cases Q:C S i j=0; · rw [wad,(kernel_free (hx S) Q w.s.ready X).bud_eq,Q]; simp
    have hh:= (hx S|>.expo i j).triggered Q; have b':o∈ S:=by by_contra h'; apply Q; rw [u S h']; rfl
    have hg:=t.above; have hs:1≤B*(1+(S.card:ℝ)):=one_le_mul_of_one_le_of_one_le hg (by simp)
    have hp:∀ x∈leaks S,|X x| ≤ B*(1+(S.card:ℝ)):= fun x h=> (t.grow x).trans (mul_le_mul_of_nonneg_left (add_le_add_right ((Nat.cast_le.mpr (show separation x.1 o ≤ S.card from (hh.1.lim _ (mem_filter.mp h).2.1 o b').le))) _) (zero_le_one.trans hg)) -- tune
    refine ((kernel_jet (hx S) w.s hs hp).2 k).trans ?_
    rw [←mul_assoc]; apply mul_le_mul_of_nonneg_right _ (h S|>.nonn i j); refine (w.q S.card).trans (_root_.mul_le_mul_of_nonneg_left ?_ w.bound.le)
    exact rent_up (half_le_self w.hb.le) S
 let G(t):ℂ:= ∑ i:Sa N,∑ j:Single N, drip (M i) X j j t
 have hp : f =ᶠ[𝓝 (0:ℝ)] G:=by
    filter_upwards [petals_open w.s.ready X] with t v
    let y:= (⟨profile (petals X t),v⟩:Openc (More N) d)
    change Matrix.trace (P y.val)= _; rw [s y,Matrix.trace_sum]; refine sum_congr rfl fun i _=>?_ ; rw [←he i y]; rfl
 let D:= ∑ S:Sa N,∑ i:Single N,wad (M S) X i i
 have hK: Bloom f D := Bloom.congr (f:=G) (Bloom.sum univ fun i _=> _root_.Zephyr.Chern.Bloom.sum univ fun j _=>(kernel_bud (hx i) w.s.ready).bloom) hp
 refine ⟨hK.1, fun i=>?_⟩; rw [hK.bud_eq]; unfold D; simp_rw [Finset.sum_apply]; apply le_trans (norm_sum_le ..)
 apply le_trans _ (mul_le_mul_of_nonneg_left q w.bound.le); rw [mul_sum]; apply sum_le_sum; intro S _; refine (norm_sum_le ..).trans ((sum_le_sum fun j _=> hv S _ _ _).trans ?_)
 rw [←mul_sum, ←mul_sum]; refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (rent_pos _ _).le) w.bound.le
 exact sum_le_sum fun i _=> Finset.single_le_sum (fun j _=> (h S).nonn i j) (mem_univ i)

lemma petal_on (p:BudgetPoint)(S:Sa N)(X:StemA N):∀ᶠ t in 𝓝 (0:ℝ), pingS p.threshold S (petals X t):=by
 refine (cont_petal X).continuousAt.tendsto.eventually (ping_o.mem_nhds (show _ from ?_)); rw [petal_idle]; exact ping_f p S -- tune

def compassLine {P T:SOp N}(E:Pattern P T r d a v)(x:Cover)(K:Scree.Loom N)(p:BudgetPoint)(k:ℕ)(t:ℝ):ℂ:=Matrix.trace (taxHat K p k (wrap N x) E (turntable N t))
lemma maskedBloom {P T:SOp N}(E:Pattern P T r d a v)(x:Cover){K:Scree.Loom N}{t:ℝ}{p:BudgetPoint}{k q:ℕ}
    (z:Checked p K t d a k q) (w:Oily a d (breadth x) W) : Bud (compassLine E x K p k) ∧
    ∀ i:Fin 3,
      ‖bud (tracer P r x) i-bud (compassLine E x K p k) i‖≤ W*(Real.exp (-a*k)*expiry (4*a) v):=by
 let X:=stream N; let W₀:=wrap N x; let A:=E.A W₀; let g(t):=Matrix.trace (beforePing A k (profile (petals X t))); let f(t):=Matrix.trace (beyond A k (profile (petals X t)))
 let u:= totals A z.hint (E.moorA _) k
 obtain ⟨h₀,_⟩:= paid_site_card (beforePing A k) u.1.pay X w (deep_grace x)
 obtain ⟨h₁,r'⟩:= paid_site_card (beyond A k) u.2 X w (deep_grace x)
 have h:Bud f:=h₁; have H:Bloom g (bud g):= Bud.bloom h₀
 have hp:(compassLine E x K p k) =ᶠ[𝓝 0] g:=by
    filter_upwards [petal_on p (offsetMask p.B W₀) X,petals_open z.angle X] with t v e
    let U:=petals X t; let V:Orbit N:=(U,Classical.arbitrary _); let y:Openc (More N) d:=⟨profile U,e⟩
    change Matrix.trace (live K p k W₀ A V.1)=Matrix.trace (beforePing A k y.val); rw [noTag W₀ A z (E.moorA _),if_pos v]; exact congrArg Matrix.trace (runs W₀ A z (E.moorA _) V v U y rfl (fun _ _ _ _ _ _ _ _=>rfl))
 have ht:tracer P r x =ᶠ[𝓝 0] (fun t=>g t +f t):=by
    filter_upwards [petals_safe X z.angle, petals_open z.angle X] with t h₀ h₁
    let U:=petals X t; let Y:= (⟨profile U,h₁⟩:Openc (More N) d)
    change Matrix.trace (taxKernel P W₀ r Y.val)=Matrix.trace (beforePing A k Y.val)+Matrix.trace (beyond A k Y.val)
    rw [E.tax W₀ U h₀ Y rfl, ← Matrix.trace_add,saw_recover]; -- tune
 refine ⟨(H.congr hp).1, fun i=>?_⟩; rw [((H.add h.bloom).congr ht|>.bud_eq), (H.congr hp|>.bud_eq),Pi.add_apply, add_sub_cancel_left]; exact r' _
lemma maskedReward {P T:SOp N}(E:Pattern P T r d a v)(x:Cover){K:Scree.Loom N}{t:ℝ}{p:BudgetPoint}{k q:ℕ}
    (z:Checked p K t d a k q)(w:Oily a d (breadth x) W)(u:∀ i∈layout r x arcOrder,Stakes (localLevel P i) b): Stakes (compassLine E x K p k) ((layout r x arcOrder).length*b- W*(Real.exp (-a*k)*expiry (4*a) v)):=by
 have ht:= (receive_tax _ _ _ _ u).2; obtain ⟨h,h'⟩:= maskedBloom E x z w; refine ⟨h,?_⟩
 let U:= tracer P r x; let V:= compassLine E x K p k; have v:= (Complex.re_le_norm (bud U 2-bud V 2)).trans (h' 2)
 unfold U V at v; rw [Complex.sub_re] at v; linarith only [ht,v]
end YM.CF.LitCurrent
