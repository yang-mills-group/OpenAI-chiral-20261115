import YM.CF.Peaks.Pave
set_option autoImplicit false
noncomputable section
namespace YM.CF.Peaks
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip
open scoped Topology Matrix MatrixOrder BigOperators Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable (j:ℕ)(L:Side)(ho:Odd L.val)(hj:Even j)(he:1≤ j)(T:Script Male)(ht:Use j L T)
variable {N P:Side}(G:Ratio N P) (x:Coil N P)(M:Male)(u:Bool)
include j ht in
lemma invertT (hx:icec x=x)(h:IsUnit (T M G x)):
  let W:= ticketT T u M G x; let V:=ticketT T (!u) M G x
  star V*W=1 ∧ W*star V=1:=by
  intro W V
  let K:=T M G x; let P:=lobe G u
  have he:Commute (lobe G true) K:=ht.orients M G x -- include
  have hh:P*K=K*P:=by unfold P; cases u; rw [lobe_plus,mul_sub,sub_mul,one_mul,mul_one,he.eq]; exact he.eq
  have hp:P*P=P:=(lobe_sq ..).1; have hg:star P=P:=(lobe_sq ..).2
  let Q:=1-P; have hb: P*Q=0:=by unfold Q; rw [mul_sub,hp,mul_one]; abel
  have hb':Q*P=0:=by unfold Q; rw [sub_mul,hp,one_mul]; abel
  have h1: K*K⁻¹=1:=(Fock.live h).1; have h2: K⁻¹*K=1:=(Fock.live h).2
  have hQ:star K⁻¹*star K=1:= by rw [←star_mul,h1,star_one]
  have he':P*K⁻¹=K⁻¹*P:= h.mul_left_cancel (by rw [← mul_assoc,← mul_assoc,← hh, mul_assoc,h1,mul_one,one_mul])
  have hc:P*star K = star K*P:=by nth_rw 1 2 [←hg]; rw [← star_mul, ← star_mul, hh]
  have hw:W=K⁻¹*P+star K*Q:=by unfold W ticketT; rw [hx]
  have hv:V=K⁻¹*Q+star K*P:=by unfold V ticketT; rw [circ,hx]; congr 2; abel -- tune
  have hl:Q*Q=Q:=by unfold Q; rw [mul_sub,sub_mul (1:Op _) P P,one_mul,hp,mul_one]; abel
  suffices hs:star V * W=1 by exact ⟨hs,mul_eq_one_comm.mp hs⟩
  rw [hw,hv,star_add,star_mul,star_mul,star_star,hg,show star Q=Q by unfold Q; rw [star_sub,star_one,hg],add_mul,mul_add,mul_add,show P*K*(star K *Q)=0 from ?_,show Q * star K⁻¹ * (K⁻¹*P)=0 from ?_,show P*K*(K⁻¹*P)=P by rw [← mul_assoc, mul_assoc P,h1,mul_one,hp],show Q*star K⁻¹*(star K*Q)=Q by rw [← mul_assoc, mul_assoc Q,hQ,mul_one,hl],add_zero,zero_add]
  · unfold Q; abel
  · rw [← he', ← mul_assoc, mul_assoc _ (star K⁻¹),show star K⁻¹ * P=P * star K⁻¹ by nth_rw 1 2 [← hg]; rw [← star_mul,← star_mul,he'], ← mul_assoc, hb',zero_mul,zero_mul]
  rw [hh,mul_assoc,← mul_assoc P,hc,mul_assoc (star K),hb,mul_zero,mul_zero]
structure Along (u:Bool)(M:Male)(G:Ratio N P)(x:Coil N P) : Prop where
  bridge : star (ticketT T (!u) M G x)*ticketT T u M G x=1
  lead : IsStarProjection (foal j u M G x)
  beam : IsStarProjection (wh j L ho u M G x)
  lowC : pine j L ho T u M G x*lake j L ho T u M G x=foal j u M G x
  baseC: lake j L ho T u M G x*pine j L ho T u M G x=wh j L ho u M G x
  leftC : foal j u M G x * pine j L ho T u M G x=pine j L ho T u M G x
  rightC : pine j L ho T u M G x * wh j L ho u M G x=pine j L ho T u M G x
omit G x M u
lemma ambient (a b:ℝ)(hp:0<a)(h:a≤b){U:Nom N P}{G:Ratio N P}(hs:JointB G U a): unionP U∈legal G b:=⟨U,⟨hs.fg.shrink h,hs.cg.shrink h,fun i=>(hs.follow i).trans h⟩,by simpa using hp.trans_le h⟩
include he ho hj ht
lemma massive (u:Bool): ∃ e:ℝ,0<e∧∃ w:ℕ,∀ {N P:Side}(G:Ratio N P),G.count=L→ w≤ N.val →∀ M (U:Nom N P), JointB G U e→ Along j L ho T u M G (unionP U):=by
  obtain ⟨a,k,v,H⟩:=(useK j L hj ho ht).2
  obtain ⟨b,S,r,V⟩:=(seller j L ho hj he u T ht).2
  obtain ⟨d,K,w,D⟩:=funde_q j he
  let e:=min b (min a d); have hm:0<e:=lt_min S (lt_min k K)
  refine ⟨e,hm,max v (max r w),fun {N P} G he hv M U h=>?_⟩
  have hh:r⊔w≤N.val := (le_max_right ..).trans hv
  have he1 := H G he ((le_max_left ..).trans hv) _ (ambient _ _ hm ((min_le_right ..).trans (min_le_left ..)) h) M
  have he2:= V G he ((le_max_left ..).trans hh) _ (ambient _ _ hm (min_le_left ..) h) M
  have he3 : e≤d:=(min_le_right ..).trans (min_le_right ..)
  have hg: IsStarProjection (foal j u M G (unionP U)):=by
    have hy:= D M P (le_trans ((le_max_right ..).trans hh) (by rw [G.exact_size]; exact Nat.le_mul_of_pos_right _ G.count.property)) _ (h.fg.shrink he3)
    suffices hp: IsStarProjection (foot G (funde j M P (profile U.1))) by cases u; rw [← show (!true)=Bool.false from rfl,foil_neg]; exact IsStarProjection.one_sub hp; exact hp -- check lemma
    exact ⟨(by unfold IsIdempotentElem; rw [← foot_mul,hy.isIdempotentElem.eq]),(by rw [isSelfAdjoint_iff,← foot_s,hy.isSelfAdjoint.star_eq])⟩
  have he4: IsStarProjection (wh j L ho u M G (unionP U)):=by
    have hb:= D (upMale L ho M) N ((le_max_right ..).trans hh) _ (h.cg.shrink he3)
    apply whirl G u; cases u; exact IsStarProjection.one_sub hb; exact hb
  obtain ⟨hh,hl,hA,hB⟩:= spruce_kt j L ho G u M (unionP U) T ht he2 hg he4 -- inspect
  exact ⟨(invertT j L T ht G _ M u (revI U) he1).1,hg,he4,hl,hh,hA,hB⟩
lemma joined : ∃ e:ℝ,0<e∧∃ w:ℕ,∀ {N P:Side}(G:Ratio N P),G.count=L→ w≤ N.val →∀ M (U:Nom N P), JointB G U e→∀ u, Along j L ho T u M G (unionP U):=by
  obtain ⟨a,p,w,H⟩:=massive j L ho hj he T ht true; obtain ⟨d,h,r,hx⟩:=massive j L ho hj he T ht false
  refine ⟨min a d,lt_min p h,max w r,fun {N P} n hu hp M U hh u=>?_⟩ -- fix implicit
  cases u
  · exact hx n hu ((le_max_right ..).trans hp) M U ⟨hh.fg.shrink (min_le_right ..),hh.cg.shrink (min_le_right ..),fun i=>(hh.follow i).trans (min_le_right ..)⟩
  exact H n hu ((le_max_left ..).trans hp) M U ⟨hh.fg.shrink (min_le_left ..),hh.cg.shrink (min_le_left ..),fun i=>(hh.follow i).trans (min_le_left ..)⟩
end YM.CF.Peaks
