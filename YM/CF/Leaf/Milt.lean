import YM.CF.Leaf.Gym
import YM.CF.Cadre.Sike
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Leaf
open Function Filter Topology Lattice Finset Palot Cadre PowerSeries
open scoped Classical Topology
variable {A:Type*}[Fintype A][DecidableEq A]{B:Type*}[AddCommMonoid B]
-- exponential Ricatti price. separate trivial order. arbitrary many angular perturbations paid on short roots. uses one-body W.Shape.
variable (o:A)(F:leaf A→ PS)(P: leaf A→ℝ)(X:leaf A)(y z s a b R K N0 N1 N2:ℝ)(v:leaf A→ℝ)
lemma KtwP {α:Type*}[AddCommMonoid α](H: B→+α)(J:leaf A→leaf A→B)(T:leaf A) : H (Ktw J T)=Ktw (fun X Y=>H (J X Y)) T:=by simp only [Ktw,map_sum,apply_ite H, map_zero]
lemma KthP {α:Type*}[AddCommMonoid α](H: B→+α)(J:leaf A→leaf A→leaf A→B)(T:leaf A) : H (Kth J T)=Kth (fun X Y Z=>H (J X Y Z)) T:=by simp only [Kth,map_sum,apply_ite H, map_zero]
abbrev αD:= Ktw (fun X Y:leaf A=> P X • F Y)
abbrev βD:= Kth (fun X Y Z:leaf A=>P X • (F Y * F Z))
def ΦD(X:leaf A): PS:= αD F P X+βD F P X
def ϕV(t:ℝ)(i:ℕ): leaf A→ℝ:=fun X=> mintL i t (F X)
def ϕY(t:ℝ)(i:ℕ):leaf A→ℝ:= ϕV (fun X:leaf A=>derivative ℝ (F X)) t i
lemma mint_v(c:ℝ)(i:ℕ)(x:ℝ)(U:PS):mintL i x (c • U)=c* mintL i x U:=by unfold mintL; simp_rw [coeff_smul,smul_eq_mul,mul_left_comm _ c,mul_sum]
abbrev mintA(t:ℝ)(i:ℕ) : PS→+ℝ:=⟨⟨mintL i t,by simp [mintL]⟩, fun x y=>mintP x y i⟩ -- tune
lemma Φcash (t:ℝ)(i:ℕ)(h:∀ X,cent (F X))(v:0 ≤ P)(p:0≤t) : let V:=ϕV F t i; mintL i t (ΦD F P X) ≤ Ktw (fun X Y:leaf A=>P X* V Y) X + Kth (fun X Y Z:leaf A=> P X * V Y * V Z) X:=by
 intro V; let f:=mintA t i; unfold ΦD; rw [mintP, show mintL i t (αD F P X)=_ from (KtwP f (fun X Y=>P X • F Y) X),show mintL i t (βD F P X)=_ from (KthP f (fun X Y Z=>P X • (F Y*F Z)) X)] -- syntax
 have he(X Y:leaf A): f (P X • F Y)=P X* V Y:= mint_v ..
 simp_rw [he]; refine add_le_add_right ?_ _; apply sum_le_sum; intro X _; apply sum_le_sum; intro Y _; apply sum_le_sum; intro Z _; split_ifs; exact (mint_v (P X) i t (F Y*F Z)).trans_le ((mul_le_mul_of_nonneg_left (cent.tend _ (h _) (h _) p) (v _)).trans_eq (mul_assoc ..).symm); rfl
-- coherent Timer.Scope. Supplies trunk budgets for full curves incl secondary derivative powers; K assumed per-seat. F inputs major. Parameters choose Lα,μappa independent.x Budget pay_M.S with $K_α as Phys in PhiD (absorbs 6 already). Norm integrality for der.
local notation "co" X:max=> Cadre.spark X
abbrev mintL3 (P V:leaf A→ℝ) := (Ktw (fun X Y=>P X * V Y))+(Kth (fun X Y Z=>P X* V Y* V Z))
structure Tax_R (F:leaf A→ PS)(P:leaf A→ℝ)(v:leaf A→ℝ)(b L w a c d e:ℝ):Prop where
 grade: ∀ X:leaf A, cent (F X)
 merits:P≥0
 veil:Tour v b
 height: 0 ≤ b
 vita: w>0
 rent:0 ≤ L-w*2
 ignite: 0<a
 ask: 0 ≤d
 ask2:0 ≤ c
 boot:∀ i:A,nook (ϕV F 0 0 * loom_v L w v 0) i < a
 past:∀ X:leaf A, ∀ i:ℕ, coeff i (derivative ℝ (F X)) ≤ coeff i (PowerSeries.C (P X)+ΦD F P X)
 cash:∀ i:A, nook (P * loom_v L w v 0) i ≤ c
 town:∀ i:A, shelfR (P * loom_v L w v 0) i ≤ d
 bill:∀ i:A,Hiκ P (loom_v L w v 0) i ≤ e
 slope:b*(c+2*a*d) ≤ w
 value: c+d*a+e*a*a < (w-b*(c+2*a*d))*a
namespace Tax_R
variable {F P v} {ℓ w' a c d e b':ℝ}(T:Tax_R F P v b' ℓ w' a c d e)
abbrev countΨ(v:leaf A→ℝ)(L w:ℝ)(t:ℝ)(i:ℕ)(F:leaf A→PS)(o:A):=nook (ϕV F t i *loom_v L w v t) o
local notation "ΣZ" i:max t:max o:max=>countΨ v ℓ w' t i F o
variable {v0:ℝ}
include T
lemma αxp (X:leaf A)(t:ℝ)(v_:t∈Set.Icc (0:ℝ) 2)(i:ℕ) : ϕY F t i X ≤ P X + mintL i t (ΦD F P X):=by
 apply (Cadre.trend v_.1 (T.past X) i).trans; rw [mintP, show mintL i t (PowerSeries.C (P X))=P X from ?_]; unfold mintL; simp_rw [coeff_C]; simp [mul_ite]
omit T
lemma meet_K (v:leaf A→ℝ)(U:Tour v b') (L w t:ℝ)(h:0 ≤ L-w*t)(X Y:leaf A)(p:Y∈ Cadre.blaze X): loom_v L w v t (αK X Y) ≤ loom_v L w v t X * loom_v L w v t Y:=by
 have he:{Y}∈drum (αK X Y) X ∅:=by apply (drum_p ..).mpr; have hp':= (mem_filter.mp p).2; simp [αK, flow, robe, hp']
 have hv:=U.loom _ _ _ he; unfold loom_v; rw [←Real.exp_add, ←mul_add]; rw [sum_singleton] at hv; exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hv h)
lemma ζpay(Q V:leaf A→ℝ)(p:0≤Q)(v:0 ≤ V)(e:ℝ)(t:∀ i:A,nook Q i ≤ e)(o:A): (∑ Y∈ spark o, V Y* ∑ Z∈Cadre.blaze Y,Q Z) ≤ shelfR V o *e:=by unfold shelfR; rw [sum_mul]; refine sum_le_sum fun i _=> (mul_le_mul_of_nonneg_left (beam i Q p _ fun y _=>t y) (v i)).trans_eq (mul_assoc ..).symm
include T
lemma αr_v(o:A)(t:ℝ)(g:t∈Set.Icc 0 2)(i:ℕ)(H:∀ o:A,countΨ v ℓ w' t i F o ≤ a):let W:= loom_v ℓ w' v t; let V:=ϕV F t i; nook (mintL3 P V * W) o ≤ d*a + e*a*a + (c+2*a*d) * shelfR (V*W) o:=by -- tune mint.P_Q
 intro X V; let L:=X; let Y:=loom_v ℓ w' v 0; have hx: 0 ≤ X:=fun i=>Real.exp_pos ..|>.le; have hp:= T.merits; have hX:X≤ Y:=fun j=> tap ℓ w' v T.veil T.vita.le g.1 j -- signature
 have ht:T.vita.le=T.vita.le:=rfl; have hn:0 ≤ V:=fun i=> (T.grade _).negℜ _ g.1 _
 have hb:0≤ V*X:=fun i=>mul_nonneg (hn i) (hx i); have hu:0 ≤ P*X:=fun i=>mul_nonneg (hp _) (hx _); have hr:P*X ≤ P*Y:=fun j=>mul_le_mul_of_nonneg_left (hX j) (hp j)
 have hR(j:A):nook (P*X) j ≤ c:=(sum_le_sum fun i _=> hr i).trans (T.cash _)
 have hh(j:leaf A):0 ≤HiΦ P X j:= mul_nonneg (hu _) (Nat.cast_nonneg _)
 have hg(j:leaf A):HiΦ P X j ≤ HiΦ P Y j:=mul_le_mul_of_nonneg_right (hr j) (Nat.cast_nonneg _)
 have hi(j:A):shelfR (P*X) j ≤ d:=(sum_le_sum (fun i _=>hg i)).trans (T.town _)
 have h0:ℓ-w'*t≥0:=by nlinarith [g.2,T.rent,T.vita]
 have he(X Y: leaf A)(p:Y∈Cadre.blaze X):=meet_K v T.veil ℓ w' t h0 X Y p
 have hw:=T.ignite.le; have hrp: Hiκ P X o ≤ e:= (sum_le_sum (fun i _=>mul_le_mul_of_nonneg_right (hg i) (Nat.cast_nonneg _))).trans (T.bill _)
 let W:= Ktw (fun i j:leaf A=> P i*V j); let R:= Kth (fun i j k:leaf A=>P i*V j*V k)
 have hv1:nook (W*X) o ≤ d*a + shelfR (V*X) o*c:= (bud_V o P V X hp hn hx he H).trans (add_le_add (mul_le_mul_of_nonneg_right (hi o) hw) (ζpay _ _ hu hb c hR o))
 have hv2:nook (R*X) o ≤ e*a*a+ 2*a*(shelfR (V*X) o*d):=(trio_X o P V X hp hn hx he H hw).trans (add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hrp hw) hw) (mul_le_mul_of_nonneg_left (ζpay _ _ hh hb d hi o) (by positivity)))
 change nook ((W+R)*X) _ ≤ _; rw [add_mul]; refine le_trans ?_ ((add_le_add hv1 hv2).trans_eq (by ring)); unfold nook; rw [←sum_add_distrib]; exact le_rfl
lemma ρlife(o:A)(t:ℝ)(X:t∈Set.Icc (0:ℝ) 2)(i:ℕ) : countΨ v ℓ w' t i F o < a:=by
 let V(t:ℝ)(X:leaf A):=loom_v ℓ w' v t X
 let W(t:ℝ)(i:ℕ):=ϕV F t i* V t; let B(t:ℝ)(i:ℕ)(o:A):=countΨ v ℓ w' t i F o; have hp:=T.merits; have he(t:ℝ):0≤ V t:=fun i=>Real.exp_pos ..|>.le
 have hv(t:ℝ)(u:0 ≤ t)(i j:ℕ)(z:i ≤ j):W t i ≤ W t j:=fun X=>mul_le_mul_of_nonneg_right ((T.grade X).kind z u) (he t _)
 apply lt_of_le_of_lt (sum_le_sum (fun j (_:j∈spark o)=> hv t X.1 i (i+1) (by omega) j)) -- tune
 let D(t:ℝ):= ϕY F t i * V t; let Z(t):= W t (i+1)*v; refine carom 2 a (fun j t=>B t (i+1) j) (fun j t=> nook (D t) j-w'* nook (Z t) j) (fun j t=>?_ ) ?_ ?_ _ _ X
 · have hq(u:leaf A):HasDerivAt (fun t=>W t (i+1) u) (D t u - w'*Z t u) t:=by apply ((cent.lead (F u) i t).mul (zerk ℓ w' v u t)).congr_deriv; change _= mintL i t _ * V t u-w'*(mintL (i+1) t _ * V t u*v u); unfold V; ring
   apply (HasDerivAt.fun_sum (fun i (_:i∈spark j)=>hq i)).congr_deriv; unfold nook; rw [sum_sub_distrib, mul_sum]
 · intro j; refine Eq.trans_lt ?_ (T.boot j); unfold B countΨ nook; change ∑ X∈spark j,ϕV F 0 (i+1) X* V 0 X=_; simp_rw [Pi.mul_apply,ϕV,car_k]; rfl
 intro j f u g p; have hm(o:A):B f i o ≤ a:=(sum_le_sum (s:=spark o) fun k _=>hv _ u.1 i (i+1) (by omega) k).trans (p _)
 have ht':= αr_v T j f u i hm
 let V':=ϕV F f i; have hl(Dx:leaf A): ϕY F f i Dx ≤ P Dx+mintL3 P V' Dx:= (αxp T Dx f u i).trans (add_le_add_right (Φcash F P Dx f i T.grade hp u.1) _)
 let Y:=loom_v ℓ w' v 0; let F_:=shelfR (W f i) j
 have h':nook (D f) j ≤ nook (P*Y) j+nook (mintL3 P V'*V f) j:=by unfold nook; rw [←sum_add_distrib]; apply sum_le_sum; intro k _; refine (mul_le_mul_of_nonneg_right (hl k) (he _ _)).trans ?_; rw [add_mul]; exact add_le_add_left (mul_le_mul_of_nonneg_left (tap ℓ w' v T.veil T.vita.le u.1 k) (hp k)) _
 let a':=nook (Z f) j
 have hz: 0≤ W f (i+1):=fun k=>mul_nonneg ((T.grade _).negℜ _ u.1 _) (he _ _)
 have hK:a ≤ a':=Eq.trans_le g.symm (sum_le_sum fun k _=>le_mul_of_one_le_right (hz k) (T.veil.pos k))
 have hf: F_ ≤ b'* a':=by unfold F_ a' shelfR nook; rw [mul_sum]; exact sum_le_sum (fun k _=> (mul_le_mul (hv _ u.1 _ _ (by omega:i ≤ i+1) k) (T.veil.rate _) (Nat.cast_nonneg _) (hz k)).trans_eq (by unfold Z; rw [Pi.mul_apply]; ring))
 apply sub_neg.mpr; have hC:=h'.trans (add_le_add (T.cash _) ht')
 have hu:0 ≤ c+2*a*d:= add_nonneg T.ask2 (mul_nonneg (mul_nonneg (by norm_num) T.ignite.le) T.ask)
 have hp:=T.value; let A':= c+2*a*d
 change nook (D f) j ≤ c+ (d*a+e*a*a+A'* F_) at hC; nlinarith only [hC,T.slope,hp,mul_le_mul_of_nonneg_left hf hu, mul_le_mul_of_nonneg_left hK (sub_nonneg.mpr T.slope)] -- tune defeq a'
end Tax_R
end YM.CF.Leaf
