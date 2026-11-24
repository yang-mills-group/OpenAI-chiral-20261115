import YM.SU5.Selected.Time.Prom
import Mathlib.Algebra.Star.UnitaryStarAlgAut
/-! # Real-time unitary *-motion & chronometer for time-slab envelopes

Act by conjugation on width-operators, before trying to qualify them as spacetime-local.
Spectrum condition in time ONLY. Flight path takes array controls of points at time-head;
records *gaps*, Euclid -> add imaginary, Mink sign convention +i*t. Parameter base t=0 a gauge.
No Norm topology of U(t). Strong continuity of these moments, no contact limit assumptions.
-/
set_option autoImplicit false
set_option maxHeartbeats 280000
set_option quotPrecheck false
noncomputable section
namespace YM.Spectral.Alps
open Function Filter Real Set Complex Analysis Boundary Probe OS.Semigroup
open scoped NNReal ENNReal Topology InnerProductSpace BigOperators ComplexOrder
variable {H:Hilbert}{a:Axis}(S:OS.Semigroup H a)
local notation "E"=> S.E
local notation "U"=> S.edge
variable {X:Type*}
private lemma balances (t:ℝ) : star (U t)=U (-t):=by
 have he : star (U t)*U t=1:= (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).1 (S.life t)
 have ht: U t*U (-t)=1:= (S.send ..).trans ((congrArg S.edge (add_neg_cancel t)).trans S.birth)
 calc star (U t)= (star (U t)*U t)*U (-t):=(by rw [mul_assoc,ht,mul_one])
      _= _:= by rw [he,one_mul]
def ascends (t:ℝ) : unitary H.Op:=by
 have h: U t∈unitary H.Op:=by
    have he(z:ℝ)(x:ℝ) : U z*U x=U (z+x):= S.send ..; have h0:U 0=1:=S.birth
    exact ⟨by rw [balances,he,neg_add_cancel,h0],by rw [balances,he,add_neg_cancel,h0]⟩
 exact ⟨U t,h⟩
noncomputable def conduct (t:ℝ) : H.Op ≃⋆ₐ[ℂ] H.Op:= Unitary.conjStarAlgAut ℂ H.Op (ascends S t)
local notation "α"=> conduct S
lemma system (t:ℝ)(A:H.Op): α t A=U t*A*U (-t):=by unfold conduct; rw [Unitary.conjStarAlgAut_apply, show star _=_ from (show star ((ascends S t : unitary H.Op): H.Op)= U (-t) from balances S t)]; rfl -- maybe star (submonoid) vs star coerces
lemma earnest(z:ℝ)(A:H.Op)(x:H): α z A (U z x)= U z (A x):=by
 rw [system, mul_assoc]; change U z (A (U (-z) (U z x)))=_; rw [← ContinuousLinearMap.comp_apply (U (-z)),send,neg_add_cancel,S.birth]; rfl
lemma conducts (t u:ℝ)(A:H.Op): α t (α u A)=α (t+u) A:=by
 unfold conduct; rw [← Unitary.conjStarAlgAut_mul_apply]; exact congrArg (fun Z: unitary H.Op=> Unitary.conjStarAlgAut ℂ H.Op Z A) (Subtype.ext (S.send t u))
lemma mandate(A:H.Op): α 0 A=A:=by rw [system, neg_zero,show U 0=1 from S.birth]; simp -- gauge predicate
lemma equality (B:H.Op)(x:H)(t:ℝ): ‖U t (B x)‖=‖B x‖:=S.life .. -- syntax
lemma group_pay (v: ℝ) (x y:H) : inner ℂ (U v x) (U v y)=inner ℂ x y:= (LinearMap.norm_map_iff_inner_map_map (U v).toLinearMap).mp (S.life v) x y
variable (x y:H) (hx : x∈S.ground)
include hx
lemma occupied (t:ℝ)(A:H.Op) : α t A x=U t (A x):=(congrArg (α t A) (mink_invar S x t hx).symm).trans (earnest S t A x)
lemma letter_expect (A:H.Op)(t:ℝ): inner ℂ x (α t A x)= inner ℂ x (A x):= by rw [occupied S x hx]; exact (congrArg (fun u:H=>inner ℂ u (U t (A x))) (mink_invar S x t hx).symm).trans (group_pay S t ..)
omit hx
-- strong continuity lemma for balcony (H-valued with any domain). Inputs real etc via restrictions.
lemma turgid [TopologicalSpace X] (f:X→ℂ)(t:X→H) (p:Continuous f)(h:Continuous t) : Continuous (fun z=> balcony S (f z) (t z)):=by
 apply continuous_iff_continuousAt.mpr; intro x
 apply Metric.tendsto_nhds.mpr; intro ε he; let u(i):=balcony S (f i); have ht: Continuous (fun i=> u i (t x)):= (balcony_cont S _).comp p
 filter_upwards [Metric.tendsto_nhds.mp (h.tendsto x) (ε/2) (by positivity),Metric.tendsto_nhds.mp (ht.tendsto x) (ε/2) (by positivity)] with i hi v
 apply lt_of_le_of_lt (dist_triangle _ (u i (t x)) _) -- half
 have h' : dist (u i (t i)) (u i (t x)) ≤ dist (t i) (t x):=by rw [dist_eq_norm, dist_eq_norm,← map_sub]; exact ((u i).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (balcony_pay ..)) -- stuck q
 change dist (u i (t i)) (u i (t x))+dist (u i (t x)) (u x (t x)) < ε
 change _ < ε/2 at v; linarith only [hi,h',v]
lemma conduct_cont(A:H.Op): Continuous (fun z:ℝ=> α z A x):=by
 simp_rw [system]; exact S.cont_edge (fun z:ℝ=> A (U (-z) x)) id (A.continuous.comp ((S.cont x).comp continuous_neg)) continuous_id -- defeq might heavy
-- Gap clock with arbitrary registry. Before each letter, allocate time gap.
variable {d:Type*}(f:d→ H.Op)
noncomputable def trip : List d→(d→ℂ)→ H.Op
| [],_=>1
| i::L,z=> balcony S (z i) * f i * trip L z
noncomputable def account (F: H.Op)(Q:H):=inner ℂ Q (F Q) -- notation
variable (i:List d)
local notation "ρ"=> trip S f
lemma flight : ∀ p:d→ℂ, ‖ρ i p‖ ≤ (i.map (fun i=>‖f i‖)).prod:=by
 intro p; induction i with| nil=> exact ContinuousLinearMap.norm_id_le -- search
                           | cons a i h=> unfold trip; rw [List.map_cons,List.prod_cons]; refine (norm_mul_le ..).trans (mul_le_mul ((norm_mul_le ..).trans (mul_le_of_le_one_left (norm_nonneg _) (balcony_pay ..))) h (norm_nonneg _) (norm_nonneg _)) -- idem
lemma flight_cont : Continuous (fun z:d→ℂ=> (ρ i z) x):=by
 induction i with
 | nil=> exact continuous_const
 | cons a i h=> change Continuous (fun z:d→ℂ=> (balcony S (z a)) (f a (trip S f i z x))); exact turgid S _ _ (continuous_apply a) ((f a).continuous.comp h)
-- product norm analytic interior, no claims off imaginary ordering requirements. Can include arbitrary insertion in middle of another word across product plumbing
lemma flight_yes [Fintype d] (p:d→ℂ)(h:∀ v∈i, 0<(p v).im): AnalyticAt ℂ (ρ i) p:=by
 induction i with
 | nil=> exact analyticAt_const
 | cons a i u=> let L : (d→ℂ)→L[ℂ] ℂ:=ContinuousLinearMap.proj a; exact ((((balcony_holo S _ (h a List.mem_cons_self)).comp (f:=L) (L.analyticAt p)).mul analyticAt_const).mul (u fun z t=> h _ (List.mem_cons_of_mem _ t)))
lemma unite (a b:List d)(p:d→ℂ): trip S f (a++b) p= trip S f a p * trip S f b p:=by induction a with|nil=> rw [List.nil_append, trip, one_mul]|cons a l v=>rw [List.cons_append,trip,v,trip,mul_assoc]; simp only [mul_assoc]
-- real Mink chronology with cumulative times, no shift if no gap. symbol A. Base coadj stationary. B(t) first gap preceded, last always. transport group. show matrix $<Ω U(path)Ω>$. General formula open endpoint x not necessarily Ω good.
noncomputable def arms (t:ℝ):List d→(d→ℝ)→ H.Op -- cannot recursive with t fixed? define differently.
| [],_=>1
| x::xs,p=> conduct S (t+p x) (f x)*arms (t+p x) xs p
include hx
lemma esplanade (t:ℝ) (p:d→ℝ): (arms S f t i p) x=U t ((trip S f i fun i=> (p i:ℂ)) x):=by
 induction i generalizing t with
 | nil=> exact (mink_invar S x t hx).symm
 | cons a i h=> let y:= (trip S f i fun i=> (p i:ℂ)) x; rw [arms,ContinuousLinearMap.mul_apply,h,trip]; rw [balcony_floor]; change α (t+p a) (f a) (U _ y)=U t (U (p a) (f a y)); rw [earnest,← ContinuousLinearMap.comp_apply (U t),send] -- orientation
lemma circuit(t:ℝ)(p:d→ℝ): inner ℂ x (trip S f i (fun i=> (p i:ℂ)) x)=inner ℂ x (arms S f t i p x):=by rw [esplanade S x hx]; nth_rw 3 [←mink_invar S x t hx]; exact (group_pay S t _ _).symm
omit hx
end YM.Spectral.Alps
open YM.Spectral.Alps
#print axioms turgid
#print axioms flight_cont
#print axioms flight_yes
#print axioms circuit
#print axioms flight
#print axioms earnest
#print axioms conducts
