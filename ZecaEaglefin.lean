import ZecaMarlin
set_option autoImplicit false
set_option maxHeartbeats 220000
noncomputable section

namespace YM.ZecaSky
open Function Metric Filter Asymptotics Set
open scoped ComplexOrder InnerProductSpace BigOperators Topology


variable {h q E:ℝ}{H:Type*}[NormedAddCommGroup H][InnerProductSpace ℂ H]
variable {U V:H→L[ℂ]H} {x:ℕ→ℤ→H}

/-- cone tap: see the construction notes. M arbitrary; compatible estimates suffice -/
structure Bask(h q E:ℝ)(U V:H→L[ℂ]H) (M:H→ℝ) : Prop where
 tab:∀v,M v ≤ ‖v‖
 space:∀v,h*q*M v ≤ M (U v - v)
 heat:∀v,Real.exp (-E) * M v ≤ M (V v)

structure Race(U V:H→L[ℂ]H)(x:ℕ→ℤ→H) : Prop where
 glide:∀t l, U (x t l)=x t (l+1)
 dwell:∀t, V (x t 0)=x (t+1) 0

lemma Race.strokes (r: Race U V x)(t k:ℕ) (l:ℤ):
 U (splashing (x t) k l)=splashing (x t) k (l+1):=by
 induction k generalizing l with
 | zero=> exact r.glide t l
 | succ k y=> rw [splashing,map_sub,y,y]

lemma Race.hatches (r: Race U V x)
 (hp:0<h)(qp:0<q) {M:H→ℝ} (y:Bask h q E U V M) (k t:ℕ):
 Real.exp (-E*t)*(h*q)^k*M (x 0 0) ≤ M (splashing (x t) k 0):=by
 induction k with
 | zero=>
    rw [pow_zero,mul_one,splashing]
    induction t with
    | zero=> simp
    | succ t a =>
       rw [← r.dwell]
       refine le_trans ?_ (y.heat _)
       refine le_trans ?_ (mul_le_mul_of_nonneg_left a (Real.exp_nonneg _))
       rw [← mul_assoc,← Real.exp_add]; push_cast;ring_nf; exact le_rfl
 | succ k a =>
    simp only [splashing]; rw [← r.strokes t k 0]
    refine le_trans ?_ (y.space _)
    exact (le_trans (le_of_eq (by rw [pow_succ];ring)) (mul_le_mul_of_nonneg_left a (mul_pos hp qp).le))

theorem eaglefin {U V:ℕ→H→L[ℂ]H}{x:ℕ→ℕ→ℤ→H}
 (coast:fishing x h) (y:∀i,Race (U i) (V i) (x i))
 (a:0≤E)(w:E<q){e:ℝ}(r:0<e):
 ∀ᶠ i in atTop, ∀M:H→ℝ, Bask h q E (U i) (V i) M →
   M (x i 0 0)<e :=by
 obtain ⟨t,k,z⟩:=marlin a w r coast
 have qp:=a.trans_lt w
 have hp:=coast.1
 filter_upwards [z] with i s M m
 by_contra! l
 have p:=((y i).hatches hp (a.trans_lt w) m k t).trans (m.tab _)
 exact s.not_ge ((mul_le_mul_of_nonneg_left l (by positivity)).trans p)
#print axioms eaglefin
