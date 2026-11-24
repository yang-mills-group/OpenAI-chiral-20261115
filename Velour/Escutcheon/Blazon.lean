import Velour.Damask.Plume
import Velour.Escutcheon.Leaves
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 2800
noncomputable section
namespace YM.OS.Semigroup
open Function Set Filter Complex Analysis MeasureTheory
open scoped NNReal ENNReal Topology BigOperators ContDiff InnerProductSpace ComplexOrder
variable {H : Hilbert} {a : Axis} (S:Semigroup H a)


open Boundary Probe
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin

open YM.Damask

variable {S}{H':Hilbert}{b:Axis}{T:Semigroup H' b}
variable {κ:Type}(L:S.Livery κ)(J:T.Livery κ)
   (h:a≠b)(A:S.Tiles h)(B:T.Tiles (Ne.symm h))
variable {n:ℕ}
local notation "ℓ"=> Fin n→ℝ
local notation "ℒ"=> Fin n→ℂ
local notation "σ"=> Equiv.Perm (Fin n)
variable (u:Fin n→κ)(X:Fin n→E4)
namespace Livery
local notation "R"=>L.penny h A u X
local notation "Q"=>J.penny h.symm B u X


private lemma shines (e:ℕ)(hv:L.modes u≤e)(g:σ)(U:ℝ→ℓ)(Z W:ℂ→ℒ)
   (cont:∀i,Continuous (fun y=>U y i))
   (bid:∀z i j,U z.re i≤U z.re j→
       Real.exp |z.im| * ((Z z j-Z z i).re-|(W z j-W z i).im|)=U z.re j-U z.re i)
   (hz:∀z i, AnalyticAt ℂ (fun w=>Z w i) z)
   (hw:∀z i,AnalyticAt ℂ (fun w=>W w i) z)
   (x:ℝ)(p:StrictMono (U x ∘g)):
   (∀ᶠ y in 𝓝 x,StrictMono (U y ∘g)) ∧
   (∀z:ℂ,z.re=x→ AnalyticAt ℂ (fun w=>R g (Z w) (W w)) z) ∧
    ∃c:ℝ,∀ᶠ y in 𝓝 x, ∀z:ℂ,z.re=y→ ‖R g (Z z) (W z)‖≤ c*Real.exp |z.im| ^ e :=by
 obtain ⟨d,t,r⟩:= ladders (T:= fun y=>U y ∘ g) p (fun i=>(cont _).continuousAt)
 have M:∀ᶠ y in 𝓝 x,StrictMono (U y ∘ g):= r.mono fun y u i j h=>sub_pos.mp
       (t.trans (u _ _ h))
 have hc:∀ᶠ y in 𝓝 x,∀z:ℂ,z.re=y→Chipped g d (Real.exp |z.im|) (Z z) (W z):=by
   filter_upwards [M,r] with y a b z f i j k
   subst y
   dsimp only [comp_apply]
   rw [bid _ _ _ (a k).le]
   exact (b _ _ k).le
 obtain ⟨c,w,l⟩:= L.shellac h A u X g _ t
 refine ⟨M,fun z a=> L.penny_marble h A u X g Z W _
   ((hc.self_of_nhds z a).pay t (Real.exp_pos _)) (hz _) (hw _),c,hc.mono fun y b z a=>?_⟩
 have N:=Real.one_le_exp (abs_nonneg z.im)
 refine (l _ N _ _ (b z a)).trans ?_
 gcongr


def ringCost :ℕ:= max (L.modes u) (J.modes u)
def active (t s:ℓ) : σ ⊕ σ → ℝ → Prop :=
 Sum.elim (fun g x=>StrictMono (rows t s x ∘ g)) (fun g x=>StrictMono (cols t s x ∘ g))

def bill (t s:ℓ): σ ⊕ σ → ℂ → ℂ :=
 Sum.elim (fun g z=> R g (φ t s z) (ψ t s z)) (fun g z=>Q g (ψ t s z) (φ t s z))


local notation "Rc"=>L.ringCost J u
lemma blazed (t s:ℓ)(p:Oblique t s)(v:Pact L J):
 Panels (active t s) (L.bill J h A B u X t s) Rc:=by
 have pay:∀i x, active t s i x→
     (∀ᶠ y in 𝓝 x,active t s i y) ∧
     (∀z:ℂ,z.re=x→ AnalyticAt ℂ (L.bill J h A B u X t s i) z) ∧
     ∃c:ℝ,∀ᶠ y in 𝓝 x,∀z:ℂ,z.re=y→
     ‖L.bill J h A B u X t s i z‖ ≤ c*Real.exp |z.im| ^ Rc :=by
    rintro (i|i)
    · exact shines L h A u X Rc (le_max_left ..) i _ _ _
       (fun j=> by unfold rows wide; fun_prop) (row_bids t s)
       (fun z j=>(wafts t s z j).1) (fun z j=>(wafts t s z j).2)
    exact shines J h.symm B u X Rc (le_max_right ..) i _ _ _
       (fun j=> by unfold cols tall; fun_prop) (col_bids t s)
       (fun z j=>(wafts t s z j).2) (fun z j=>(wafts t s z j).1)
 refine {
    cover:=fun x=>?_
    localize:=fun i x t=>(pay _ _ t).1
    meet:=fun x=>?_
    period:=fun x=>?_
    beams:= fun i z t=>(pay _ _ t).2.1 z rfl
    spends:=fun i x t=>(pay _ _ t).2.2
 }
 · rcases slopes _ _ p x with y|y
   · obtain ⟨g,u⟩:=permuting y; exact ⟨Sum.inl g,u⟩
   obtain ⟨g,u⟩:=permuting y; exact ⟨Sum.inr g,u⟩
 · rintro (f|f) (g|g) a b
   · rw [neat (s:=rows t s x) (g:=f) (f:=g) a b]
   · change R _ _ _ = Q _ _ _
     rw [(spun t s x).1,(spun t s x).2]
     exact L.swap_coin J h A B u X v f g _ _ a b
   · change Q _ _ _= R _ _ _
     rw [(spun t s x).1,(spun t s x).2]
     exact (L.swap_coin J h A B u X v g f _ _ b a).symm
   rw [neat (s:=cols t s x) (g:=f) (f:=g) a b]
 rintro (f|f) a
 all_goals simp only [active,bill,Sum.elim_inl, Sum.elim_inr] at *
 all_goals rw [(spun _ _ _).1,(spun _ _ x).1,(spun _ _ _).2,(spun _ _ x).2,(ran t s x).1,(ran t s x).2] 
 all_goals exact ⟨a,rfl⟩
#print axioms blazed


def sweeping (t s:ℒ)(r:ℝ):ℒ:=fun i=>cos (risen r)*t i - sin (risen r)*s i
def samite (t s:ℒ)(r:ℝ):ℒ:=fun i=>sin (risen r)*t i + cos (risen r)*s i
/-- Take an imaginary angle with input axes a,b arrays. -/
def drifts (t s:ℒ)(r:ℝ):ℂ:= R 1 (sweeping t s r) (samite t s r)

lemma samite_warm (t s:ℒ)(r:ℝ)(p:StrictMono (re ∘ t))
 (q:∀i,(s i).im=0) :
 Radial (sweeping t s r) (samite t s r):=by
  intro i j v
  have u:(t i).re < (t j).re:=p v
  unfold sweeping samite risen
  rw [sin_mul_I, cos_mul_I, ← ofReal_cosh, ← ofReal_sinh]
  simp [-ofReal_cosh,-ofReal_sinh,q]
  rw [←mul_sub,←mul_sub,abs_mul,abs_of_pos (sub_pos.mpr u)]
  apply mul_lt_mul_of_pos_right _ (sub_pos.mpr u)
  exact sub_pos.mp (pos_of_mul_pos_right 
    ((angular_price r).symm ▸ one_pos) (Real.exp_pos |r|).le)

lemma driftA (t s:ℂ→ℒ)(k:ℂ)
  (ct:∀i,AnalyticAt ℂ (fun z=> t z i) k)(cs:∀i,AnalyticAt ℂ (fun z=>s z i) k)
  (p:StrictMono (re ∘ t k))(q:∀i,(s k i).im=0)(r:ℝ):


 AnalyticAt ℂ (fun z=>L.drifts h A u X (t z) (s z) r) k:=
 L.penny_marble h A u X 1 (fun z=>sweeping (t z) (s z) r)
   (fun z=>samite (t z) (s z) r) k (samite_warm (t k) (s k) r p q)
   (fun i=>(analyticAt_const.mul (ct i)).sub (analyticAt_const.mul (cs i)))
   (fun i=>(analyticAt_const.mul (ct i)).add (analyticAt_const.mul (cs i)))

local notation "D"=> L.drifts h A u X

include B
lemma wisps (t s:ℓ)(p:Oblique t s)(r:Pact L J)(w:StrictMono t)
 (v:Rank Rc→ℝ)(y:Injective v)(a:ℝ):
 D (soaked t) (soaked s) a=
 ∑ i, hoops Rc (risen ∘ v) (risen a) i * D (soaked t) (soaked s) (v i):=by
 let k:=L.blazed J h A B u X t s p r
 have d(x:ℝ):k.chain (risen x)=D (soaked t) (soaked s) x:= by
    rw [k.chain_eq _ (Sum.inl 1)]
    · rfl
    change StrictMono (rows t s (risen x).re ∘ _)
    rw [show (risen x).re=0 from by simp [risen], stood]
    exact w
 rw [← d,k.studded.interp (risen ∘ v) (coin_inj.comp y)]
 simp_rw [comp_apply,d]


lemma orbiting (t s:ℓ)(r:Pact L J)(w:StrictMono t)
 (v:Rank Rc→ℝ)(y:Injective v)(a:ℝ):
 D (soaked t) (soaked s) a=
 ∑ i, hoops Rc (risen ∘ v) (risen a) i * D (soaked t) (soaked s) (v i):=by
 let l:=𝓝[>] (1:ℝ)
 haveI:NeBot l:= inferInstanceAs (NeBot (𝓝[>] (1:ℝ)))
 let b(z:ℂ): Fin n→ℂ:=fun i=>z*s i
 have bs:b 1=soaked s:= funext fun i=> one_mul _
 let f(c:ℝ):ℝ→ℂ:=fun x=>D (soaked t) (b x) c
 have tF(c): Tendsto (f c) l (𝓝 (D (soaked t) (soaked s) c)):=by
    have e:StrictMono (re ∘ soaked t):=by simpa only [Function.comp_def,soaked,ofReal_re]
    have q:= (L.driftA h A u X (fun _=>soaked t) b 1 (fun _=>analyticAt_const)
        (fun _=>analyticAt_id.mul analyticAt_const) e (fun i=>by rw [bs]; rfl) c).continuousAt
    rw [ContinuousAt] at q
    rw [bs] at q
    rw [← ofReal_one] at q
    exact q.comp ((continuous_ofReal.tendsto _).mono_left nhdsWithin_le_nhds)
 let g(x:ℝ):=∑ i, hoops Rc (risen ∘ v) (risen a) i * f (v i) x
 have tG:Tendsto g l (𝓝 _):=tendsto_finsetSum _ fun i _=> (tF (v i)).const_mul (hoops Rc (risen ∘ v) (risen a) i)

 refine tendsto_nhds_unique ((tF a).congr' ?_) tG
 filter_upwards [open_row t s w.injective] with x p
 have e:b x= soaked (fun i=>x*s i):=funext fun i=>(ofReal_mul _ _).symm
 unfold g f; rw [e]; exact L.wisps J h A B u X _ _ p r w v y a
#print axioms orbiting
