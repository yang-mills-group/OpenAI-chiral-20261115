import Organdy.Cloche
import Organdy.Thistle
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option synthInstance.maxSize 24000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy.Royal
open Buffered Buffered.Afterglow
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Pastry Tenant Tower

open VacuumSelection


open Lamour.Bridge.Celeste Lamour.Bridge.Celeste.Clock
open CF.Pannier.Chancel Hookah Tapestry


/- General pricing after arbitrary thaws on the *same* RateNet. -/
section
variable {N:Side} {G:Club N}
abbrev sizeN(N:Side) :=(More N).val^4
abbrev spread (K:Calibration)(w:ℕ):=4*(w+addgap K)
def dense(K:Calibration)(w:ℕ)(L:List (Hookah N)):Prop:=
  L.length≤ sizeN N ∧ sizeN N≤ L.length*(spread K w)^4

structure Sustained (K:Calibration)(w p:ℕ)(G:Club N)(v:Mark N→ℂ)
    (T M:ℝ):Prop where
 bound (A:Hookah N):G.accepts A→∀ x,‖A.x x‖≤ M
 invoice (L:List (Hookah N)):Romp G p L→dense K w L →‖v (buffet L)‖≤T^L.length

variable {K:Calibration}{w p:ℕ}{v:Mark N→ℂ}{T M e:ℝ} (V:Sustained K w p G v T M)
include V in
lemma fringe (a:0 ≤ M){L:List (Hookah N)}
 (f:Romp G p L)(x:Fields N):
 ‖buffet L x‖ ≤M^L.length:=by
 induction L with
 | nil=>rw [buffet_empty,List.length_nil,pow_zero,Pi.one_apply];exact norm_one.le
 | cons Y Z ih=>
    rw [buffet_more,Pi.mul_apply,List.length_cons,pow_succ']
    exact (norm_mul_le ..).trans (mul_le_mul (V.bound _ (f.core _ List.mem_cons_self) x)
       (ih ⟨fun r h=> f.core r (List.mem_cons_of_mem _ h),(List.pairwise_cons.mp f.annex).2⟩) (norm_nonneg _) a)


def freed(T M:ℝ)(N:Side):= (min 1 T)^sizeN N/M^(sizeN N)
lemma freed_pos(a:0<T)(b:0<M):0<freed T M N:=div_pos (pow_pos (lt_min one_pos a) _) (pow_pos b _)
include V
lemma efflorescent {m:Side}
 (a:0<T) (b:1≤M) (u:0<e)
 (g:N=K.c m){ν:Mark N→ℂ} (h:Twosome K N ν)
 (thaw:∀ f:Mark N, Envelope f → ∀ C:ℝ,(∀x,‖f x‖≤ C)→‖v f-ν f‖ ≤ (e*freed T M N)*C)
 (j:Axis)
 {L:List (Hookah N)}(f:Romp G p L)
 (r:ℕ)(c:L.length=2^r)(hh:(2^r)*(w+addgap K)≤N.val)
 {d:ℕ}(q:d+addgap K=2^r*(w+addgap K))
 (z:cows j (Broad p L) d)
 (z':∀i,i≠j→cows i (Broad p L) w):
   ‖v (buffet L)‖ ≤ (1+2*e)*T^(2^r):=by
 obtain ⟨J,R,S,H,k,k0,t,Q⟩:=champagne h g j L f r c hh z' q z
 have A:=V.invoice J R ⟨S,H⟩
 have hM:=zero_lt_one.trans_le b
 have X(P)(p₀:Romp G p P)(h₀:P.length≤ sizeN N):
    ‖v (buffet P)-ν (buffet P)‖ ≤ e*T^P.length:=by

     refine (thaw _ p₀.occupy.env _ (fun i=> (fringe V hM.le p₀ i).trans
       (pow_le_pow_right₀ b h₀))).trans ?_
     unfold freed
     rw [mul_assoc,div_mul_cancel₀ _ (pow_pos hM _).ne']
     have q:0≤ min 1 T:= le_min zero_le_one a.le
     exact mul_le_mul_of_nonneg_left ((pow_le_pow_of_le_one q (min_le_left ..) h₀).trans
       (pow_le_pow_left₀ q (min_le_right ..) _)) u.le
 have e1: 1+e≤(1+e)^k:=by simpa using pow_le_pow_right₀ ((le_add_of_nonneg_right u.le):1≤1+e) (show 1≤k from k0)
 have hw: ‖ν (buffet J)‖ ≤ ((1+e)*T^L.length)^k:=by
     have p:=norm_le_norm_sub_add (ν (buffet J)) (v (buffet J)); rw [norm_sub_rev] at p
     rw [mul_pow,←pow_mul,mul_comm L.length,←t]
     exact p.trans ((add_le_add (X J R S) A).trans (by rw [add_comm,←one_add_mul]; exact mul_le_mul_of_nonneg_right e1 (pow_nonneg a.le _))) -- one_add_mul? one_add_mul gives (1+e)y=y+e*y
 have h₂:= (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity:0≤(1+e)*T^L.length) k0.ne').mp (Q.trans hw)
 have h₃:=X L f ((Nat.le_mul_of_pos_left L.length k0).trans (t.ge.trans S))
 refine (norm_le_norm_sub_add _ (ν (buffet L))).trans ((add_le_add h₃ h₂).trans ?_)
 rw [c]; exact (le_of_eq (by ring))
end

variable {I:Type}{l:Filter I}[l.NeBot]{P:Spine}{s:ℕ}{j:Axis}
 {i k:I→ℕ}
 {G: Clubs P s i}
 {w p:ℕ}
abbrev take(P:Spine)(s i k:ℕ) := Journey.compass P.run i k s

abbrev Rendered (l:Filter I) (P:Spine) (s:ℕ) (i k:I→ℕ)
 (w p:ℕ)(G:Clubs P s i)
 (r:ℝ):Prop:=
 ∃ M,1≤M∧∀ᶠ z in l, Sustained P.calibration w p (G z) (take P s (i z) (k z)) (Real.exp r) M

local notation "H"=>P.calibration
variable (R:RateNet l P i k)
open Py.Rate.LocalLimit.Papal
include R
theorem fabulous {r:ℝ}
 (h:Rendered l P s i k w p G r):Fitted l j w p G r:=by
 intro n b d S L F g C
 let Y:=P.run
 let T:=Real.exp r
 have t:0<T:=Real.exp_pos _
 let N (v:ℕ):=side P.run v s
 obtain ⟨M,u,v⟩:=h
 have z(a:ℝ)(e:0<a): ‖P.E s g.val‖ ≤ (1+2*a) * T^(2^n):=by
    apply le_of_tendsto (C.price.pays R).norm
    let D:=w+addgap P.calibration
    let E(j):= a*freed T M (N j)

    let U (i k:ℕ):Prop:= ∃ h:Ferry Y s i k,2^n*D ≤ (N i).val ∧
      ∀ f:Mark (N i),Envelope f → ∀ c:ℝ, (∀ x,‖f x‖≤ c)→‖take P s i k f-solder Y i k h.depth s f‖≤E i*c

    have E1(j):0<E j:=mul_pos e (freed_pos t (zero_lt_one.trans_le u))
    have f:∀ᶠ z in l,U (i z) (k z):=
      R.both (B:=U)
       (((count_grows Y s).eventually_ge_atTop (2^n*D)).mono fun i h=>
        ((ferry_later Y s i).and (thaw_plot Y _ (E1 i) s)).mono fun _ ⟨u,v⟩=> ⟨u,h,fun a b c=> v i u.depth a c b⟩)
    filter_upwards [v,f,C.scheduled] with x h ⟨q,l,t'⟩ ⟨w,r,y,z⟩
    exact efflorescent h t u e (patronise P s i x).symm (revive Y P.large s _ _ q) t' j w n r l C.width ⟨b,y⟩ z

 let f(a:ℝ):=(1+2*a)*T^(2^n)
 have q:Continuous f:=by unfold f;fun_prop
 have q': Tendsto f (𝓝[>] 0) (𝓝 (f 0)):= q.continuousWithinAt
 have h:=ge_of_tendsto q'
    (show ∀ᶠ x in 𝓝[>] 0, ‖P.E s g.val‖ ≤ f x from (eventually_mem_nhdsWithin).mono (fun x=> z x))
 simpa only [f,mul_zero,add_zero,one_mul] using h
#print axioms fabulous
