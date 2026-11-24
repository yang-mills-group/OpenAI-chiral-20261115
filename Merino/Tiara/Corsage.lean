import Merino.Tiara.Iridescent
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxRecDepth 2500
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Tiara
open Function Filter Metric SU Lat Lattice Cube Finset Spire Scroll Tulip Skye Window Vale Girt Buffered Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open BProof Hive Swell Hem Merino.Mitre Plume
open Afterglow Tower Lifted Journey

open Py.Rate.LocalLimit Preparation Tower.VacuumSelection
open Medal Lace Cuff Swell Hem
variable (P:Spine)(p:Bolts)(s i k:ℕ)
local notation "Ω"=>RegNum P s i
local notation "Γ"=>LedgerM P s i k
local notation "K"=> LoomM P s i

open scoped InnerProductSpace
variable {C:Constellation}
local notation "D"=> P.calibration
local notation "H"=> Lace.pole
local notation "n"=> (priceTick P)
local notation "x"=> (scaleM P s)
variable {r:ℕ→ℕ}(a:StrictMono r)
 {F:ℕ→LinksC→ℂ}{g:LinksC→ℂ}
 {X:ℕ→Reins P.calibration}{J:Reins P.calibration}
 (M:Carol P p C r s F g X J)

/-- Price inclination units: full gauge lag t, matter displacement t/2. -/
abbrev couch(t:ℕ):= balcony (etch P s) n H (t/2:ℕ)
abbrev toss(t:ℕ)(c:ℝ)(f:LinksC→ℂ)(j:Reins P.calibration)(σ:Signed):=
 scene D f j n σ c H (t/2:ℕ)
lemma pose (t:ℕ)(σ:Signed):crest H (t/2:ℕ) σ = (sun t σ:Sweep Ω):=rfl
section
variable {t:ℕ}(σ:Signed)
lemma front(c d:ℝ)(F:LinksC→ℂ)(j:Reins P.calibration):
 toss P t (c*d) F j σ=(c:ℂ) • toss P t d F j σ:=by unfold toss scene;rw [Complex.ofReal_mul,mul_smul,chime_scale]
include M
lemma joys:
 ∀c:ℝ, Elite (couch P s t) (fun u=>toss P t c (F u) (X u) σ) (toss P t c g J σ):=
 fun _=>excursus M.rail M.rolls ..

variable (f:ℕ)(w:
   ∀ᶠ i in atTop, ∀k, merrier P s i k →∀d t,Strut (scaleM P s) t→t%2=0→∀σ,Wickday P p f s i k d t σ)
-- x notation under variable binder dangerous (P-shadow); f binder?
include a w
private lemma aromaR (h:Strut x t)(e:t%2=0):
 let T:=toss P t (hueM P s) g J σ
 ‖P.E s (mirror D H 0 T*T)‖≤ mPrice (gold P s f):=by
 let z(u:ℕ):= toss P t (hueM P s) (F u) (X u) σ
 dsimp only
 have b:=(joys P p s M σ (hueM P s) (t:=t)).toBQueue
 refine le_of_tendsto (merino_coffee P.run P.large s P.history P.law r
   a.tendsto_atTop ((SlabMark.BQueue.revolve H 0 b).multiply b) |>.norm) ?_
 filter_upwards [M.fitted,a.tendsto_atTop.eventually (P.stockGo.eventually w)] with u j v
 obtain ⟨m,d,h1,h2,h3,h4,h5⟩:= j
 have y:=(nativeScene (F u) (X u) σ (sideVal P s (P.nomadic (r u))) H (t/2:ℕ) d.y d.ticket.hem
    (h5 σ) h4 (hueM P s))
 rw [d.leap,pose] at y

 let i:=P.nomadic (r u);let k:=P.engine (r u)
 let e':=sideVal P s i
 have hw{A B:Side}(e:A=B)(T:Mark A):ship e (photo T)=photo (ship e T):=by subst B;rfl
 change ‖compass P.run i k s (ship e' (photo (z u (momentm P.run i s))))‖≤_
 rw [hw]
 have y':ship e' (z u (momentm P.run i s))=ball (stone P p s i k d) (sun t σ) := y
 rw [y']
 exact (v k m d _ h e σ).2

end


def ArenaLet (s t:ℕ):Prop:= Tower.region H 0 P.calibration.ℓ (couch P s t)
open Pressure
lemma airborne:
 ∀ᶠ s' in atTop,∀t,Strut (scaleM P s') t→ t%2=0→ArenaLet P s' t:=by
 filter_upwards [(turnover P.par).eventually (offPeak (P.calibration.ℓ +2*n))] with s' u t h v j y
 let d:=etch P s'+(P.calibration.ℓ +2*n)
 have j1:(2*d+4)^2 ≤ t:=u t h
 have j2:etch P s'+2*n+P.calibration.ℓ ≤ t:=by unfold d at j1;nlinarith
 obtain ⟨m,b,rfl⟩:= mem_image.mp y
 have q:=(box_test.mp b).1 H
 -- q radius?
 simp only [Pi.add_apply,Pi.smul_apply,step_apply,ite_true] 
 simp
 omega

variable {t:ℕ}
lemma snapOK (l:ArenaLet P s t){v:Buffered.Family P.calibration}
 (h:InTest P.calibration true (couch P s t) false v):
  v∈ P.Vox H s:=
 (purpose_ok ..).mpr ⟨⟨couch P s t,h,by rw [SlabMark.area0];exact l⟩,fun j=>by cases j⟩

lemma snap (V:P.Vox H s):
 ‖P.piece H s V‖^2=(P.E s (mirror D H 0 V.val*V.val)).re:=by
 rw [norm_sq_eq_re_inner (𝕜:=ℂ)]
 have q:=contracts P.run P.large P.law P.history.circuit H 0 false (P.room H)
   s s s le_rfl le_rfl V V
 rw [SlabMark.area0,Nat.sub_self] at q
 rw [q];rfl

variable (f:ℕ)(w:
   ∀ᶠ i in atTop, ∀k, merrier P s i k →∀d t,Strut (scaleM P s) t→t%2=0→∀σ,Wickday P p f s i k d t σ)
include M a w
lemma procession (l:ArenaLet P s t)(h:Strut x t)(v:t%2=0):
  ∃U:P.Vox H s,
    U.val= roses D n H (t/2:ℕ) (hueM P s) g J∧
    ‖P.piece H s U‖^2 ≤ mPrice (gold P s f):=by
 let d:=mPrice (gold P s f)
 have dh:0≤d:=by unfold d mPrice;positivity


 let q(σ):=toss P t (hueM P s) g J σ
 let b(σ):P.Vox H s:=⟨q σ,snapOK P s l (joys P p s M σ (t:=t) _).landing⟩
 have y(σ): ‖P.piece H s (b σ)‖≤Real.sqrt d:=by
     rw [←Real.sqrt_sq (norm_nonneg _)]
     apply Real.sqrt_le_sqrt
     rw [snap]
     exact (Complex.re_le_norm _).trans (aromaR P p s a M σ f w h v)
 let j:=arrows P.run P.large P.law P.history.circuit H 0 false (P.room H) s
 let u:P.Vox H s:=∑σ:Signed,(Hem.ramp σ:ℂ) • b σ
 refine ⟨u, ?_,?_⟩
 · change (P.Vox H s).subtype (∑σ:Signed,(Hem.ramp σ:ℂ) • b σ)=_
   rw [map_sum]
   rfl
 change ‖j u‖ ^ 2≤ d
 refine le_trans (b:=(Real.sqrt d)^2) ?_ (Real.sq_sqrt dh).le
 apply pow_le_pow_left₀ (norm_nonneg _)
 unfold u
 rw [map_sum]
 apply (norm_sum_le ..).trans
 rw [←one_mul (√d),←ramp_abs,sum_mul]
 refine sum_le_sum fun σ _=>?_
 rw [map_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs]
 exact mul_le_mul_of_nonneg_left (y σ) (abs_nonneg _)
end YM.CF.Merino.Tiara
