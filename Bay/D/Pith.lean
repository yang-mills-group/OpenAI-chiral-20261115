import Bay.D.Sencha
import Bay.D.Betra
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

namespace D
open Exterior Precision Nacre
open scoped ContDiff
open Regis Regis.Head Etch Gleam Next.SectorChange Next.SectorChange.Gaussian
open Pressure Work.F03 ProbabilityTheory
local notation "T4"=>SU.group
open Buffered Lamour.Bridge.Celeste.Clock Fabric
open Py Py.Rate LocalLimit Preparation Buffered.Afterglow Papal
open Vale clocks
open YM.CF.Pannier.Chancel Journey Tower Tower.SlabMark VacuumSelection Tapestry
open scoped ComplexOrder NNReal ENNReal

open Lake
namespace Lake
variable {S:Finset Cover}{K:Calibration}{N:Side} {i:ℕ}
/-- single scaled measurement readback -/
def blend(x:Lake K S):ℕ→Buffered.Family K:=x.sun.pool+Complex.I • x.ray.pool
lemma blendQ(x:Lake K S):BQueue S x.blend x.allLake.val:=
 trip_add x.sun.good (trip_scale x.ray.good Complex.I)

lemma Seal.both{x:Lake K S}{m:Side}{e:K.c m=N}
 {F:Pane N→ℂ}(h:x.Seal i m e F):
 (e ▸ x.blend i m :Mark N) = Hookah.chalkOp F:=by
 subst N
 obtain ⟨p,q⟩:=h
 change x.sun.pool i m=_ at p
 change x.ray.pool i m=_ at q
 change x.sun.pool i m + Complex.I • x.ray.pool i m=_
 rw [p,q];funext X
 change ((F X.1).re:ℂ) • 1+ Complex.I • (( (F X.1).im:ℂ) • 1) = F X.1 • (1:FC _)
 rw [smul_smul,←add_smul,mul_comm Complex.I,Complex.re_add_im]

end Lake
variable (P:VacuumSelection.Spine)(s:ℕ)
local notation "K"=>P.calibration
local notation "Ω"=>scale P s
local notation "Y"=>P.run
local notation "N" c:max=> Papal.count Y s c
variable (d:ℕ)

def Corsair(g:Guest P)(f:P.Test):Group3:=fun j=>Price P s g (Lake.notes P (P.shifts 3 d f) j)

abbrev militia (i k:ℕ)(f:Pane (N i)→ℂ):Group3:=
  fun j=>compass Y i k s (Hookah.chalkOp
   (strata f (forward (prepL K _ d)) (after (tailL K _ d)) j))

abbrev BigBang (i r:ℕ){S:Finset Cover}(x:Lake K S):=
  x.Seal r _ (Journey.terrain Y P.large (P.run.ir i) s)
lemma burst {i:ℕ→ℕ}{k:ℕ→ℕ}(h:Row P i k)
 {S:Finset Cover}{x:Lake K S}
 {f:∀r,Pane (N (i r))→ℂ}(t:∀ᶠ r in atTop, BigBang P s (i r) r x (f r)):
 Tendsto (fun r=>militia P s d (i r) (k r) (f r)) atTop (𝓝 (Corsair P s d none x.allLake)):=by
 rw[tendsto_pi_nhds]
 intro j
 unfold Corsair
 rw [←Lake.tone_clause]
 have u:= quickens P s h (blendQ (x.tones d j))
 refine Tendsto.congr' ?_ u
 filter_upwards[t] with r v
 rw[Journey.sharp,Journey.listen,Journey.send,Lake.Seal.both (Lake.tone_three v d (tailL _ _ d) rfl j)]

local notation "R₀"=>wholeD K d
def splashZ(a:ℝ)(f:P.Test): P.Test:= P.shifts 3 d ((a:ℂ) • f)

def fires(g:Guest P)(f:P.Test):ℝ:= (Price P s g (P.reflectTest 3 f*f)).re


lemma pos_intro(g:Guest P)(a:ℝ)(f:P.Test):
 a^2 * (synopsis (Corsair P s d g f)).re ≤ fires P s g (splashZ P d a f):=by
 let y:=P.shifts 3 d f
 have e:splashZ P d a f=(a:ℂ) • y:=by
    exact map_smul _ _ _
 let z:=P.reflectTest 3 y
 rw [e,fires]
 have h:P.reflectTest 3 ((a:ℂ) • y)= (a:ℂ) • z:=by
    rw[map_smulₛₗ, Complex.conj_ofReal]
 rw [h, Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul,←sq,map_smul,smul_eq_mul,←Complex.ofReal_pow,Complex.re_ofReal_mul]
 apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
 change ((Price P s g (z*y)) - Price P s g y * Price P s g (P.reflectTest 3 y)).re ≤ _
 rw [←price_star,Complex.star_def,Complex.mul_conj,Complex.sub_re,Complex.ofReal_re]
 exact sub_le_self _ (Complex.normSq_nonneg _)

lemma inkPrice(g:Guest P)(f:P.Test):
 (ranked (R₀:ℝ) (Corsair P s d g f)).re=R₀^8*(synopsis (Corsair P s d g f)).re:= by
 rw[ranked,← Complex.ofReal_pow,Complex.re_ofReal_mul]

-- use metric lower bound for all a (c_s formula specialized)
lemma bonfire {δ z ε:ℝ}
  (t:0<δ)(r:0 < R₀)
  (m:ε≤lbott δ / 2) (k:lbott δ≤z)
  {f:P.Test} {g:Guest P}
  (b:‖ranked (R₀:ℝ) (Corsair P s d g f) - z‖≤ε)
  (a:ℝ)(v:0≤a):
 Real.sqrt (lbott δ/2) * a / (R₀:ℝ)^4 ≤ Real.sqrt (fires P s g (splashZ P d a f)) := by
 have t0:=lbott_pos δ t
 have r' : (0:ℝ) < R₀:=by exact_mod_cast r
 have n := (Complex.abs_re_le_norm _).trans b

 rw [Complex.sub_re,inkPrice,Complex.ofReal_re,abs_le] at n
 let u:= (synopsis (Corsair P s d g f)).re
 have l : lbott δ /2 / (R₀:ℝ)^8 ≤ u:=(div_le_iff₀ (by positivity)).mpr (by unfold u;rw[mul_comm];linarith only [k,m,n.1])
 let p := pos_intro P s d g a f
 have h:0≤fires P s g (splashZ P d a f):=
    le_trans (mul_nonneg (sq_nonneg _) (le_trans (by positivity) l)) p
 apply (le_of_sq_le_sq _ (Real.sqrt_nonneg _))
 rw [Real.sq_sqrt h,div_pow,mul_pow,Real.sq_sqrt (half_pos t0).le, ←pow_mul]
 rw [mul_div_right_comm, mul_comm]
 exact le_trans (mul_le_mul_of_nonneg_left l (sq_nonneg _)) p

abbrev floorPrice (κ:Calibration)(d:ℕ)(x τ q:ℝ):= q/(x*τ^2*halfSteps κ d^4)
abbrev floorC(δ:ℝ):=Real.sqrt (lbott δ/2)/256
abbrev Dollar(x τ q:ℝ):=q/(x*τ^2)
lemma floorCp(δ:ℝ)(t:0<δ):0<floorC δ:=div_pos (Real.sqrt_pos_of_pos (half_pos (lbott_pos _ t))) (by norm_num)

lemma floorSpend (x τ q δ:ℝ): floorC δ * floorPrice K d x τ q =
 Real.sqrt (lbott δ/2) * Dollar x τ q / (R₀:ℝ)^4 :=by
 unfold floorC floorPrice Dollar wholeD halfSteps
 rw [div_pow,Nat.cast_mul,Nat.cast_ofNat,mul_pow]
 have h(c v a b:ℝ): c /256 * (v / (a*(b/16))) = c*(v/a)/(16*b):=by
    by_cases t:a=0; simp [t]
    by_cases u:b=0; simp [u]
    field_simp; ring
 norm_num only [show (2:ℝ)^4=16 from by norm_num]
 exact h ..

variable {m:ℕ} {i k:ℕ→ℕ}
 {g:∀r,Pane (N (i r))→ℂ}
 {τ q ε:ℝ}
local notation "SΩ"=> Band inletO (radiusB Ω)

/-- mesh reading, leading charge and moving reflection lower.
 Written Z-measures are x*tuneZ taking g; Q/τ² normalized limit hence Dollar. -/
structure Clang (P:VacuumSelection.Spine)(s:ℕ)(i k:ℕ→ℕ)
  (g:∀r,Pane (Papal.count P.run s (i r))→ℂ)
  (T:P.Test)(d:ℕ)(z:ℕ→ℝ)(τ q δ ε:ℝ):Prop where
   comes:Tendsto (fun r=>militia P s d (i r) (k r) (g r))
      atTop (𝓝 (Corsair P s d none T))
   fire(y:Guest P):
     floorC δ * floorPrice P.calibration d (scale P s) τ q ≤
     Real.sqrt (fires P s y (splashZ P d (Dollar (scale P s) τ q) T))
   near: ∀ᶠ r:ℕ in atTop,
    let R : ℝ:= wholeD P.calibration d
    (∀y,‖ranked R (Corsair P s d y T)-(z r:ℂ)‖≤ε) ∧
     ‖ranked R (militia P s d (i r) (k r) (g r))-(z r:ℂ)‖≤2*ε

lemma clangs (D:P.Register)
 (e:Encore P s i k)(v:Styx K Ω m d)
 (ε δ:ℝ)(a:0<ε)(p:0<δ)(u:ε≤lbott δ/2)
 (hp:0≤q)
 {ig:∀r,Pane (N (i r))→ℂ}
 {T:Lake K SΩ} {z:ℕ→ℝ}
 (h:∀ᶠ r in atTop, BigBang P s (i r) r T (ig r))
 (b:∀ᶠ r:ℕ in atTop, ∃ M:Group3,lbott δ ≤ z r ∧
     CrownRank Ω (R₀:ℝ) ε (z r) M ∧
     Light P s (i r) (k r) r T d M):
 Clang P s i k ig T.allLake d z τ q δ ε:=by
 have t :=burst P s d e.1 h
 have j:= cowlled v.right v.sub v.paid
 have f:= mallets P s D e j v.left T
 let y: Group3→ℂ:= ranked R₀
 have tp:∀ᶠ r in atTop,dist (y (militia P s d (i r) (k r) (ig r))) (y (Corsair P s d none T.allLake)) < ε:=
   Metric.tendsto_nhds.mp (ranked_cont.continuousAt.tendsto.comp t) ε a
 have l:∀ᶠ r in atTop,lbott δ≤z r∧ ∀g,‖y (Corsair P s d g T.allLake)-(z r:ℂ)‖≤ε:=by
     filter_upwards [b,f] with r B F
     obtain ⟨m,w,k,h⟩:=B
     exact ⟨w,fun g=>k _ (F _ h g)⟩
 have r:0<R₀:=by unfold wholeD; have w:=v.right; unfold Cowl at w; omega
 refine ⟨t,?_,?_⟩

 · intro w
   obtain ⟨n,v₁,v₂⟩:=l.exists
   rw[floorSpend]
   have hq:=v.left.1
   exact bonfire P s d p r u v₁ (v₂ w) _ (div_nonneg hp (mul_nonneg hq.le (sq_nonneg _)))
 filter_upwards [l,tp] with n x e
 refine ⟨x.2,?_⟩
 rw[two_mul];rw[dist_eq_norm] at e
 exact (norm_sub_le_norm_sub_add_norm_sub _ (y _) _).trans (add_le_add e.le (x.2 none))

end YM.CF.Bay.D
