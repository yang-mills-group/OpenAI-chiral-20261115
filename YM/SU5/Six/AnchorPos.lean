import YM.SU5.Six.Photos
import YM.SU5.Six.Rates
import YM.SU5.Aria.Grotto
import YM.SU5.Six.KeepCharge
import YM.SU5.Six.MirrorCharge
set_option maxHeartbeats 200000
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Set
open Cheer (Narrow)

/-!
# An all-axis open domain and an anchor in each of its chambers

No `readyUV` computed anew on changing the poses; translate with the
continuous **otherSpectrum** motion. We can just expand the heat difference
and use the matrix heat/space estimates (including strictly positive time
cross) from the proof of `zoommat`.
-/
abbrev Orders:= {s: Axis→Bool // s 3=true}
def OrderSlab (σ: Orders)(w:Vantage)(j:Axis):Set ℝ := if σ.val j then Set.Ioi (2*w j) else Set.Iio (-(2*w j))
def OrderChamber (σ:Orders) (w:Vantage):Set Vantage:= {t|∀ j,t j ∈OrderSlab σ w j}
lemma order_forward (σ:Orders)(w t:Vantage)(p:t∈OrderChamber σ w): 2*w 3<t 3:= by
  have he:=p (3:Axis); rwa [OrderSlab,if_pos σ.property] at he
lemma slab_open (σ w j):IsOpen (OrderSlab σ w j):=by unfold OrderSlab; split <;> first| exact isOpen_Iio| exact isOpen_Ioi
lemma chamber_open (σ w): IsOpen (OrderChamber σ w):= by
  rw [show OrderChamber σ w=Set.univ.pi (OrderSlab σ w) by ext; simp [OrderChamber, Set.pi]]
  exact isOpen_set_pi (Set.finite_univ) (fun i _=>slab_open σ w i)
noncomputable def pointMatrix (P:Spine)(x:P.Spectrum0 3)(s n:ℕ)(p:Vantage): Matrix Lead.Clan Lead.Clan ℂ:= Matrix.of (fun Z W=> P.transmission x s n Z W p)
def ReadsSix (A:Matrix Lead.Clan Lead.Clan ℂ):Prop:= A.det≠0 ∧ ∀ Z,A Z Z≠0
lemma readsSix_open : IsOpen {m:Matrix Lead.Clan Lead.Clan ℂ|ReadsSix m}:= by
  rw [show {m|ReadsSix m}= {m:Matrix Lead.Clan Lead.Clan ℂ|m.det ≠0} ∩ ⋂ (i:Lead.Clan),{m|m i i≠0} from by ext; simp [ReadsSix]]
  exact ((isOpen_ne (x:=0)).preimage (Continuous.matrix_det (continuous_id (X := Matrix Lead.Clan Lead.Clan ℂ)))).inter (isOpen_iInter_of_finite (fun i=>(isOpen_ne (x:=0)).preimage ((continuous_id (X := Matrix Lead.Clan Lead.Clan ℂ)).matrix_elem i i)))
private lemma cross_cont : Continuous (transverse (3:Axis)):= Continuous.subtype_mk (by
 apply ((PiLp.continuous_toLp 2 _).comp (f:=fun x:Trans 3→ℝ=> fun i:Axis=> if h:i = (3:Axis) then (0:ℝ) else x ⟨i,h⟩) (continuous_pi fun i=> ?_)); split
 · exact continuous_const
 exact continuous_apply _) _
lemma screen_cont {u:ℕ→Bank}{v:Bank}(x:∀ k,Tendsto (fun n=>reveal k (u n)) atTop (𝓝 (reveal k v))):Tendsto u atTop (𝓝 v):= by
 rw [eyes_toFace 3 v]; exact (cross_cont.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr x)).congr fun n=>(eyes_toFace 3 (u n)).symm
-- generic aperture and time margin at zoom
variable (P:Spine)(b:Orders)(Z W:Lead.Clan)(n s:ℕ)
def sample_anchor (j:Axis) : ℝ := if j=(3:Axis) then 10*P.dew s n else if b.val j then 3*P.probeWidth s n j else -(3*P.probeWidth s n j)
-- `n s` order? variable order b n s. use command checks.
#check @sample_anchor

local notation "ƛ"=> P.dew
local notation "γ" t:max=> Cheer.FLap (promenade Z) 0 t
private def primaW (Z:Lead.Clan) (a:ℝ) := Cheer.FLap (promenade Z) 0 (a:ℂ)
def proofTone := primaW Z 10 - primaW Z (10+1/2) - primaW Z (10+1/2) + primaW Z (10+1/2+1/2)
private lemma proofTone_paid : 0 < (proofTone Z).re:= by
  let F(a:ℝ): E4→ℂ:= Cheer.tendsK 0 (a:ℂ)
  have he (a:ℝ)(p:E4) : F a p= ↑(Real.exp (-(a*time p))):= by unfold F Cheer.tendsK; push_cast; simp only [inner_zero_right,Complex.ofReal_zero,zero_mul,zero_sub]
  let a:ℝ := 10; let b:ℝ := 1/2
  let M:Measure E4:= (promenade Z).val
  let H:=fun p:E4=>F a p -F (a+b) p - F (a+b) p+F (a+b+b) p
  have hh(k:ℝ)(p:0≤k): Integrable (F k) M:=Cheer.destined _ _ _ (home_bright Z) p
  have hc:0≤a:=by norm_num [a]
  have hv:0<b:=by norm_num [b]
  have hp:= hh a hc; have ht:= hh (a+b) (add_nonneg hc hv.le); have hl:= hh (a+b+b) (add_nonneg (add_nonneg hc hv.le) hv.le)
  have hr:= (hp.sub ht).sub ht
  have hI:Integrable H M:= hr.add hl
  have hM: proofTone Z = ∫ p,H p∂M:= by
    change _=∫ p,((F a-F (a+b)-F (a+b))+F (a+b+b)) p∂M; rw [integral_add' hr hl, integral_sub' (hp.sub ht) ht, integral_sub' hp ht]; rfl
  let L:=fun p:E4=> RCLike.re (H p)
  have Hq:∀ᵐ x∂M,0<L x:= by
    filter_upwards [promenade_strict Z] with x g
    have hg:0<time x:=((Mink.strict_self _).1 g).1
    let t:=time x; let E:ℝ:=Real.exp (-(a*t)); let E₁:= Real.exp (-(b*t));
    have e(k:ℝ): Real.exp (-((k+b)*t))=Real.exp (-(k*t))*E₁:=by rw [show -((k+b)*t)=-(k*t)+-(b*t) by ring,Real.exp_add]
    have hL: L x= E*(1-E₁)^2:= by change (F a x - F (a+b) x - F (a+b) x + F (a+b+b) x).re= _; simp_rw [he]; simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re]; change E-Real.exp (-((a+b)*t))-Real.exp (-((a+b)*t))+Real.exp (-((a+b+b)*t))= _; rw [e (a+b),e a]; unfold E; ring
    have heB:E₁<1:=by unfold E₁; rw [Real.exp_lt_one_iff]; exact neg_lt_zero.mpr (mul_pos hv hg)
    rw [hL]; exact mul_pos (Real.exp_pos _) (pow_pos (sub_pos.mpr heB) _)
  change 0< RCLike.re (proofTone Z); rw [hM, ← integral_re hI]
  haveI N:NeZero M := ⟨promenade_ne _⟩ -- measure
  change 0<∫ p,L p∂M
  apply lt_of_le_of_ne (integral_nonneg_of_ae (Hq.mono fun _ e=>e.le))
  intro e
  have hz:= (integral_eq_zero_iff_of_nonneg_ae (Hq.mono fun _ e=>e.le) hI.re).1 e.symm
  obtain ⟨x,v,d⟩:= (Hq.and hz).exists; exact d.not_gt v -- tune
lemma proofTone_ne : proofTone Z≠0:=fun e=>by have he:= proofTone_paid Z; rw [e] at he; exact lt_irrefl (0:ℝ) he
private lemma three_gaps (X:Hilbert)(S:OS.Semigroup X (3:Axis))(x y:X)(p:Bank)(a b:ℝ≥0) :
    inner ℂ (x-S.E b x) (S.U p (S.E a (y-S.E b y)))=
      inner ℂ x (S.U p (S.E a y))-inner ℂ x (S.U p (S.E (a+b) y))-inner ℂ x (S.U p (S.E (a+b) y))+inner ℂ x (S.U p (S.E (a+b+b) y)):=by
  have e(v w:ℝ≥0)(u:X): S.E v (S.E w u)=S.E (w+v) u:= by rw [add_comm w,S.time]; rfl
  rw [map_sub, map_sub, inner_sub_left, inner_sub_right, inner_sub_right,S.swing,S.swing]
  have h(u:X):S.E b (S.U p u)= S.U p (S.E b u):= DFunLike.congr_fun (S.independent b p) u
  rw [h,h,e a b,e b a,add_comm b a,e]; ring

variable {P}{K:P.Register}{x:P.Spectrum0 3}{J:P.Ellis 3 x}{c r:ℕ→ℕ}(B:Experiment P K c r x J)
local notation "s'" i:max=> c i
local notation "n'" i:max=> r i
local notation "ρ" i:max=> P.dew (c i) (r i)
local notation "w'" i:max=> P.probeWidth (c i) (r i)
local notation "Q" i:max => P.sample_anchor b (r i) (c i)
local notation "R" i:max=> ((Q i) 3).toNNReal
local notation "ξ"=> P.otherSpectrum 3 3 x
local notation "S"=> P.seasons 3 ξ
local notation "δ" i:max=> transverse 3 (fun j:Street=>(P.sample_anchor b (r i) (c i) j.val))
local notation "Φ"=> P.birthCloud x
include J B
lemma anchor_in : ∀ᶠ i in atTop, Q i ∈ OrderChamber b (w' i):= by
  filter_upwards [(limit_times_width B.launch).eventually (eventually_lt_nhds (show (5/2:ℝ)<10/2 by norm_num))] with i p
  have hp:0<ρ i:=P.dew_pos _ (B.launch.unitSize _)
  intro j
  unfold OrderSlab; simp only [sample_anchor]
  by_cases h:j=3
  · subst j; rw [if_pos b.property, if_pos rfl]; apply Set.mem_Ioi.mpr
    linarith only [(div_lt_iff₀ hp).1 p]
  have he:= P.width_here (c i) (r i) j
  by_cases v:b.val j
  · rw [if_neg h, if_pos v, if_pos v, Set.mem_Ioi]; linarith only [he]
  rw [if_neg h, if_neg v,if_neg v, Set.mem_Iio]; linarith only [he]
lemma anchor_bank : Tendsto (fun i=>(ρ i)⁻¹ • δ i) atTop (𝓝 (cutPulse 0)):=by
  rw [show cutPulse 0=0 from Subtype.ext (show position (0:Space3) 0=0 from (by rw [←Mink.combine_at]; exact map_zero _))]; apply screen_cont; intro j
  have h:= limit_space_width B.launch j.property
  rw [rev_zero]
  have ht(c:ℝ): Tendsto (fun i=> c*((w' i) j.val/(ρ i))) atTop (𝓝 0) := by simpa only [mul_zero] using h.const_mul c
  by_cases v:b.val j.val
  · refine (ht 3).congr fun i=>?_; rw [revs,show reveal j _=(Q i) j.val from transverse_eyes 3 (fun j:Street=>(Q i) j.val) j]; unfold sample_anchor; rw [if_neg j.property,if_pos v]; ring
  refine (ht (-3)).congr fun i=>?_; rw [revs,show reveal j _=(Q i) j.val from transverse_eyes 3 (fun j:Street=>(Q i) j.val) j]; unfold sample_anchor; rw [if_neg j.property,if_neg v]; ring
lemma anchor_heat (E':ℕ→ℝ≥0)(t:ℝ)(p:0<t)(w:P.dimensionS c r E' t):
    Tendsto (fun i=> inner ℂ (Φ Z (c i) (r i)) ((S).U (δ i) ((S).E (E' i) (Φ W (c i) (r i))))) atTop (𝓝 (if Z=W then primaW Z t else 0)):= by
  let f(i:ℕ):= inner ℂ (P.birthCloud x Z (c i) (r i)) ((S).U (δ i) ((S).E (E' i) (P.birthCloud x W (c i) (r i))))
  by_cases u: Z=W
  · subst W; refine Eq.mp (congrArg (fun t => Tendsto f atTop (𝓝 t)) (if_pos (show Z=Z from rfl)).symm) ?_
    exact zoom_diagonal Z B.launch B.ready Twah.keyV_go (B.ground.2.1.accepted 3) (0:Space3) ⟨t,p.le⟩ _ w _ (anchor_bank b B)
  exact Eq.mp (congrArg (fun t=> Tendsto f atTop (𝓝 t)) ((if_neg u).symm)) (zoom_other_pos Z W B.launch B.ready Twah.keyV_go u (B.ground.2.1.accepted 3) _ p _ w _ (anchor_bank b B))
local notation "Γ" i:max t:max => inner ℂ (Φ Z (c i) (r i)) ((S).U (δ i) ((S).E t (Φ W (c i) (r i))))
local notation "Δ" i:max=> P.increment (c i) (r i)
omit B
include J
private lemma gapsPaid (i:ℕ)(u:Q i ∈ OrderChamber b (w' i)) :
   P.transmission x (c i) (r i) Z W (Q i)= (Γ i (R i))-(Γ i ((R i)+(Δ i)))-(Γ i ((R i)+(Δ i)))+(Γ i ((R i)+(Δ i)+(Δ i))):= by
  let w:= P.birthCloud x Z (c i) (r i); let w₂:= P.birthCloud x W (c i) (r i); let p:Vantage:= Q i
  let D:= δ i; let a:= (R i); let T:=(S); let E':=T.E; let b':=(Δ i); let H:=P.ManyF 3 ξ; let V:=(E' a) (w₂-E' b' w₂); let K':=P.cartage 3 ξ p
  refine (Eq.trans (P.positive_time_charge x (c i) (r i) Z W (Q i) J (order_forward b _ _ u)) (Eq.trans ?_ (three_gaps H T w w₂ D a b')))
  exact congrArg₂ (inner ℂ) (P.filtered_explicit x (c i) (r i) Z) (((congrArg (fun y:H=> K' (E' a y)) (P.filtered_explicit x (c i) (r i) W))).trans (DFunLike.congr_fun (P.uses_cart 3 ξ p) V)) -- redundant parentheses?
omit J
private lemma combine_gaps (f g k:ℕ→ℂ)
   (h:Tendsto f atTop (𝓝 (if Z=W then primaW Z 10 else 0)))
   (u:Tendsto g atTop (𝓝 (if Z=W then primaW Z (10+1/2) else 0)))
   (v:Tendsto k atTop (𝓝 (if Z=W then primaW Z (10+1/2+1/2) else 0))) :
   Tendsto (fun i=> f i-g i-g i+k i) atTop (𝓝 (if Z=W then proofTone Z else 0)):= by
  have hL:= ((h.sub u).sub u).add v
  have L: (if Z=W then primaW Z 10 else 0)-(if Z=W then primaW Z (10+1/2) else 0)-(if Z=W then primaW Z (10+1/2) else 0)+(if Z=W then primaW Z (10+1/2+1/2) else 0)=if Z=W then proofTone Z else 0:= by split_ifs with p; rfl; ring
  rw [L] at hL; exact hL
include J B
lemma anchor_clears : Tendsto (fun i=> P.transmission x (c i) (r i) Z W (Q i)) atTop (𝓝 (if Z=W then proofTone Z else 0)):= by
  let f(i:ℕ):ℝ≥0:= R i; let g(i):=P.increment (c i) (r i)
  have hpF : P.dimensionS c r f 10:= tendsto_const_nhds.congr fun i=>by
    have hv:0<ρ i:= P.dew_pos (c i) (B.launch.unitSize i); unfold f sample_anchor; rw [if_pos rfl, Real.coe_toNNReal]
    · field_simp [hv.ne']
    positivity
  have hg:P.dimensionS c r g (1/2):= increment_ratio B.launch
  have hs(a v:ℕ→ℝ≥0)(u w:ℝ)(h:P.dimensionS c r a u)(p:P.dimensionS c r v w): P.dimensionS c r (a+v) (u+w):= (h.add p).congr fun i=> by simp only [Pi.add_apply,NNReal.coe_add,add_div]
  let q:= anchor_heat b Z W B; let m:= f+g; let n₀:= f+g+g; have h':P.dimensionS c r m (10+1/2):= hs f g _ _ hpF hg
  have h:= q f 10 (by norm_num) hpF; have hm:= q m (10+1/2) (by norm_num) h'; have hn₀:= q n₀ (10+1/2+1/2) (by norm_num) (hs m g _ _ h' hg)
  let X(t:ℕ→ℝ≥0)(i:ℕ):ℂ:= Γ i (t i)
  exact (combine_gaps Z W (X f) (X m) (X n₀) h hm hn₀).congr' ((anchor_in b B).mono fun i u=>(gapsPaid b Z W (J:=J) i u).symm)
lemma vary_pose_live : ∀ᶠ i in atTop,ReadsSix (P.pointMatrix x (c i) (r i) (Q i)):= by
 let X:= Matrix.diagonal proofTone
 have he: X.det≠0:= by unfold X; rw [Matrix.det_diagonal]; exact Finset.prod_ne_zero_iff.mpr (fun i _=> proofTone_ne i)
 have hg:ReadsSix X:= ⟨he,fun i=> (Matrix.diagonal_apply_eq ..).trans_ne (proofTone_ne i)⟩
 let F(i):= P.pointMatrix x (c i) (r i) (Q i)
 have ht:Tendsto F atTop (𝓝 X):= tendsto_pi_nhds.mpr (fun Z=> tendsto_pi_nhds.mpr (fun W=>anchor_clears b Z W B)) -- tune orientation
 exact ht.eventually (readsSix_open.mem_nhds hg)
omit B
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
