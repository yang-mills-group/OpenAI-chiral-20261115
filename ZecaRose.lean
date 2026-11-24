import SatinThinPromenade
import ZecaViolet
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition
variable (P:Spine)(R : P.Register)(j:Axis)
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "W"=> P.calibration
local notation "Q"=> P.par.block
local notation "ℓ"=> P.calibration.ℓ
open Papal Regis.Head Gleam
/-! # Price of ensemble-of-trips. Exactly composed on printed test level before estimation. -/
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
variable {s t f r v i k:ℕ}
local notation "Λ"=> P.par
local notation "L"=> P.par.R.L
local notation "H"=>P.large
local notation "N" s:max i:max => Journey.side P.run i s
/-! # Buy height and travel together. Keep both actual calibration and rank resolution schedule. -/
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
open Worth Pays CF.BProof
open Real (log)
open Aria Casting MacroGrid
local notation "z'" => witnessZ
open Regis.Head.Etch Push.Local AnalyticBridge.VerifiedReset
local notation "Δ" t:max x:max => P.tariffQ z' t x
variable (x : P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "M"=> P.ColorHil 3 (ξ)
local notation "G"=> P.ManyF 3 (ξ)
local notation "E" r:max=> P.singleState 3 r x
local notation "Ω"=> P.colorZero 3 ξ

-- B2-geo
variable (l:List Axis)
abbrev roseMargin:ℕ:=P.roomy+P.echoFoot
abbrev roseJump:ℕ:=P.sidesPerTick*P.roseMargin
abbrev roseRoot (f s:ℕ)(l:List Axis):Cover:=
  P.rootSpace f s l + fun _: Axis=> (P.roseJump:ℤ)
abbrev roseFlat:=4*(P.sidesPerTick + P.roseJump + P.par.block.val +1)
abbrev roseWide (j:Axis)(s:ℕ):=4*P.axleQ j (P.thresholdF s)+P.roseFlat
local notation "κ"=>P.sidesPerTick
local notation "κz" => (P.sidesPerTick:ℤ)
local notation "σ" u:max=> nodeC (P.roseRoot f u l)
local notation "q" u:max=> P.axleQ j (P.thresholdF u)
local notation "w" u:max=> P.roseWide j u

lemma rose_height :
 (↑(2*(q s +P.roseJump)+1):ℤ)≤ (σ s) j ∧
 (σ s) j ≤ ↑(2*(q s+P.sidesPerTick+P.roseJump)+1):=by
 have h:=P.broadly j s f l
 change (q s:ℤ)≤ _ ∧ _ ≤ (q s :ℤ)+κz at h
 simp only [nodeC,two_smul,Pi.add_apply,Pi.one_apply,roseRoot]
 let qx := P.rootSpace f s l j
 -- omega sees reducible add in h and unfolded in root? force
 change _ ≤ (qx+_+(qx+_)+1) ∧ (qx+_+(qx+_)+1) ≤ _
 change _ ≤ qx ∧ qx ≤ _ at h; omega
lemma rose_sundial :
 (P.roseJump:ℤ)≤ (σ s) j ∧
 (σ s) j + P.roseJump ≤ w s :=by
 have h:=P.rose_height j (f:=f) (s:=s) l
 change _ ∧ _ ≤ (↑(4*(q s)+4*_):ℤ)
 omega

lemma rose_β (D:ℝ)(h:0<D):
 ∀ᶠ s:ℕ in atTop, 2*spanSites P.par.block (w s) ≤ scout P.par D s:=by
 let c:=2*spanSites P.par.block (4+P.roseFlat)
 filter_upwards [P.earns_widthT j D h c] with s a
 have ha: c*(q s)≤ scout P.par D s:=by
    exact_mod_cast a.trans (Nat.le_ceil _)
 apply le_trans ?_ ha
 have hg:1≤ q s:=by unfold axleQ repeatD; omega
 have ht:w s ≤ (4+P.roseFlat)*q s:=by
    unfold roseWide; rw [add_mul]; gcongr
    exact Nat.le_mul_of_pos_right P.roseFlat hg
 unfold c spanSites; rw [mul_assoc 2 _ (q s),mul_assoc _ _ (q s)]; gcongr
lemma rose_rent:
 ∀ᶠ s:ℕ in atTop,14* Worth.meterC (hat P.par.R.L P.par.x s) *
            (((8*spanSites P.par.block (P.roseWide j s):ℕ):ℝ))^4 ≤ 1:=by
 filter_upwards [P.weather_bill 1 zero_lt_one, P.rose_β j 1 zero_lt_one] with s a b
 unfold repeatBill at a
 have hq:0≤14*Worth.meterC (hat L P.par.x s):=mul_nonneg (by norm_num) (coin_pos ..).le
 apply le_trans ?_ a
 apply mul_le_mul_of_nonneg_left _ hq
 apply pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr _) _
 omega

lemma rose_license :
 ∀ᶠ s:ℕ in atTop, ∀ (f:ℕ)(l:List Axis),Odessa j (P.roseRoot f s l) s (w s) P:=by
 filter_upwards [P.rose_rent j] with s t f l
 have h:=P.rose_height j (s:=s) (f:=f) l
 have hr:(w s:ℤ) ≤ ruler P.par.block*(w s):=le_mul_of_one_le_left (by positivity)
      (ruler_gene _)
 have h' : P.labW s+ℓ+frameRadius j=q s:=rfl
 refine ⟨?_, ⟨by omega,by omega⟩, le_trans ?_ hr,le_trans ?_ hr,?_, t⟩
 · unfold roseWide roseFlat; omega
 · unfold roseWide roseFlat; omega
 · unfold roseWide roseFlat; omega
 have p:w s ≤ spanSites P.par.block (w s):=Nat.le_mul_of_pos_left _ (Nat.mul_pos (by decide) P.par.block.property)
 unfold plusAgain stepAgain; unfold roseWide roseFlat at *
 omega

-- placement
private lemma interval_slide {k e x y a z W₁ J u r:ℤ}
 (p:0<k)(t:1≤ u)(G₁: r*k+e ≤ J)
 (h:0≤J)(q₁:0≤W₁)
 (v:J ≤ z) (b:z+J≤W₁)
 (d:-e≤x∧x≤e)
 (H₁:u*z=x+k*a)
 (hh:y=u*W₁):
 r ≤ a ∧ a+r ≤ y:=by
 constructor
 · apply (mul_le_mul_iff_right₀ p).mp
   linarith only [H₁,G₁,d,v,le_mul_of_one_le_left (h.trans v) t]
 rw [hh]
 apply (mul_le_mul_iff_right₀ p).mp
 linarith only [H₁,G₁,d,mul_le_mul_of_nonneg_left b (by omega:0≤ u),
    le_mul_of_one_le_left h t,
    le_mul_of_one_le_left (mul_nonneg (by omega:0≤ u) q₁) (show 1 ≤ k from p)]

local notation "X" t:max=>pivotQ (P.granule (P.megaK f t)) l
lemma granule_limit' :
 - (P.echoFoot:ℤ) ≤ (X t) j ∧ (X t) j ≤ P.echoFoot:=by
  have hx:=(P.lodge (P.megaK f t))
  obtain h|h:=pivot_alone (P.granule (P.megaK f t)) l j <;>
      rw [h] <;> unfold granule <;> omega
lemma rose_align(p:f ≤ s)(h:s≤t):
 ∃ a : Cover,P.clockPlate s t (P.roseRoot f s l) =
          X t + P.sidesPerTick • a ∧
 (P.roomy:ℤ) ≤ a j ∧
 a j + P.roomy ≤ P.gum (w s) s t := by
 let u:ℕ:= P.par.R.L.val^(t-s)
 have hp:1≤u:=pow_pos P.par.R.L.property _
 have hp': (1:ℤ)≤ u:=by exact_mod_cast hp
 have odd : Odd P.par.R.L.val:=P.par.R.odd_side
 obtain ⟨z,d⟩:=P.charge_race f s t p h l odd
 let a:Cover:=z + fun _=> (↑(2*u*P.roseMargin):ℤ)
 have v: P.clockPlate s t (P.roseRoot f s l)= X t + κ • a:=by
    ext i
    have ht:= congrFun d i
    have lt: nodeC (P.roseRoot f s l) i=nodeC (P.rootSpace f s l) i + 2*P.roseJump:=by
       simp only [nodeC,roseRoot,two_smul,Pi.add_apply]; ring
    change (u • nodeC (P.roseRoot f s l)) i=_
    change (u • nodeC (P.rootSpace f s l)) i=_ at ht
    rw [Pi.smul_apply, lt,smul_add, ← Pi.smul_apply,ht]
    dsimp only [a,Pi.smul_apply,Pi.add_apply]; simp only [nsmul_eq_mul,roseJump]
    push_cast; ring
 refine ⟨a,v,?_⟩
 let Z:=nodeC (P.roseRoot f s l) j
 have eq: (u:ℤ)*Z = (X t) j + (κ:ℤ)*(a j):=by
   have e:=congrFun v j
   change (u • nodeC _) j=_ at e
   simpa only [Pi.smul_apply,Pi.add_apply,nsmul_eq_mul,Pi.mul_apply,Pi.natCast_apply] using e
 have xp: - (P.echoFoot:ℤ) ≤ (X t) j ∧ (X t) j ≤ P.echoFoot:= P.granule_limit' j l
 have ht:=P.rose_sundial j l (f:=f) (s:=s)
 have p0:(P.roomy:ℤ)*κz+(P.echoFoot:ℤ) ≤ P.roseJump:=by
   unfold roseJump roseMargin
   rw [Nat.cast_mul κ, Nat.cast_add P.roomy]
   linarith only [le_mul_of_one_le_left  (Int.natCast_nonneg P.echoFoot)
       (show (1:ℤ)≤κz from P.stepPos)]
 have z₁:(P.roseJump:ℤ)≤Z:=ht.1
 have z₂: Z+ P.roseJump ≤ w s:=ht.2
 exact interval_slide P.stepPos hp' p0 (Int.natCast_nonneg _)
   (Int.natCast_nonneg _) z₁ z₂ xp eq (Nat.cast_mul u (w s))

private lemma rose_le_β :
 ∀ᶠ s:ℕ in atTop,(P.roseWide j s :ℝ) ≤ hat P.par.R.L P.par.x s :=by
 let c:=4+P.roseFlat
 filter_upwards [P.earns_widthT j 1 zero_lt_one c,
   (turnover P.par).eventually (coin_budget (a:=0) (b:=1) (c:=0)
      (d:=1) (e:=0) (f:=0) (Or.inl zero_lt_one) 1 1 zero_lt_one)] with s hq hp
 rw [coinY (P.f_here s), one_mul,one_mul] at hp
 have hg:1≤ q s:=by unfold axleQ repeatD; omega
 have ht:w s ≤ (4+P.roseFlat)*q s:=by
    unfold roseWide; rw [add_mul]; gcongr
    exact Nat.le_mul_of_pos_right P.roseFlat hg
 refine le_trans ?_ (hq.trans hp.le)
 rw [←Nat.cast_mul]; exact_mod_cast ht

abbrev rosePad(s:ℕ):= P.roseWide j s * P.macroStep s
-- radius, orientation card
lemma rose_rapid :
  Tendsto (fun n:ℕ=>2^n*P.rosePad j (2*n)) atTop (𝓝 0):=by
 let m:= timeMesh P.par
 let z:ℝ:=2
 let y:ℝ:=m.L
 have hz:1<z:=by unfold z; norm_num
 have hy: z≤y:= by
   unfold z y; exact_mod_cast m.Llarge
 let b:=P.par.x
 let d:=2*billX L
 let k:ℝ:=m.base
 have hh:Tendsto (fun n:ℕ=>(n:ℝ)/z^n) atTop (𝓝 0):=by
    simpa only [pow_one] using tendsto_pow_const_div_const_pow_of_one_lt 1 hz
 have h0:Tendsto (fun n:ℕ=>(1:ℝ)/z^n) atTop (𝓝 0):=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt hz)
 let V(n:ℕ):= (b+n*d)*k/z^n
 have ht:Tendsto V atTop (𝓝 0):=by
    have h:=((h0.const_mul (b*k)).add (hh.const_mul (d*k)))
    simp only [mul_zero,add_zero] at h
    exact h.congr (fun n=> by unfold V; ring)
 have hn:Tendsto (fun n:ℕ=>2*n) atTop atTop:=tendsto_atTop_mono
    (f:=fun n:ℕ=>n) (fun n=> by omega) tendsto_id
 refine squeeze_zero' (Eventually.of_forall (fun n=>show 0≤ 2^n* P.rosePad j (2*n) from mul_nonneg (by positivity) (mul_nonneg (Nat.cast_nonneg _) (P.macroStep_pos _).le))) ?_ ht
 have hw:=hn.eventually (P.rose_le_β j)
 filter_upwards [hw] with n h
 have hd:hat L P.par.x (2*n)=b+(n:ℝ)*d:=by unfold b d hat; rw [Nat.cast_mul, Nat.cast_ofNat]; ring
 have hs:P.macroStep (2*n)=k/(y^(n+n)):=by
    unfold macroStep mill k y
    rw [two_mul,NNReal.coe_div,NNReal.coe_pow,NNReal.coe_natCast]
 rw [hd] at h
 have hc:0≤ k:=NNReal.coe_nonneg _
 calc 2^n*P.rosePad j (2*n) ≤ z^n*((b+(n:ℝ)*d)*P.macroStep (2*n)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h (P.macroStep_pos _).le) (by positivity)
      _ ≤ z^n*((b+(n:ℝ)*d)*(k/z^(n+n))) :=by
          rw [hs]; have hp:= (Nat.cast_nonneg _).trans h; gcongr
      _ = _ := by unfold V; rw [pow_add]; field_simp


abbrev gPosition(t:ℕ)(a:Cover): Vantage:=fun j=>
 (a j:ℝ) * P.macroStep t / P.sidesPerTick
lemma gPosition_clock (h:s≤t) (y:Cover):
 P.gPosition t (P.clockPlate s t y)=P.gPosition s (nodeC y):=
  funext (fun j=>congrArg (·/(κ:ℝ)) (P.lap_quote j s t h y))
lemma gPosition_lined (y a z:Cover)(h:y=z+P.sidesPerTick • a):
 P.gPosition t y=P.gPosition t z+ P.meshPose t a:=by
  funext i
  have ht:(κ:ℝ)≠0:=(Nat.cast_pos.mpr P.sides_pos).ne'
  rw [Pi.add_apply, P.pose_w,h]
  unfold gPosition; rw [Pi.add_apply,Pi.smul_apply,nsmul_eq_mul,
       Int.cast_add,Int.cast_mul,Int.cast_natCast]
  field_simp

abbrev roseHub(f s:ℕ)(l:List Axis):=P.gPosition s (nodeC (P.roseRoot f s l))
abbrev granPos(f v:ℕ)(l:List Axis):=
 P.gPosition v (pivotQ (P.granule (P.megaK f v)) l)
lemma granPos_line(p:s≤v)(a:Cover)
 (q₁:P.clockPlate s v (P.roseRoot f s l)=X v + P.sidesPerTick • a):
 P.roseHub f s l= P.granPos f v l + P.meshPose v a:=
  (P.gPosition_clock p _).symm.trans (P.gPosition_lined _ _ _ q₁)
-- permit payment through heat at hub between 0 and width

lemma roseHub_in:
 0≤ P.roseHub f s l j ∧ P.roseHub f s l j ≤ P.rosePad j s:=by
 let y:=nodeC (P.roseRoot f s l) j
 have hp:0≤y:= (Int.natCast_nonneg P.roseJump).trans (P.rose_sundial j l).1
 have h:y ≤ w s:= by
   have h: y+ P.roseJump ≤ w s:=(P.rose_sundial j l).2; omega
 have ht: 1≤ (κ:ℝ):= by exact_mod_cast P.sides_pos
 exact ⟨div_nonneg (mul_nonneg (show 0≤ (y:ℝ) from by exact_mod_cast hp) (P.macroStep_pos _).le) (Nat.cast_nonneg _),
     (div_le_self (mul_nonneg (show 0≤ (y:ℝ) from by exact_mod_cast hp) (P.macroStep_pos _).le) ht).trans
       (mul_le_mul_of_nonneg_right (by exact_mod_cast h) (P.macroStep_pos s).le)⟩
lemma gum_tick(p:s≤t) {m:ℕ}:
  (P.gum m s t:ℝ)*P.macroStep t = m*P.macroStep s:=by
 unfold gum; rw [Nat.cast_mul,Nat.cast_pow, mul_comm _ (m:ℝ), mul_assoc,P.daysF _ _ p]
lemma granPos_tiny:
 |P.granPos f v l j|≤P.echoFoot * P.macroStep v:=by
 have ht:=P.granule_limit' j (t:=v) (f:=f) l
 unfold granPos gPosition
 rw [abs_div, abs_mul, abs_of_pos (P.macroStep_pos _),
     abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) P.sidesPerTick)]
 exact (div_le_self (by have h:=P.macroStep_pos v; positivity)
     (show 1≤ (κ:ℝ) from by exact_mod_cast P.sides_pos)).trans
     (mul_le_mul_of_nonneg_right (by exact_mod_cast (abs_le.mpr ht)) (P.macroStep_pos v).le)
lemma granPos_zero:
 Tendsto (fun v=> P.granPos f v l) atTop (𝓝 0):=by
 apply tendsto_pi_nhds.mpr; intro j; apply squeeze_zero_norm (a:=fun v=> P.echoFoot*P.macroStep v)
 · intro v
   rw [Real.norm_eq_abs]; exact P.granPos_tiny j l
 simpa only [mul_zero] using P.macroStep_zero.const_mul (P.echoFoot:ℝ)
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
