import SatinPP.Drill
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3500
set_option maxHeartbeats 650000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six MacroGrid

open TopologicalSpace SatinJets
variable (P:Spine)(x:P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "G"=> P.ManyF 3 ξ
local notation "Γ"=> P.cartage 3 ξ
local notation "Θ"=> P.seasons 3 ξ
local notation "E"=> (Θ).E
local notation "κ"=> P.wealth 3 ξ
local notation "D" s:max=>P.lengthP s
local notation "F%" s:max=> P.pointEra s
variable (V:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))

-- τ-fee
abbrev bell (s:ℕ):Vantage:=P.meshPose s (P.runP (P.pointEra s) s 1 0)
def arrears (s:ℕ):ℝ:= (P.bell s 3)/(D s)
lemma arrears_t: Tendsto P.arrears atTop (𝓝 1):= by
 let y(s:ℕ): ℝ:= P.persistN (P.plannedK s)
 let z(s:ℕ):ℝ:= P.plannedK s

 have h:Tendsto (fun i=> y i/z i) atTop (𝓝 0):=
    squeeze_zero (fun s=>div_nonneg (P.tiny_one_ledger s _|>.1) (P.plan_p s).le) (fun s=> div_le_div_of_nonneg_right (P.tiny_one_ledger s _|>.2) (P.plan_p s).le) (tendsto_const_nhds.div_atTop (a:=(P.echoFoot:ℝ)) P.planned_grows)
 have t:= (tendsto_const_nhds (x:=(1:ℝ))).sub h; rw [sub_zero] at t; apply t.congr; intro i
 unfold arrears bell lengthP runP
 rw [P.tile_effective _ _ (P.era_le i),←P.offeringF (P.era_le i)]
 let b:=z i; let a:=y i; let c:ℝ:= P.sidesPerTick; let d:=P.macroStep i
 have p:0<b:=P.plan_p i; have q:0<d:=P.macroStep_pos _; have r:0<c:=Nat.cast_pos.mpr P.sides_pos
 change 1-a/b=(b*d/c-a*d/c)/(b*d/c)
 field_simp

abbrev sprig (s:ℕ)(a:ℝ)(σ:ℝ) := (σ:ℂ) • κ (V 3 [] ((D s)*a))
structure VelvetGlass (r:ℕ→ℕ)(σ:ℕ→ℝ): Prop where
 climbs:StrictMono r
 scarce:Tendsto (fun i=>P.lengthP (r i)) atTop (𝓝 0)
 station: P.Spots r x
 glass {t:ℕ→ℕ}(u:Tendsto t atTop atTop)
    {a b:ℕ→ℝ}{c d:ℝ}(u₀:1<c)(z:1<d)(p:Tendsto a atTop (𝓝 c))(q:Tendsto b atTop (𝓝 d))
    {y:ℕ→ Vantage}{w:Vantage} (f:Tendsto y atTop (𝓝 w)):
   Tendsto (fun i=>inner ℂ
       (P.sprig x V (r (t i)) (a i) (σ (t i)))
       (Γ ((D (r (t i))) • y i) (P.sprig x V (r (t i)) (b i) (σ (t i))))) atTop
       (𝓝 (gloss (starLane 3 w (c+d))))
def Silhouette :Prop:=∃ r σ, P.VelvetGlass x V r σ
-- warming lens at time one
variable {A:ℕ→P.Apron}(R:P.Radiates x A V)

abbrev wakePose(s:ℕ): Vantage:= fun _=>P.lengthP s
local notation "U⚘" s:max=> P.wakePose s
local notation "Ξ" => κ
def CandleLoan (s:ℕ)(δ:ℝ):Prop:= ∃ b:ℝ, b≠0 ∧ dist (Γ (U⚘ s) (Ξ (V 3 [] (D s)))) ((b:ℂ) • P.invoiceV x (P.pointEra s) s s 1) ≤ δ*|b|
abbrev lampMove (s:ℕ):Vantage:= P.wakePose s-P.bell s
local notation "Lk" s:max=>P.lightKet x 3 s []
local notation "D₀"=>Real.sqrt min7
local notation "D₁" s:max=> Real.sqrt (P.dBase s)
local notation "Fℓ" s:max=>P.invoiceV x (P.pointEra s) s s 1
lemma margin₀:0<D₀:=Real.sqrt_pos.mpr min_budget
lemma arrears_val (s:ℕ): P.arrears s * P.lengthP s=P.bell s 3:= div_mul_cancel₀ _ (P.lengthP_pos _).ne'
lemma invoice_pose(s:ℕ)(p:P.reached (P.pointEra s) s): (Fℓ s) = Γ (P.bell s) ((D₁ s:ℂ) • ((Lk s) (P.arrears s))):= by
 rw [P.invoice_flight x _ _ _ p,one_smul]
 have hpos:(D₁ s:ℂ) ≠ 0:=Complex.ofReal_ne_zero.mpr ((Real.sqrt_pos.mpr (P.lofty s)).ne')
 unfold lightKet factor; rw [mul_comm (P.lengthP s) (P.arrears s),P.arrears_val,Apron.pivot_nil,smul_smul,mul_div_cancel₀ _ hpos] 


lemma tiny_loan {s:ℕ}{δ:ℝ}(p:P.reached (F% s) s)(h:P.CandleLoan x V s δ):
 ∃ σ:ℝ, dist (Γ (P.lampMove s) (P.sprig x V s 1 σ)) ((Lk s) (P.arrears s)) ≤ δ/D₀ := by
 obtain ⟨b,e,y⟩:=h
 let c:=P.bell s; let v:G:=Ξ (V 3 [] (D s))
 let t:=Γ (P.lampMove s) v
 let z:= (Lk s) (P.arrears s)
 let h₀:=D₁ s
 have he:Γ (U⚘ s) v=Γ c t:= by
    rw [show (U⚘ s)=c+P.lampMove s from (by unfold c lampMove;abel),P.cart_paves];rfl
 rw [show (κ) (V 3 [] (D s))=v from rfl,he,P.invoice_pose x s p, ←map_smul,smul_smul,dist_eq_norm,←map_sub,P.cart_norm] at y
 let d:=b*h₀
 have hy: ‖t-(d:ℂ) • z‖ ≤ δ*|b|:= by unfold d;rw [Complex.ofReal_mul];exact y
 refine ⟨d⁻¹,?_⟩
 have H:D₀≤ h₀:=Real.sqrt_le_sqrt (P.dBase_interval s).1
 have w:d≠0:=mul_ne_zero e (lt_of_lt_of_le margin₀ H).ne'
 unfold sprig;rw [dist_eq_norm,mul_one,map_smul]
 let θ:=‖(↑d⁻¹:ℂ) • t-z‖
 have r: |b| * (h₀ * θ) ≤ δ*|b|:= by
    have u: |b| *h₀ = ‖(d:ℂ)‖ := by
       rw [Complex.norm_real,Real.norm_eq_abs, show |d| =|b| *|h₀| from abs_mul ..,abs_of_pos (margin₀.trans_le H)]
    unfold θ; rw [←mul_assoc,u,←norm_smul,smul_sub, Complex.ofReal_inv,smul_smul,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr w),one_smul]
    exact hy
 rw [le_div_iff₀ margin₀, mul_comm]
 exact (mul_le_mul_of_nonneg_right H (norm_nonneg _)).trans (le_of_mul_le_mul_left (r.trans_eq (mul_comm ..)) (abs_pos.mpr e))

abbrev led (s:ℕ)(a:ℝ):= P.arrears s+(a-1)
abbrev refract (s:ℕ)(a:ℝ)(σ:ℝ):= Γ (P.lampMove s) (P.sprig x V s a σ)
local notation "L%" s:max => fun a=> (Lk s) (P.led s a)
include R
lemma warms (s:ℕ)(σ:ℝ){a:ℝ}(h:P.faceWidth s ≤ P.arrears s)(e:1≤a):
 dist (P.refract x V s a σ) ((Lk s) (P.led s a)) ≤ dist (P.refract x V s 1 σ) ((Lk s) (P.arrears s)):= by
 let d:=D s; have t:=P.lengthP_pos s; let z:=(d*(a-1)).toNNReal
 have y: P.refract x V s a σ=E z (P.refract x V s 1 σ):= by
    unfold refract sprig; rw [mul_one,P.warm_drive,map_smul (E z)]
    rw [P.height_pass x 3 V R [] t (le_mul_of_one_le_right t.le e)]
    unfold z d;rw [mul_sub,mul_one]
 have k:(Lk s) (P.led s a) = E z ((Lk s) (P.arrears s)):= by
    rw [P.lamplight x 3 s [] h (le_add_of_nonneg_right (sub_nonneg.mpr e))]
    rw [add_sub_cancel_left]

 rw [y,k,dist_eq_norm,← map_sub,dist_eq_norm]
 exact (ContinuousLinearMap.le_opNorm ..).trans (mul_le_of_le_one_left (norm_nonneg _) ((Θ).shrinks _))

omit R in
private lemma exchange {G₀:Hilbert} {a b a' b':ℕ→ G₀}
  {y:ℂ}(L:Tendsto (fun i=>inner ℂ (a i) (b i)) atTop (𝓝 y))
   (u:Tendsto (fun i=>dist (a i) (a' i)) atTop (𝓝 0))
   (v:Tendsto (fun i=>dist (b i) (b' i)) atTop (𝓝 0))
  (A:∃ z:ℝ,∀ᶠ i in atTop, ‖a i‖ ≤ z)
  (B:∃ z:ℝ,∀ᶠ i in atTop, ‖b i‖ ≤ z):
   Tendsto (fun i=>inner ℂ (a' i) (b' i)) atTop (𝓝 y):=by
 obtain ⟨w,h⟩:=A; obtain ⟨z,p⟩:=B
 have hx:= (u.mul_const z).add ((u.const_add w).mul v)
 rw [zero_mul,mul_zero,zero_add] at hx
 have hl:Tendsto (fun i=>‖inner ℂ (a i) (b i)-inner ℂ (a' i) (b' i)‖) atTop (𝓝 0):=by
    refine squeeze_zero' (Eventually.of_forall fun i=>norm_nonneg _) ?_ hx
    filter_upwards [h,p] with i h' p'
    refine (norm_sub_le_norm_sub_add_norm_sub _ (inner ℂ (a' i) (b i)) _).trans ?_

    rw [←inner_sub_left,←inner_sub_right,dist_eq_norm,dist_eq_norm]
    have hg :=norm_le_norm_add_norm_sub (a i) (a' i)
    exact add_le_add ((norm_inner_le_norm ..).trans (mul_le_mul_of_nonneg_left p' (norm_nonneg _))) ((norm_inner_le_norm ..).trans (mul_le_mul_of_nonneg_right (hg.trans (add_le_add_left h' _)) (norm_nonneg _)))
 have hy:=L.sub (tendsto_zero_iff_norm_tendsto_zero.mpr hl)
 rw [sub_zero] at hy; exact hy.congr fun i=>sub_sub_cancel _ _
omit R in
lemma twirl (w y:Vantage)(v v₀:G):
    inner ℂ v (Γ y v₀)=inner ℂ (Γ w v) (Γ y (Γ w v₀)):=by
 rw [←ContinuousLinearMap.adjoint_inner_right,P.cart_reverses, ←ContinuousLinearMap.comp_apply (Γ y), ←ContinuousLinearMap.comp_apply (Γ (-w)),←P.cart_paves, ←P.cart_paves, show -w+(y+w)=y by abel]

variable (J:P.Ellis 3 x) {r:ℕ→ℕ}
include J
lemma auditions (h:StrictMono r)(S:P.Spots r x) {δ:ℕ→ℝ}(u:Tendsto δ atTop (𝓝 0))
 (L:∀ᶠ i in atTop, P.CandleLoan x V (r i) (δ i)): ∃ σ,P.VelvetGlass x V r σ:= by
 have hy:= h.tendsto_atTop
 have hx:= hy.eventually (P.ready_granule (P.roomy))
 have ht:∀ᶠ i in atTop, ∃ w:ℝ,
    dist (P.refract x V (r i) 1 w) ((Lk (r i)) (P.arrears (r i))) ≤ δ i/D₀ := by
    filter_upwards [L,hx] with i f p; exact P.tiny_loan x V p f
 -- choose
 obtain ⟨N,z⟩:=Filter.eventually_atTop.mp ht

 choose! σ e using z
 refine ⟨σ,h,P.flight_soon.comp (P.future_payment.comp hy), S,?_⟩
 intro t v a b c d h₁ h₂ p q y w f
 let s:=r ∘ t
 have hc:=hy.comp v
 have pe:=P.arrears_t.comp hc
 have he {a:ℕ→ℝ}{z:ℝ}(p':Tendsto a atTop (𝓝 z)): Tendsto (fun i=>P.led (s i) (a i)) atTop (𝓝 z):= by
    simpa only [show (1:ℝ)+(z-1)=z by ring] using! pe.add (p'.sub (tendsto_const_nhds (x:=(1:ℝ))))
 have c₀:0<c:=zero_lt_one.trans h₁; have d₀:0<d:=zero_lt_one.trans h₂
 let Z(a:ℕ→ℝ)(i):= (Lk (s i)) (P.led (s i) (a i))
 let U(i):=Γ (D (s i) • y i)
 have hv:Tendsto (fun i=>inner ℂ (Z a i) (U i (Z b i))) atTop (𝓝 (gloss (starLane 3 w (c+d)))):=
    P.crystal x 3 J (fun p=> (S p).comp v) hc [] (he p) c₀ [] f (he q) d₀
 let Y(a:ℕ→ℝ)(i):= P.refract x V (s i) (a i) (σ (t i))

 have ee {a:ℕ→ℝ}{z:ℝ}(u':1<z)(p':Tendsto a atTop (𝓝 z)):Tendsto (fun i=>dist (Z a i) (Y a i)) atTop (𝓝 0):=by
    have hb:= (u.comp v).div_const D₀
    rw [zero_div] at hb
    apply squeeze_zero' (Eventually.of_forall (fun _=>dist_nonneg)) _ hb
    filter_upwards [v.eventually_ge_atTop N,p'.eventually (le_mem_nhds u'),(P.face_t.comp hc).eventually_lt pe zero_lt_one] with i n₁ n₂ n₃
    rw [dist_comm]
    exact (P.warms x V R (s i) (σ (t i)) n₃.le n₂).trans (e (t i) n₁)
 have hx: P.Spots s x:=fun p=>(S p).comp v
 obtain ⟨C,uC,C'⟩:=P.rough_bound x 3 hx hc [] zero_lt_one
 have R': Tendsto (fun i=>inner ℂ (Y a i) (U i (Y b i))) atTop (𝓝 (gloss (starLane 3 w (c+d)))):= by
    refine exchange hv (ee h₁ p) ((ee h₂ q).congr (fun i=>?_)) ⟨C,?_⟩ ⟨C,?_⟩

    · unfold U;rw [dist_eq_norm,dist_eq_norm, ←map_sub,P.cart_norm]
    · filter_upwards [C',(he p).eventually (le_mem_nhds h₁)] with i p q;exact p _ q
    filter_upwards [C',(he q).eventually (le_mem_nhds h₂)] with i p q
    unfold U; rw [P.cart_norm]; exact p _ q
 exact R'.congr (fun i=>(P.twirl x (P.lampMove (s i)) ((D (s i)) • y i) _ _).symm)

