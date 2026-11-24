import YM.SU5.CompassRose.Piazza

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 500000
set_option quotPrecheck false
set_option linter.unusedSectionVars false

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine

open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine Preparation.Yoke
open CF.Velvet CF.Pannier.Chancel CF.Pannier.Chancel.Rous Pressure
open YM.Stationary (Gaia)
open Onyx Regis.Circuit Regis.Head Regis.Head.Brecht Exterior Hiro

namespace Rose
open EmberWind Jewel
open Lamour Lamour.Bridge
variable (P:Spine)(s:ℕ)(A:ℝ)(β:ℕ→ℝ)
local notation "K"=> P.calibration
local notation "R" s:max=> sPow P.par s A
local notation "K!" f:max => Papal.household P.calibration f
local notation "P$" s:max => P.eReadL s
local notation "ζ⇒" => P.reflectTest 3
local notation "M$" => P.halfShift 3
local notation "lamp" X:max => temp (hat P.par.R.L P.par.x X)
open Fixture Shuttle Arrival
open Aria Casting DoseTravel
namespace Basilica
variable (x:P.Spectrum0 3)(J:P.Ellis 3 x)(j:Axis)
local notation "Δ" D:max=> Apron.realWidth P D j
local notation "ξ"=> P.advocate 3 x j
local notation "Z"=> P.ManyF j ξ
local notation "H"=> P.seasons j ξ
local notation "G" p:max=> P.cartage j ξ p

section fees
variable (B D:P.Apron) (c:ℝ) (p q:Vantage)
def Past : Z:= (G p) ((H).E ((c-p j-Δ B).toNNReal) (glareY x B j))
def FutureC : Z:= (G p) ((H).E ((p j-c-Δ B).toNNReal) (flashY x B j))
lemma continuing : Continuous (Past P x j B c) ∧ Continuous (FutureC P x j B c):= by
 constructor; · exact P.caravan j ξ id _ continuous_id (((H).continuousE _).comp (continuous_real_toNNReal.comp ((continuous_const.sub (continuous_apply j)).sub continuous_const)))
 exact P.caravan j ξ id _ continuous_id (((H).continuousE _).comp (continuous_real_toNNReal.comp (((continuous_apply j).sub continuous_const).sub continuous_const)))
include J
lemma two_born (i:p j+ Δ B<c)(k:c< q j- Δ D) : P.bodyPair x B D p q=inner ℂ (Past P x j B c p) (FutureC P x j D c q):=by -- Castle.first_heart extension
 let a:= c-p j-Δ B; let b:= q j-c-Δ D; let u:=glareY x B j; let v':= flashY x D j
 have h1:0<a:=by unfold a; linarith
 have h2:0<b:=by unfold b; linarith
 have he: (q-p) j-(Δ B+Δ D)=a+b:=by unfold a b; simp only [Pi.sub_apply]; ring
 rw [P.bodyPair_fwd x B D j p q J (sub_pos.mp (show 0<(q-p) j-_ from he.symm ▸ add_pos h1 h2)), he]; unfold Past FutureC; rw [Real.toNNReal_add h1.le h2.le,(H).time,ContinuousLinearMap.comp_apply,P.warm_drive,←OS.Semigroup.swing]; let d:= (H).E b.toNNReal v'; symm; rw [←ContinuousLinearMap.adjoint_inner_right,P.cart_reverses]; rw [←ContinuousLinearMap.comp_apply,←P.cart_paves,add_comm (-p),sub_eq_add_neg q] -- right adjoint
end fees

open MacroGrid
section ledgers
local notation "µ" s:max f:max => P.meshPose s f
variable (B D:P.Apron)(F U:SampleDose)
def weightP (F:SampleDose)(s:ℕ)(v:Cover):ℝ:=(P.macroStep s)^4*F.val (µ s v)
def tray {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E](f:Vantage→E):E:=∑ i∈ P.usedGrid s F, weightP P F s i • f (µ s i)
-- Universe limit of MacroGrid lemma to Type. may not cause issue
lemma quadrature {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E](f:Vantage→E)(p:Continuous f) : Tendsto (fun s=> tray P s F f) atTop (𝓝 (∫ x:Vantage,F.val x • f x)):=by
 let g(x:Vantage):= F.val x • f x; let TX(t:ℕ):=P.usedGrid t F
 apply (rSum_limit P.macroStep P.macroStep_zero g (F.smooth.continuous.smul p) P.macroStep_pos F.budget.smul_right).congr
 intro i; let b:=P.macroStep i; let k(v:Cover):=g (µ i v); have he(v:Cover)(h:v∉ TX i): F.val (µ i v)=0:=by by_contra n; exact h ((P.usedPose i F v).2 (subset_closure n))
 have ht(v:Cover)(h:v∉ TX i):k v=0:=by unfold k g; rw [he v h,zero_smul]
 change (∫ x,floorCost b k x)=_; rw [(room_price b (P.macroStep_pos i) k (TX i) ht).2]; unfold k g; simp_rw [Finset.smul_sum,smul_smul,show Fintype.card Axis=4 from rfl]; rfl

abbrev clockP (B:P.Apron)(j:Axis):ℝ:= B.realWidth P j
-- domain checks plus Mink arrangement with dominant axis 2 and time=3. independent of θ state
structure Plaza (p q:Vantage) : Prop where
  order_ (j:Axis) : clockP P B j+clockP P D j < q j-p j
  room_: q 3 - p 3 + clockP P B 3 + clockP P D 3 < q 2 - p 2 - clockP P B 2-clockP P D 2
include J
lemma pave_gram (u v:Cover) (b:B.s≤ s)(t:D.s≤ s)(e:Plaza P B D (µ s u) (µ s v)) : P.singleState 3 s x ((P.issuing s B u)*(P.issuing s D v))=P.bodyPair x B D (µ s u) (µ s v):=by
 let A:= usher B D; let L:=[false,true]; let f:= usher u v; have he(i:Axis):P.Turnstile i A L (P.gridSpot s ∘ f):=by
    have ht(i): P.gridSpot s (f i)= usher (µ s u) (µ s v) i:=by cases i <;> rfl
    rw [show P.gridSpot s ∘ f=_ from (show P.gridSpot s ∘ f= usher (µ s u) (µ s v) from funext ht)]; exact P.orderPair B D i _ _ (e.order_ i)
 have hf:P.Plenum A L (P.gridSpot s ∘ f):=⟨fun i=> ⟨_,List.Perm.refl _,he i⟩⟩
 have hx: P.fullScroll s A f L=P.issuing s B u * P.issuing s D v:=by change P.issuing _ _ _*(P.issuing _ _ _*1)=_; rw [mul_one]
 -- top authority common axes
 unfold bodyPair; rw [←hx]; have hp:P.gridSpot s ∘ f=usher (µ s u) (µ s v):=funext fun i=> by cases i <;> rfl
 rw [←hp]; exact P.spot_full x _ _ f J s (fun i _=> by cases i; exact b; exact t) (he 3) hf
-- constant term alone. keep bodyOne even when nonzero
abbrev ESingle :ℂ:= P.bodyOne x B 0
lemma tray_single (v:Cover)(a:B.s≤ s): P.singleState 3 s x (P.issuing s B v)= ESingle P x B:= (P.castAt_price x J B a v).trans ((P.bodyOne_price x J B _).trans (P.bodyOne_price x J B 0).symm)
lemma solo_beam : Tendsto (fun s=> P.singleState 3 s x (P.prepared s B F)) atTop (𝓝 ((∫ k:Vantage,F.val k) • ESingle P x B)):=by
 let V(_ : Vantage):=ESingle P x B; have he:Tendsto (fun s=> tray P s F V) atTop (𝓝 ((∫ k:Vantage,F.val k) • ESingle P x B)):=by
    have hp:= quadrature P F V continuous_const; rw [show (∫ x:Vantage,F.val x • V x)= _ from integral_smul_const ..] at hp; exact hp
 apply he.congr'; filter_upwards [eventually_ge_atTop B.s] with s e; unfold prepared tray; rw [map_sum]; apply Finset.sum_congr rfl; intro i _; rw [map_smul,tray_single P s x J B i e]; exact (Complex.coe_smul ..).symm
variable (c:ℝ) (h:∀ i∈tsupport F.val,i j+ clockP P B j<c)(t:∀ i∈tsupport U.val,c< i j-clockP P D j)(q:∀ p∈tsupport F.val, ∀ q∈tsupport U.val,Plaza P B D p q)
include c j h t q
lemma double_tray (a:B.s≤ s)(d:D.s≤ s): P.singleState 3 s x ((P.prepared s B F)*(P.prepared s D U))=inner ℂ (tray P s F (Past P x j B c)) (tray P s U (FutureC P x j D c)):=by
 unfold prepared tray; rw [sum_mul,sum_inner]; simp_rw [mul_sum,map_sum,inner_sum]; apply sum_congr rfl; intro i hv; apply sum_congr rfl; intro l he
 let b:Vantage:= µ s i; let d':= µ s l; let Q: b∈ tsupport F.val:= (P.usedPose s F i).1 hv; let T:d'∈ tsupport U.val:=(P.usedPose s U l).1 he
 rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,map_smul,map_smul,pave_gram P s x J B D i l a d (q b Q d' T), two_born P x J j B D c b d' (h _ Q) (t _ T)]; unfold activation; rw [← Complex.coe_smul (weightP _ _ s i :ℝ),← Complex.coe_smul (weightP _ _ s l:ℝ),inner_smul_left,inner_smul_right,Complex.conj_ofReal]; try rfl
lemma duo_beam : Tendsto (fun s=>P.singleState 3 s x ((P.prepared s B F)*(P.prepared s D U))) atTop (𝓝 (inner ℂ (DoseTravel.beam Z F (Past P x j B c)) (DoseTravel.beam Z U (FutureC P x j D c)))):=by
 unfold DoseTravel.beam; simp_rw [Complex.coe_smul]; apply ((quadrature P F (Past P x j B c) (continuing P x j B c).1).inner (quadrature P U (FutureC P x j D c) (continuing P x j D c).2)).congr'; filter_upwards [eventually_ge_atTop B.s,eventually_ge_atTop D.s] with s a d; exact (double_tray P s x J j B D F U c h t q a d).symm
end ledgers

section smear_placement
variable (B D:P.Apron) (p q:Vantage) (F U: SampleDose)
local notation "↑t" X:max => clockP P X 3
abbrev whole (F U:SampleDose): Prop:= ∀ x∈ tsupport F.val,∀ y∈tsupport U.val, Plaza P B D x y
lemma stable (u:Plaza P B D p q) : ∀ᶠ z:Vantage×Vantage in 𝓝 (p,q), Plaza P B D z.1 z.2:=by
 let Ω₂(z: Vantage×Vantage) (i: Axis):ℝ:= z.2 i-z.1 i
 have he(i:Axis): Continuous (fun z=>Ω₂ z i):= ((continuous_apply i).comp continuous_snd).sub ((continuous_apply i).comp continuous_fst)
 let g(z:Vantage×Vantage):= Ω₂ z 3 + ↑t B + ↑t D
 let h(z:Vantage×Vantage):= Ω₂ z 2 - clockP P B 2-clockP P D 2; have hv: ∀ᶠ z in 𝓝 (p,q),g z<h z:= Filter.Tendsto.eventually_lt (ContinuousAt.tendsto (f:=g) ((((he 3).add continuous_const).add continuous_const).continuousAt)) ((((he 2).sub continuous_const).sub continuous_const).tendsto (p,q)) u.room_
 filter_upwards [hv,Filter.eventually_all.mpr (fun i: Axis=>(show ∀ᶠ z in 𝓝 (p,q),clockP P B i+clockP P D i < Ω₂ z i from ((he i).tendsto ..).eventually (lt_mem_nhds (u.order_ i))))] with z p h; exact ⟨h,p⟩
-- even on full widths. authentic physical Eu separation in time & space.
-- 'Mink.spacelike' here domain statement, not commutativity of continued fields!
abbrev Far (A A':Set Vantage): Prop:=∀ x∈ A,∀ y∈ A', (∀ i:Axis,x i<y i) ∧ (WithLp.toLp 2 (y-x):E4)∈Mink.spacelike
lemma far_in (h:whole P B D F U) : Far (P.spacePrice B F) (P.spacePrice D U):=by
 intro x p y u; simp only [spacePrice,Set.mem_iUnion] at p u; obtain ⟨a,v,p⟩:=p; obtain ⟨b,w,u⟩:=u; have hx(i:Axis): |x i - a i| ≤ clockP P B i:=p i; have hu(i:Axis): |y i-b i| ≤ clockP P D i:= u i; have he:= h a v b w; have ht(i:Axis): x i< y i:=by linarith only [(abs_le.mp (hx i)).2,(abs_le.mp (hu i)).1, he.order_ i]
 refine ⟨ht,(Mink.lateral _).mpr ?_⟩; let d:E4:=WithLp.toLp 2 (y-x)
 have hp:y 2-x 2 ≤ ‖spatial d‖:=(show |y 2-x 2|≤ ‖spatial d‖ from PiLp.norm_apply_le (spatial d) (2:Fin 3))|>.trans' (le_abs_self _)
 change |y 3-x 3| < ‖spatial d‖; rw [abs_of_pos (sub_pos.mpr (ht 3))]; linarith only [(abs_le.mp (hx 2)).2, (abs_le.mp (hu 2)).1,(abs_le.mp (hx 3)).1,(abs_le.mp (hu 3)).2,hp,he.room_]
lemma far_disjoint {A X:Set Vantage} (h:Far A X): Disjoint A X:= Set.disjoint_left.mpr (fun _ i j=> lt_irrefl _ ((h _ i _ j).1 0))
lemma price_compact : IsCompact (P.spacePrice B F):=by
 exact P.cost_isCompact B F

local notation "V⇐" c:max F:max => DoseTravel.beam Z F (Past P x j B c)
local notation "V⇒" c:max F:max => DoseTravel.beam Z F (FutureC P x j D c)
-- Two arbitrary AP charged smears. `margin` at same x. actual Eu expectation,
-- not decoupled through Wick prices nor a replacement process. No Ward/KISS required.
abbrev covarianceM (c:ℝ):ℂ:= inner ℂ (V⇐ c F) (V⇒ c U) - ESingle P x B*ESingle P x D
abbrev cavity (F U:P.Test)(x:P.Spectrum0 3)(s:ℕ):= P.selectedPanel F U s x
structure preserveEU (c δ:ℝ) : Prop where
 normF : F.Normalized
 normU : U.Normalized
 billing : whole P B D F U
 past : ∀ p∈tsupport F.val,p j + clockP P B j < c
 soon : ∀ q∈tsupport U.val,c<q j-clockP P D j
 more : δ < ‖covarianceM P x j B D F U c‖

include J
variable (c ε:ℝ)
local notation "Fst" s:max=> P.prepared s B F
local notation "Snd" s:max=> P.prepared s D U
lemma EU_read (E:preserveEU P x j B D F U c ε):
    Tendsto (fun s=> P.singleState 3 s x (Fst s)) atTop (𝓝 (ESingle P x B)) ∧
    Tendsto (fun s=> P.singleState 3 s x (Snd s)) atTop (𝓝 (ESingle P x D)) ∧
    Tendsto (fun s=> cavity P (Fst s) (Snd s) x s) atTop (𝓝 (covarianceM P x j B D F U c)) ∧
    ∀ᶠ s in atTop, ε< ‖cavity P (Fst s) (Snd s) x s‖ := by
 have e:= solo_beam P x J B F; have g:= solo_beam P x J D U; rw [E.normF.2, one_smul] at e; rw [E.normU.2,one_smul] at g
 have u:Tendsto (fun s=> cavity P (Fst s) (Snd s) x s) atTop (𝓝 (covarianceM P x j B D F U c)):= (duo_beam P x J j B D F U c E.past E.soon E.billing).sub (e.mul g); exact ⟨e,g,u,u.norm.eventually (lt_mem_nhds E.more)⟩
abbrev obtainHere (D:P.Apron)(U:SampleDose):= P.prepared s D U ∈ enclave K ∧ P.asked_at s (P.prepared s D U) (P.spacePrice D U)
omit J in
lemma EU_local (a:s≥ B.s)(b:s≥ D.s) (E:preserveEU P x j B D F U c ε):
    Far (P.spacePrice B F) (P.spacePrice D U) ∧ Disjoint (P.spacePrice B F) (P.spacePrice D U) ∧ IsCompact (P.spacePrice B F) ∧ IsCompact (P.spacePrice D U) ∧ obtainHere P s B F ∧ obtainHere P s D U:=by
 let h:= far_in P B D F U E.billing; exact ⟨h, far_disjoint h,price_compact P B F,price_compact P D U,⟨P.prepared_color s _ _, P.prepared_at s B F a⟩,⟨P.prepared_color s _ _, P.prepared_at s D U b⟩⟩
lemma sale (e:Plaza P B D p q)(h: ε< ‖P.bodyPair x B D p q - P.bodyOne x B p * P.bodyOne x D q‖) : ∃ F U c,preserveEU P x j B D F U c ε :=by
 obtain ⟨c,v,w⟩:=exists_between (show p j+ clockP P B j < q j-clockP P D j from (by linarith only [e.order_ j]))
 obtain ⟨L₁,q₁,L₂,q₂,u⟩:= mem_nhds_prod_iff.mp (show {z:Vantage×Vantage| Plaza P B D z.1 z.2} ∈ 𝓝 (p,q) from stable P B D p q e)
 let F(i):= DoseTravel.slider p (DoseTravel.chosen p i); let Q(i):= DoseTravel.slider q (DoseTravel.chosen q i); have he:Tendsto (fun i=> covarianceM P x j B D (F i) (Q i) c) atTop (𝓝 (P.bodyPair x B D p q-ESingle P x B*ESingle P x D)):=by rw [two_born P x J j B D c p q v w]; exact ((DoseTravel.sprinkle p Z _ (continuing P x j B c).1).inner (DoseTravel.sprinkle q Z _ (continuing P x j D c).2)).sub_const _
 rw [show P.bodyOne x B p = ESingle P x B from (P.bodyOne_price x J B p).trans (P.bodyOne_price x J B 0).symm, show P.bodyOne x D q = ESingle P x D from (P.bodyOne_price x J D q).trans (P.bodyOne_price x J D 0).symm] at h
 have a₁: ∀ᶠ i:ℕ in atTop, tsupport (F i).val⊆ L₁∩{t:Vantage| t j+clockP P B j<c}:= concentrates p _ (inter_mem q₁ (((continuous_apply j).add continuous_const).continuousAt.tendsto (gt_mem_nhds v)))
 have a₂: ∀ᶠ i:ℕ in atTop, tsupport (Q i).val⊆ L₂∩{t:Vantage| c<t j-clockP P D j}:= concentrates q _ (inter_mem q₂ (((continuous_apply j).sub continuous_const).continuousAt.tendsto (lt_mem_nhds w)))
 obtain ⟨i,z,b,g⟩:= ((he.norm.eventually (lt_mem_nhds h)).and (a₁.and a₂)).exists
 exact ⟨F i,Q i,c,prescribed ..,prescribed ..,fun i x j y=> u (show (i,j)∈ L₁ ×ˢ L₂ from ⟨(b x).1,(g y).1⟩),fun _ x=>(b x).2,fun _ x=>(g x).2,z⟩
#print axioms sale
#print axioms EU_read
end smear_placement
end Basilica
end Rose
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
