import YM.CF.BPress.Sugar.Jive
import YM.CF.BPress.Sugar.Moon
/-! Report of House roles. Absolute log cost used for Envelope (not uniform), to convert integral. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Sugar
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Cube Lat SU Spin.Paint Nacre Laic Font Tulip Tenant Dial Scroll Thera Meadow Topology Habitat Habitat.Upled Habitat.Plain Engine Pf Primary Hazel Mount Stamps Skye Port Locale Cube Precision Next.SectorChange RG
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace ContDiff Classical YM.CF.BPress.Vesper YM.CF.BPress.Habitat YM.CF.BPress.Habitat.Plain YM.CF.BPress.Habitat.Driver
attribute [local instance] opCStarAlgebra
variable {m s N:Side}{B:BandWidth}{A:Bands (More N) B}{R:Hangar (More N)}
-- Envelope
section env
open RG
variable {T:Type*}[MeasurableSpace T]{p:T→ℂ}
lemma envX(p':Envelope p): Envelope (fun x=>Complex.exp (p x)):= by
 obtain ⟨b,v⟩:= p'.cost; refine ⟨Complex.continuous_exp.measurable.comp p'.meas, Real.exp b,fun i=>?_⟩; rw [Complex.norm_exp]; exact Real.exp_monotone ((le_abs_self _).trans ((Complex.abs_re_le_norm _).trans (v i)))
end env
namespace Crew
open Grid Driver Letter Letters Hazel Chrono Spin.Hole Actor House LocalH Stage Wealth Weave Pressure Mount.Silhouette Awards Push.SectorMeasure Env Scree Vesper Shot
variable {X:Stage N}{Y:Driver N} {H:Crew A}{e c d u:ℝ}{k:ℕ}
local notation "η"=>mState N A
abbrev lock (x:mState N A): Rod N:= x.2.2.2.2.1
abbrev can (x:mState N A): ActY N:= x.2.2.2.2.2
def grim (R:Hangar (More N))(H:Crew A)(X:Stage N)(ε:ℝ)(x:mState N A): Shot N:= ShotZ A ε (H.harborT x) (Lily.interest A (H.tape x)) (areaC R H X x) (can x) (lock x) -- tune A implicit
variable (F:Rented R H X Y.d e k c)(Q:Stamp A R X Y)
lemma can_m : Measurable (can (A:=A)):=by unfold can; fun_prop
lemma lock_m : Measurable (lock (A:=A)):=by unfold lock; fun_prop
variable (R H X)
lemma grim_m {α:Type}[MeasurableSpace α](v:α→ mState N A)(t:Measurable v): Given (grim R H X u ∘ v):=by
 let k:= areaC R H X; have he:= (areaC_m R H X); refine ⟨H.harbor_m.comp t,fun i=> ?_,fun i=> ?_,fun i=>?_ , H.interestM.comp t⟩; · exact ((Wheel.ζ_C (Vesper.forcePart i)).measurable.comp lock_m).comp t -- name
 · exact (askM k he (fun k x=> yKick k (u:ℂ) (can (A:=A) x) i) (fun S=>by unfold yKick; split; exact measurable_const.mul (((show Continuous (fun i:Circle=> (i:ℂ)) from continuous_subtype_val).measurable.comp (measurable_pi_apply i)).comp can_m); exact measurable_const)).comp t
 by_cases h:i∈ Lily.vacancy A <;> (change MeasurableSet {j:α|i∈Lily.vacancy A}; simp [h])
variable {R H X}
include F Q
lemma grim_p (p:0≤u)(v:H.castP): inBudget (grim R H X u v.val) u:= shotBudget A p _ _ _ _ _ (Stage.player_vase (F.pay v.val v.property).licence Q (F.roof.paid (harborT H v.val))).t' -- tune order
omit F Q
def maskH (R:Hangar (More N))(H:Crew A)(X:Stage N)(x: mState N A)(u:ℝ): ℂ:= Ωmask N (H.flag x) (lock x)*bill_phase (u:ℂ) (can x) (areaC R H X x)
lemma maskH_meas (u:ℝ) : Measurable (fun x=> maskH R H X x u):=by
 unfold maskH; exact (askM (H.flag) (H.flag_m) (fun i x=> Ωmask N i (lock x)) (fun i=> (((Wheel.ζ_C i).measurable).comp (lock_m (A:=A))).inv)).mul (askM (areaC R H X) (areaC_m R H X) (fun i (x:η)=> bill_phase (u:ℂ) (can x) i) (fun i=>((((Wheel.ζ_C i).measurable).comp can_m).inv).mul measurable_const))
lemma maskH_cost (u:ℝ) (p:0≤u)(x: mState N A): ‖maskH R H X x u‖=u⁻¹^(areaC R H X x).card:=by simp only [maskH,bill_phase,Ωmask,norm_mul,norm_pow,norm_inv,Wheel.ζ_price,inv_one,one_mul,Complex.norm_real,Real.norm_of_nonneg p]
lemma maskEnv (p:0≤u) : Envelope (fun x=> maskH R H X x u):=by
 let c:= max 1 (u⁻¹); have hv:1≤c:=le_max_left ..; refine ⟨maskH_meas u,c^(Fintype.card (Site N)),fun x=>?_ ⟩; rw [maskH_cost u p x]; apply le_trans (pow_le_pow_left₀ (show 0≤u⁻¹ from inv_nonneg.mpr p) (le_max_right 1 u⁻¹) _); exact pow_le_pow_right₀ hv (card_le_univ _)
end Crew
namespace Crew
open Grid Driver Letter Letters Hazel Chrono Spin.Hole Actor House LocalH Stage Wealth Weave Pressure Mount.Silhouette Awards Push.SectorMeasure Env Scree Vesper Shot
variable {A: Bands (More (mid m s)) B}{R:Hangar (More (mid m s))} {X:Stage (mid m s)}{Y:Driver (mid m s)}{H:Crew A}{e c d u t q μ v:ℝ}{k:ℕ}
local notation "η"=> More (mid m s)
variable (F:Rented R H X Y.d e k c)(Q:Stamp A R X Y) (ε:ℝ)(P:Edition Y)
-- $C.α $Π.
def stern0 (g: H.castP):= ΔRest A X.W.M P (ΓStage F Q g) (grim R H X ε g.val)
def Report (g:H.castP):= maskH R H X g.val ε * Complex.exp (stern0 F Q ε P g)
variable {F Q ε P} {Z W Z' V:Pledge} {h:Wish Y Z W Z'}{G:Brace.Duet m s}{T:Scree.GramM (mid m s)}
variable (L:Passports Y T G h P V q d ε t v) (a:0≤ε)
include a L
lemma logEnv : Envelope (stern0 F Q ε P):=by
 let H0(i)(x:H.castP):=δRest A X.W.M scaffold (fun j=>P.op j (ΓStage F Q x)) i; let Y0(i)(x:H.castP):=δRest A X.W.M id (fun j=> P.logG j (ΓStage F Q x) (grim R H X ε x.val)) i; refine Law.addC (total (univ:Finset (Tenor η)) (g:=H0) ?_) (total (univ:Finset (Support η)) (g:=Y0) ?_); · intro i; unfold H0 δRest; split; exact ⟨(L.measure i).comp (Γ_m F Q),_,fun x=> L.known i (ΓStage F Q x)⟩; exact Law.fixedP _
 intro i; unfold Y0 δRest; split; exact ⟨L.cloud _ _ _ (grim_m _ _ _ Subtype.val measurable_subtype_coe) (Γ_m F Q), _, fun x=> L.turn _ _ _ (grim_p F Q a x)⟩; exact Law.fixedP _
lemma reportEnv : Envelope (Report F Q ε P):= Law.prodP (Env.along (maskEnv a) measurable_subtype_coe) (envX (logEnv L a))
end Crew
end YM.CF.BPress.Sugar
