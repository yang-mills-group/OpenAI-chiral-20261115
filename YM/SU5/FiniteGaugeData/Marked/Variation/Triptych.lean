import YM.SU5.FiniteGaugeData.Marked.Variation.Linoleum
import YM.SU5.FiniteGaugeData.LocalLimit.Local.Smoothing

/-! # Split the initial product with its exact noise weights -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 550000
open YM.CF.Girt
set_option synthInstance.maxSize 18000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Satin
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder Classical
open Fock Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange
open Common VolumeCape VolumeCape.Atlas VolumeCape.Mesh VolumeCape.Cane VolumeCape.Read Mail.Radiant
open Push.GridApprox
attribute [local instance] opCStarAlgebra
section
variable {I J X V:Type*}[Fintype I][Fintype J][MeasurableSpace X][NormedAddCommGroup V][NormedSpace ℂ V][NormedSpace ℝ V][IsScalarTower ℝ ℂ V] [CompleteSpace V]
-- recollection by finite subsystem, complementary variables always integrate to one even for small volumes
lemma recover (e:I↪J)(g:(I→X)→V)(q:J→ X→ℂ)(μ:Measure X)[IsFiniteMeasure μ](v:∀ j,∫ x,q j x ∂μ=1):
 (∫ x:J→X,(∏ j,q j (x j)) • g (x ∘ e) ∂Measure.pi (fun _=> μ))=(∫ x:I→X,(∏ j,q (e j) (x j)) • g x ∂Measure.pi fun _=> μ):=by
 classical
 let A:((I→X)×(other e→X))≃ᵐ(J→X) :=(MeasurableEquiv.sumPiEquivProdPi (fun _: I⊕other e=> X)).symm.trans (MeasurableEquiv.piCongrLeft (fun _:J=>X) (keysZ e))
 let L:= (Measure.pi fun _:I=>μ); let W:Measure (other e→ X):= Measure.pi fun _=>μ
 have he:MeasurePreserving A (L.prod W) (Measure.pi fun _=>μ):= (measurePreserving_piCongrLeft (fun _: J=>μ) _).comp (measurePreserving_sumPiEquivProdPi_symm (X:=fun _=> X) (fun _=> μ))
 let Y(k:I→X)(z:other e→X): J→ X:= mapa e X (k,z)
 rw [←he.integral_comp' ( fun x:J→X=> (∏ j,q j (x j)) • g (x ∘ e))]
 change (∫ a, (∏ j,q j (Y a.1 a.2 j)) • g (Y a.1 a.2 ∘ e) ∂L.prod W)=_
 let K(y:I→X):=(∏ i,q (e i) (y i)) • g y; let U(x:other e→X):=∏ i:other e,q i.val (x i)
 have ht (a:(I→X)×(other e→X)):(∏ j,q j (Y a.1 a.2 j)) • g (Y a.1 a.2 ∘ e)= U a.2 • K a.1:=by
    obtain ⟨x,y⟩:=a; change (∏ j,q j (Y x y j)) • g (Y x y ∘ e) = _ • ((∏ i,q (e i) (x i)) • g x); rw [show Y x y ∘ e =x from ?_, smul_smul]
    · exact congrArg (fun (z:ℂ)=> z • g x) ((sums_t e q x y).trans (mul_comm ..)) -- simp smul_smul under K? unfold
    funext i; unfold Y mapa; dsimp only [Function.comp_apply,Equiv.trans_apply]; nth_rw 1 [←key_in]; rw [Equiv.piCongrLeft_apply_apply]; rfl
 simp_rw [ht]
 have p := integral_prod_smul (μ:=W) (ν:=L) U K
 rw [←integral_prod_swap (f:=fun x=> U x.2 • K x.1)] -- type
 have m:(∫ y,U y∂W)=1:=by unfold U W; rw [integral_fintype_prod_eq_prod (fun i: other e=> q i.val)]; simp [v]
 exact p.trans (by rw [m,one_smul])
end
#check integral_prod_swap
#check Envelope.compactC
section
variable (C:Side)(D:ℕ→ℝ)(S:Finset Cover)(n:Side)
variable {μ:Measure (Read.Wor (More n) C)}[IsProbabilityMeasure μ]
variable (l:Loom n)(s:Measurable l) (v:∀x, (depot n).map (fun z=>l (x,z))= (((Borel.Aerial.valsf n).prod μ)).map (Dream.sceneQ C D n x))
variable (h:Side)
variable (f:Fields n→FC (Single h)) (vf:Envelope f) (H:∀x y,Agrees (region S n) x.1 y.1→Agrees (region S n) x.2 y.2→ f x=f y) -- use x inferred?
variable {ν:Side}(A:StepData (More n) ν)(β:ℝ)(F:Config SU.group (More n))
abbrev PoleL := ↥(porch C S) × Axis
abbrev rawF := PoleL C S → SU.E
abbrev rawK := (↥(porch C S)) → SU.E
local notation "π₁"=>(Measure.pi fun _ : PoleL C S=> group.probHaar)
local notation "π₂"=>(Measure.pi fun _:((porch C S):Type)=>group.probHaar)
def mist (C:Side)(S:Finset Cover){n ν:Side}(A:StepData n ν)(β:ℝ)(F:rawF C S)(x:rawF C S):ℂ:=∏ i:PoleL C S, (noiseLink A β (F i) (x i):ℂ)
lemma mist_c {p q:Side}(A:StepData p q):Continuous (fun x:ℝ× rawF C S × Hall C S=> mist C S A x.1 x.2.1 x.2.2.1):=by unfold mist noiseLink StepData.penaltyWeight; fun_prop (disch:=intro _; exact (A.penaltyZ_pos _).ne')

include s v vf H
omit s v
include vf H
private lemma theater(p:Tipping S n C)(m:Read.Wor (More n) C):
 let G:= F ∘ stretch (porch C S) n
 (∫ g:Borel.Aerial.Frame n, (∫ V,(A.noise β F V:ℂ) • f (V,Dream.sceneQ C D n V (g,m))∂prior group (More n))∂Borel.Aerial.valsf n)=(∫ q:Hall C S, mist C S A β G q.1 • f (replant S n (Common.pairs C D S (chooseCourse C S n m) q))∂Common.law C S):=by
 intro G
 let e: PoleL C S ↪ Edge (Seat n):=⟨stretch (porch C S) n,inject_stretch S n C p⟩
 let d: (porch C S:Type) ↪ Seat n:=⟨pole (porch C S) n,fun x y t=> Subtype.ext (p (tips_here _ x.property) (tips_here _ y.property) t)⟩
 let y(x:Hall C S):=f (replant S n (Common.pairs C D S (chooseCourse C S n m) x))
 let z(x:Hall C S):FC (Single h):= mist C S A β G x.1 • y x
 let Ω:=Common.law C S
 haveI : IsProbabilityMeasure Ω:= inferInstanceAs (IsProbabilityMeasure (Common.law C S))
 have hm:Envelope (fun x:Hall C S=>mist C S A β G x.1):=Envelope.compactC ((mist_c C S A).comp (continuous_const.prodMk (continuous_const.prodMk continuous_id)))
 have hy:Envelope y:= Env.along (g:=replant S n ∘ Common.pairs C D S _) vf ((replant_b S n).comp (pairs_m C D S _))
 have hz:Integrable z Ω:=Env.integrableX (Girt.kitE _ _ (fun (a:ℂ)(v:FC (Single h))=> a • v) (by exact continuous_fst.smul continuous_snd) hm hy) _
 let α:Measure (rawF C S):=Measure.pi fun _=>SU.group.probHaar
 let τ:Measure (rawK C S):=Measure.pi fun _=>SU.group.probHaar
 let Y(G:rawK C S):FC (Single h):=∫ x,z (x,G)∂α
 change _ = (∫ x,z x∂α.prod τ)
 rw [integral_prod_symm _ hz]
 suffices hx : (∫ g:Borel.Aerial.Frame n, (∫ V,(A.noise β F V:ℂ) • f (V,Dream.sceneQ C D n V (g,m))∂prior group (More n))∂Borel.Aerial.valsf n)=(∫ g:Borel.Aerial.Frame n, Y (g ∘ d)∂Borel.Aerial.valsf n) by
    rw [hx]; exact (hinge (fun g:Borel.Aerial.Frame n=> g ∘ d) Y (normP group.probHaar d d.injective) hz.integral_prod_right).symm
 apply integral_congr_ae; apply Filter.Eventually.of_forall; intro g
 let B(i:Edge (Seat n))(x:SU.E):ℂ:= noiseLink A β (F i) x
 have hX (V:Pane n) :
     (A.noise β F V:ℂ) • f (V,Dream.sceneQ C D n V (g,m))=(∏ i:Edge (Seat n), B i (V i)) • y (V ∘ e,g ∘ d):=by
    apply congrArg₂ (α:=ℂ) (β:=FC _) (· • ·)
    · unfold StepData.noise; rw [Complex.ofReal_prod]; rfl
    have he := laced S n C D p V g m
    exact (H _ _ he.1 he.2).symm
 simp_rw [hX]
 unfold prior Y; rw [recover e (fun x:rawF C S=> y (x,g ∘ d)) B SU.group.probHaar (fun i=> ((integral_ofReal (𝕜:=ℂ) (f:=noiseLink A β (F i))).trans (by rw [noiseLink_mass]; rfl)))]
 rfl
include s v
lemma triangle (p:Tipping S n C):
 let G:=F ∘ stretch (porch C S) n
 (∫ x,(A.noise β F x.1:ℂ) • f (drawn l x) ∂city n)=(∫ t, (∫ q:Hall C S, mist C S A β G q.1 • f (replant S n (Common.pairs C D S (chooseCourse C S n t) q)) ∂Common.law C S)∂μ):=by
 intro G
 let B(y:Pane n):ℂ:= A.noise β F y
 have hc:Continuous B:=by unfold B StepData.noise StepData.penaltyWeight; fun_prop
 let X(y:Orbit n):FC (Single h):=B y.1 • f (drawn l y)
 have hX:Integrable X (city n):=Env.integrableX (Girt.kitE _ _ (fun (a:ℂ)(v:FC (Single h))=> a • v) (by exact continuous_fst.smul continuous_snd) (Env.along (g:=Prod.fst) (Envelope.compactC hc) measurable_fst) (Env.along (g:=drawn l) vf (drawn_m l s))) _ -- Env.scale real?
 let M:= Read.Wor (More n) C; let U:=Borel.Aerial.Frame n × M
 let Y(y:Pane n)(t:U):Fields n:= (y,Dream.sceneQ C D n y t)
 have hy: Measurable (Function.uncurry Y):= measurable_fst.prodMk (Dream.sceneM C D n)
 let R(y:Pane n × U):FC (Single h) := B y.1 • f (Y y.1 y.2)
 let ρ:= prior group (More n)
 haveI:IsProbabilityMeasure ρ:=inferInstanceAs (IsProbabilityMeasure (prior group (More n)))
 have hR:Integrable R (ρ.prod ((Borel.Aerial.valsf n).prod μ)):= Env.integrableX (Girt.kitE _ _ (fun (a:ℂ)(v:FC (Single h))=> a • v) (by exact continuous_fst.smul continuous_snd) (Env.along (g:=Prod.fst) (Envelope.compactC hc) measurable_fst) (Env.along (g:=uncurry Y) vf hy)) _
 change (∫ x, X x ∂_)=_
 rw [show (∫ x, X x ∂city n) = _ from integral_prod X hX]
 have h0(y:Pane n): (∫ i, X (y,i)∂depot n)=(∫ t, R (y,t)∂((Borel.Aerial.valsf n).prod μ)):=by
    let W(z:Pane n):FC (Single h):= B y • f (y,z)
    have mW:Measurable W:= ((continuous_const (y:=B y)).smul continuous_id).measurable.comp (vf.meas.comp (measurable_const.prodMk measurable_id))
    have yv:Measurable (fun i:Ids n=> l (y,i)):=s.comp (measurable_const.prodMk measurable_id); have py: Measurable (Dream.sceneQ C D n y):= (Dream.sceneM C D n).of_uncurry_left; 
    change (∫ i, W (l (y,i)) ∂_)=(∫ t, W (Dream.sceneQ C D n y t) ∂_)
    rw [← integral_map (f:=W) yv.aemeasurable mW.aestronglyMeasurable,v, integral_map py.aemeasurable mW.aestronglyMeasurable]
 simp_rw [h0]
 rw [show ∫ (x:Pane n), (∫ y,R (x,y)∂((Borel.Aerial.valsf n).prod μ))∂prior group (More n)=(∫ y,(∫ x,R (x,y)∂ρ)∂((Borel.Aerial.valsf n).prod μ)) from integral_integral_swap hR]
 rw [show ∫ y,(∫ x,R (x,y)∂ρ)∂((Borel.Aerial.valsf n).prod μ) = _ from integral_prod_symm _ hR.integral_prod_right]
 exact integral_congr_ae (Eventually.of_forall fun m=> theater C D S n h f vf H A β F p m)
#check Env.scale
#check Integrable.integral_prod_right
#check integral_integral_swap
end
