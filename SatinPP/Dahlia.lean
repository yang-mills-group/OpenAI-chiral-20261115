import SatinPP.Curtsy
/-! # Dense thermal jets, choose in any open cross-channel test
        without losing to a disconnected power -/
set_option autoImplicit false
set_option maxHeartbeats 240000
set_option synthInstance.maxSize 28000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.SatinJets
open Function Filter Metric InnerProductSpace Set Complex
open OS.Semigroup
open scoped NNReal Topology BigOperators InnerProductSpace ComplexOrder Classical
variable {H : Hilbert}{j : Axis} (S : OS.Semigroup H j) (Y : ℝ → H)
variable {s : ℝ}

variable (h:Positive S Y)
include h
private lemma far_chords (p:0<s)(v:H)(R:∀ w∈ (jets S Y s).range, inner ℂ v w = 0) :
    EqOn (fun z=> inner ℂ v (lifted S Y z)) (fun _=> inner ℂ v (Y s)) inside:= by
 let c := (s:ℂ)
 let X : H →L[ℂ] ℂ:= innerSL ℂ v
 let y:=X (Y s)
 let T:= X ∘ lifted S Y
 have E (n:ℕ): X (jet S Y (n+1) c) = 0:= R _ ⟨Finsupp.single n 1,by simp [jets,c]⟩
 have g: AnalyticOnNhd ℂ (fun z=>inner ℂ v (lifted S Y z)) inside:= fun z t=> (X.analyticAt _).comp (lifted_analytic S Y h z t)
 obtain ⟨ε,u,hε⟩:= Metric.mem_nhds_iff.mp (open_inside.mem_nhds (show c∈inside from p))
 apply g.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
          (convex_halfSpace_gt reCLM.toLinearMap.isLinear 0|>.isPreconnected) (show c∈inside from p)
 filter_upwards [ball_mem_nhds _ u] with z t
 have e: DifferentiableOn ℂ (lifted S Y) (Metric.ball c ε):= (lifted_analytic S Y h).differentiableOn.mono hε
 have w:= (Complex.hasSum_taylorSeries_on_ball e t).mapL X |>.tsum_eq -- parentheses
 change X (lifted S Y z)= X (Y s); rw [← w, tsum_eq_single (0:ℕ)]
 · simp [c,lifted_heat S Y h p]
 intro n hn; rcases Nat.exists_eq_succ_of_ne_zero hn with ⟨i,h'⟩; subst n; simp only [map_smul]; rw [show X (iteratedDeriv i.succ (lifted S Y) c) =_ from E i]; simp


lemma deep_prism (q:0<s){t u:ℝ}(p:0<t)(d:0<u)(c:ℂ):
 c • (Y t-Y u)∈closure (Set.range fun x=>prism S Y x s):=by
 let Z:Submodule ℂ H:= (jets S Y s).range
 change _ ∈ Z.topologicalClosure
 apply Submodule.smul_mem
 rw [←Submodule.orthogonal_orthogonal_eq_closure]; intro v w
 have e:∀{b:ℝ}(y:0<b), inner ℂ v (Y b)=inner ℂ v (Y s):=by
    intro b y;rw [← lifted_heat S Y h y]
    exact far_chords S Y h q v ((Z.mem_orthogonal' v).mp w) (show (b:ℂ)∈inside from y)
 rw [inner_sub_right,e p,e d,sub_self]
end YM.SatinJets
end
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

local notation "ℒ"=>Lead.Clan

open SatinNucleus
variable {r:ℕ→ℕ}{σ:ℕ→ℝ}{B:ℕ→P.Apron}{f n:ℕ}
variable (W:P.VelvetGlass x V r σ)(R:P.Radiates x B V)
local notation "β" i:max a:max=>P.sprig x V (r i) a (σ i)

/- buy profiles at any positive pad, near plume -/
local notation "Prof"=> P.profilesZ x V
def cotillon(w:ℒ→Prism)(q:ℝ)(a:ℒ):=P.profilesZ x V w a q
variable (J:P.GalaxyShow x f n B V)
local notation "Ψ%" => P.cotillon x V
local notation "ρ" a:max => (purePrice a:ℂ)
include W J
lemma surplice(a:ℒ){ε:ℝ}(h:0<ε):
 ∀ᶠ i in atTop,∀q:ℝ,0<q → ∃ w:Prism,dist (P.plume x V r σ i a)
    (prism (Θ) (P.route_y x V a) w q)<ε:=by
 let v:ℂ:=squire a
 have t:Tendsto (fun T:ℝ=>‖v‖ * (((T+T)^4)⁻¹)) atTop (𝓝 0):= by
    have p:Tendsto (fun t:ℝ=> t+t) atTop atTop:=tendsto_id.atTop_add_atTop tendsto_id
    simpa only [mul_zero] using! (tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (n:=4) (by decide)).comp p)).const_mul ‖v‖
 obtain ⟨T,g,e⟩:=((eventually_gt_atTop (1:ℝ)).and (t.eventually (gt_mem_nhds (half_pos h)))).exists
 filter_upwards [((P.velvet_norm x V W g).const_mul ‖v‖).eventually (gt_mem_nhds e)] with i w q q0
 let Y:=P.route_y x V a
 let z:=D (r i)
 let u:= z*cavalier a; let b:=z*T
 have p:0<u:=mul_pos (P.lengthP_pos _) (zero_lt_one.trans (cavalry _))

 let c:=v*σ i/ (ρ a)
 let Z:=c • (Y u - Y b)
 have d:dist (P.plume x V r σ i a) Z < ε/2:=by
    have e: ρ a ≠0:=Complex.ofReal_ne_zero.mpr (purePrice_p a).ne'
    unfold Z Y route_y
    rw [smul_sub, smul_smul c, smul_smul c,show c*(ρ a)=v*σ i from div_mul_cancel₀ _ e]
    unfold plume;rw [mul_smul v,mul_smul v,dist_eq_norm]
    change ‖v • β i (cavalier a)-(v • β i (cavalier a)-v • β i T)‖ < _
    rw [sub_sub_cancel,norm_smul]
    exact w
 have d₁:=deep_prism _ Y (P.route_pos x f n V J a) q0 p (show 0<b from mul_pos (P.lengthP_pos _) (zero_lt_one.trans g)) c
 obtain ⟨_,⟨w,rfl⟩,m⟩:=Metric.mem_closure_iff.mp d₁ (ε/2) (half_pos h)
 exact ⟨w,(dist_triangle _ Z _).trans_lt (by change dist Z _ < ε/2 at m;linarith only [d,m])⟩


structure Surge(d M h ϵ z:ℝ)(v:G) : Prop where
 cap:‖v‖≤M
 whip: (33/4)*h≤dist v (P.strideHeel x d h v)
 swish(j:Axis)(p:j≠3):dist v (P.spurHeel x j d z v) ≤ slack j*z
 pin(y:Vantage)(p:‖y‖≤ϵ)(t:ℝ)(w:0≤t)(z:t≤ϵ): dist v (P.anklet x d y t v) ≤ h/8

lemma cavalcade :
 ∃ M h ϵ:ℝ,0 < M ∧ 0<h ∧ 0<ϵ ∧ ∀ᶠ z:ℝ in 𝓝[>] 0, ∀ᶠ i in atTop, ∀q:ℝ, 0<q→
 ∃ w:ℒ→Prism,∀ᶠ F:ℒ→G in 𝓝 (P.cotillon x V w q),∀m,fanSet m→P.Surge x (D (r i)) M h ϵ z (ounce m F):=by
 obtain ⟨M,b,h'⟩:=P.plume_cap x V W
 obtain ⟨h,g,p,v⟩:= (Eventually.and (self_mem_nhdsWithin (s:=Set.Ioi (0:ℝ))) tsBought).exists
 have g:0<h:=g
 let F:=P.plume x V r σ
 let U i y t:= P.anklet x (D (r i)) y t
 have jolt:∀ᶠ ϵ in 𝓝[>] (0:ℝ),∀ a:ℒ,∀ᶠ i:ℕ in atTop,∀ y:Vantage,‖y‖≤ϵ→∀t,0≤t→t≤ϵ→dist (F i a) (U i y t (F i a))≤h/100:=
    eventually_all.mpr fun a=>P.poised x V W J.heat a (by positivity)

 obtain ⟨l,L,a⟩:=(Eventually.and (self_mem_nhdsWithin (s:=Set.Ioi (0:ℝ))) jolt).exists
 refine ⟨6*M+6,h,l,by positivity, g,L,?_⟩
 filter_upwards [tsBought,self_mem_nhdsWithin] with z t hz
 have hz:0<z:=hz
 let k:=min 1 (min h z/2000)
 have k0:0<k:=by unfold k; positivity
 obtain ⟨e₁,e₂,e₃⟩: k≤1 ∧ k ≤h/2000 ∧ k≤z/2000:=by
    rw [show k=min 1 (min (h/2000) (z/2000)) from by unfold k;rw [min_div_div_right (by norm_num: (0:ℝ) ≤ 2000)]]
    exact ⟨min_le_left .., (min_le_right ..).trans (min_le_left ..),(min_le_right ..).trans (min_le_right ..)⟩
 filter_upwards [h',P.trumpets x V W J.heat g p, P.crinoline x V W t.2,eventually_all.mpr a,eventually_all.mpr (fun a:ℒ=>P.surplice x V W J a k0)] with i h₁ h₂ h₃ h₄ h₅ q p'
 choose w c using fun a=>h₅ a q p'
 refine ⟨w,?_⟩
 have u:∀ᶠ X:ℒ→G in 𝓝 (P.cotillon x V w q),∀ a,dist (F i a) (X a)<k:=
    eventually_all.mpr fun a=> (((show Continuous (fun X:ℒ→G=>dist (F i a) (X a)) from continuous_const.dist (continuous_apply a)).tendsto (P.cotillon x V w q))).eventually (gt_mem_nhds (c a))
 refine u.mono fun X q' m e=>?_
 let y:=ounce m (F i); let y':=ounce m X
 have d:dist y y' ≤6*k:=by

    rw [dist_eq_norm]
    unfold y y' ounce;rw [←sum_sub_distrib]; simp_rw [←smul_sub]
    exact ounce_bound m (v:=fun a=>F i a-X a) e fun a=>by rw [←dist_eq_norm];exact (q' a).le
 change P.Surge x _ _ _ _ _ y'
 have ds(A:(G).Op)(q:‖A‖≤1):= abs_le.mp ((lipschitz q y y').trans (mul_le_mul_of_nonneg_left d (by norm_num)))
 constructor
 · have dd:‖y-y'‖≤6*k:=by rwa [←dist_eq_norm]
   linarith only [norm_le_insert' y' y,norm_sub_rev y y',dd,e₁,ounce_bound m e h₁]

 · have t:= ds _ ((Θ).shrinks ((D (r i))*h).toNNReal)
   have t':= (ds (P.strideHeel x (D (r i)) h) ((Θ).shrinks _)).2
   linarith only [t',whip g h₂ e,e₂,g]
 · intro j p
   have t':=(ds (P.spurHeel x j (D (r i)) z) (P.cart_pay ..)).1
   linarith only [t',swish hz j (h₃ j p) e,e₃,hz]
 intro v d₀ u w t
 have t':= (ds (U i v u) (P.anklet_pay x ..)).1
 have t₀:dist y (U i v u y)≤6*(h/100):= by
    rw [dist_eq_norm]; unfold y
    rw [←ounces_map]
    unfold ounce;rw [←sum_sub_distrib];simp_rw [←smul_sub]
    exact ounce_bound m e fun a=>by rw [←dist_eq_norm];exact h₄ a _ d₀ _ w t
 linarith only [e₂,t',t₀,g]

