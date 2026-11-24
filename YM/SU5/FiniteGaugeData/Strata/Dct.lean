import YM.SU5.FiniteGaugeData.Eight.Murmur
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Eight
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Window.Brique
open Reed (Fine)
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
open Heat Quest Fock.Brique
open Nacre Heat Charm Chrono Journey
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
open SalonG
open Quest.Chaperone
open Steam
variable {Λ: Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1 ≤ Λ.x)
variable {u v:ℕ→ℕ}{I:ℕ→ Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}
variable (K:Universal Y h u v I E){P:Call Λ l}{J:Wicket Λ l}(R:Rolled Y h u v J P)
variable (A:∀ i:Axis, Repertory Y h K R i)
open Hills Tint
variable (S T:Finset Cover)(s i k:ℕ) {g α C D ε θ C₀:ℝ}
local notation "Kₜ"=> tent Y h
local notation "N"=> side Y i s
local notation "Ω"=> (Y.voyage i).CapeT s
local notation "E₁"=> W (tent Y h)→ₗ[ℂ]ℂ
namespace Stratus
section 
-- extending the WP8 DCT-cut technique to *arbitrary* a.e. convergence to zero on true Loom points at representative sales. (Power probe mean will be a particular case.)
-- avoid uniform bounds of Laurent price; already integrable for constant matrices. exploit finite-dimensional basis. Price can be this phase expensive; never using for horizon uniform link-pool.
private lemma vex {S I J:Type*}[MeasurableSpace S][Fintype I][Fintype J][DecidableEq I][DecidableEq J](μ:Measure S)(F:ℕ→S→Op I)(G:S→ Op I→ₗ[ℂ] Op J)(h:∀ i, Integrable (fun y=>G y (F i y)) μ)(H:∀ Z:Op I, Integrable (fun y=>G y Z) μ)(p:∀ i x, ‖F i x‖ ≤ C) (q:∀ᵐ x∂μ,Tendsto (fun i=>F i x) atTop (𝓝 0)): Tendsto (fun i=> ∫ y:S,G y (F i y) ∂μ) atTop (𝓝 0):=by
 let u(i j:I):Op I:=Matrix.single i j 1
 let f(y:S):ℝ:=∑ i:I,∑ j:I, C * ‖G y (u i j)‖
 have he:Integrable f μ:=integrable_finsetSum _ fun i _=>integrable_finsetSum _ fun j _=>(H _).norm.const_mul _
 have hp(x:Op I):∑ i:I,∑ j:I, x i j • u i j=x:= by ext i j; simp [u,Matrix.sum_apply,Matrix.single_apply,ite_and,eq_comm]
 have hx(i:ℕ)(y:S):‖G y (F i y)‖ ≤ f y:=by
    rw [←hp (F i y),map_sum]; refine (norm_sum_le ..).trans (sum_le_sum (fun j _=>?_)); rw [map_sum]; apply (norm_sum_le ..).trans; apply sum_le_sum; intro k _; rw [map_smul,norm_smul]; exact mul_le_mul_of_nonneg_right ((norm_entry (F i y) j k).trans (p i y)) (norm_nonneg _)
 have ht(x:S)(k:Tendsto (fun i=>F i x) atTop (𝓝 0)): Tendsto (fun n=> G x (F n x)) atTop (𝓝 0):=by
    let L:Op I →L[ℂ] Op J:=LinearMap.toContinuousLinearMap (G x); exact (map_zero L ▸ L.continuous.continuousAt.tendsto.comp k)
 simpa only [integral_zero] using tendsto_integral_of_dominated_convergence (f:= fun (_:S)=> (0:Op J)) f (fun i=> (h i).1) he (fun i=> Eventually.of_forall (hx i)) (q.mono ht)

variable {c t:Side}(G:Ratio c t)(U:StepData (More c) (More t))(y b:ℝ)(ζ:Chi)(R_:Loom c) (j:ℕ)(u':Op SU.Slot)(M:Male)(ho:Odd G.count.val)(r:ℕ)(q:LaurentRadius j G.count r)(w:0<b)(v₀:2*b<firstRadius SU.group)(t':Measurable R_)(p:U.patch.Branches U.kernel SU.group) (x:Fields t)
-- `gathered` is uniform bounded finite-purpose B-OP over V. Heather.
local notation "K'"=> FC (Single c)
local notation "Τ"=> FC (Single t)
local notation "ξ" V:max Z:max=> gathered G j u' M ho ζ b (fun _=>Z) x V -- test constant
private def opusZ(V:Orbit c): FC (Single c)→ₗ[ℂ] FC (Single t) where
 toFun M':= U.density y x.1 V.1 • (ξ (drawn R_ V) M')
 map_add' A B:=by unfold gathered avgF before; simp only [map_add,sum_add_distrib,smul_add]
 map_smul' x V':=by unfold gathered avgF before; simp_rw [map_smul,←smul_sum,smul_comm (M:=ℝ) _ x]; rfl
include q w v₀ t' p
lemma floater (f:ℕ→Mark c){D:ℝ}(t₂:∀ i z, ‖f i z‖≤ D)(t₃:∀ᵐ z∂city c,Tendsto (fun i=> f i (drawn R_ z)) atTop (𝓝 0))(h':∀ i, Envelope (f i)): Tendsto (fun i=> pushMark G U j u' M ho ζ b y R_ (f i) x) atTop (𝓝 0):= by
 let W: Fields c ×K'→ Τ:= fun z=> ξ z.1 z.2; let K(z:Orbit c):= drawn R_ z; let L(z:Orbit c):= U.density y x.1 z.1; let P:= U.patch; let Z(i:ℕ)(z:Orbit c):= L z • gathered G j u' M ho ζ b (f i) x (K z)
 have hi(F:Mark c)(v':Envelope F): Integrable (fun z:Orbit c=> L z • gathered G j u' M ho ζ b F x (K z)) (city c):=Env.integrableX (Env.scale (Env.along (slice_env U y p x.1) measurable_fst) (Env.along (g:= fun z:Orbit c=> (x,drawn R_ z)) (env_gathered G j u' M ho ζ b q w v₀ F v') (measurable_const.prodMk (drawn_m _ t')))) _
 simp_rw [show ∀ i,pushMark G U j u' M ho ζ b y R_ (f i) x= (∫ z:Orbit c,Z i z ∂city c) from fun i=> outright G U _ _ _ ho ζ b y R_ q t' p w v₀ (f i) (h' i) x]; let X:= opusZ G U y b ζ R_ j u' M ho x; -- eta avoid
 have hz(F:Mark c)(v:Envelope F): Integrable (fun y=> X y (F (K y))) (city c):= hi F v; -- W shortcuts
 exact vex (city c) (fun i y=> f i (K y)) X (fun i=> hz (f i) (h' i)) (fun V=> hz (fun _=>V) ⟨measurable_const,‖(V:K')‖,fun _=>le_rfl⟩) (fun i y=> t₂ _ _) t₃
end
-- Catalogue-level DCT estimate. Hypothesis AE in detected offer at that phase size. use actual Gram upper continuation; independent of holding calibration data constant between moments.
section
variable (f:ℕ→ Catalog S)(C:ℝ)(hc:0<C)(hc':∀ i, ‖f i‖≤ C)
local notation "FF"=> fun n=> composeQ Kₜ S (f n)
local notation "Mf" i:max n:max=> sold Y h s i (composeQ Kₜ S (f n))
abbrev SupplyP := ∀ i:ℕ,Hosp S (side Y i s)→ ∀ᵐ z∂city (side Y i s), Tendsto (fun j=> (Mf i j) (drawn ((Y.voyage i).CapeT s) z)) atTop (𝓝 0)
variable (t₀:SupplyP Y h S s f)
include hc hc' t₀
lemma mooring (e:Offered Y S s i k)(p:Fields (side Y i (s+1))): Tendsto (fun n=> ingress Y s i k (Mf i n) p) atTop (𝓝 0):=by
 let h':= apt (Y.ir i) Λ.block Λ.R.L s; let t:= t₀ i (solvent_lower Y S s e.bill); let z:=crease Y s i k e.calendar e.age; have he(n:ℕ)(x:Fields (side Y i s)): ‖(Mf i n) x‖ ≤ duration S * C:= (sold_q_bound ..).trans (mul_le_mul_of_nonneg_left (hc' _) (duration_pos _).le); let q:= fullness Y i k e.calendar
 exact floater h' _ _ Λ.J.d Chi.canonical _ _ _ _ Λ.R.odd_side _ (Journey.legal Λ) z.1 z.2 ((Y.voyage i).ownership s).paid.bill (q.cap_grant.branch s e.age) p _ he t (fun n=>(sold_affair Y h S s i (compose_t S Kₜ _)).env)
local notation "WK"=> GridStep Λ l S
omit hc hc' t₀ in
private lemma compacto {X:Type*}[TopologicalSpace X][FirstCountableTopology X][T2Space X]{F: Set X}{y:ℕ→ X}{x:X} (v:IsCompact F)(e:∀ n,y n∈F)(p:∀ (m:ℕ→ℕ), StrictMono m→∀ t∈F,Tendsto (y ∘ m) atTop (𝓝 t)→ t=x) : Tendsto y atTop (𝓝 x):=by
 refine tendsto_def.mpr (fun i t=>?_); by_contra h
 obtain ⟨w,z,t₀⟩:= extraction_of_frequently_atTop (show ∃ᶠ n in atTop,y n∉i from (@not_eventually _ (fun n=> y n∈ i) _).mp h); obtain ⟨z',ht,m,q,L⟩:= v.tendsto_subseq (x:=y ∘ w) (fun i=>e _); obtain rfl:= p (w∘m) (z.comp q) z' ht L; obtain ⟨i,F0⟩:= (L.eventually (show ∀ᶠ t in 𝓝 z', t∈i from t)).exists; exact (t₀ (m i) F0)
lemma concerto (e:Offered Y S s i k): Tendsto (fun n=> snag Y h S s i k (f n)) atTop (𝓝 0):=by
 let a:PaidPt Y S s:= ⟨(i,k),e⟩; let U:=transitionQ Y h S s a; let K₂:= closure (Set.range (⇑U ∘ f)); let EV:=fun y=> (sold Y h (s+1) i) (composeQ Kₜ WK y); have he(y):EV (U y)=ingress Y s i k (sold Y h s i (composeQ Kₜ S y)):=by unfold EV U; rw [transitionQ_apply]; exact exchanged ..
 rw [snag_pay Y h S s i k e]; refine compacto (F:=K₂) (collective Y h S s (fun _=>a) f C hc') (fun n=> subset_closure ⟨n,rfl⟩) (fun m p t _ v=>?_ ); apply sold_catalog_inj Y h WK (s+1) i (roomy_hosp _ e.bill.upper); funext y; change EV t y=EV 0 y; rw [show EV 0=0 from (by unfold EV; rw [map_zero,map_zero])]; change _ = (0:FC _)
 refine tendsto_nhds_unique (((evalTransit Y h WK _ _ y).continuousAt (x:=t) |>.tendsto).comp v) (((mooring Y h S s i k f C hc hc' t₀ e y).comp p.tendsto_atTop).congr' (Eventually.of_forall (fun i'=>?_)))
 change ingress Y s i k _ y=EV (U (f (m i'))) y; rw [he]; -- fine
include K R
lemma PhysK : Tendsto (fun n=> P S s (f n)) atTop (𝓝 0):=by
 obtain ⟨κ,hκ⟩:= eligible_exists Y u _ K.pick.grow_k
 refine Metric.tendsto_nhds.mpr fun ε ht=>?_ ; obtain ⟨i,⟨z0,Vz⟩,v₁⟩:= ((hired Y h S s K R ((ε/2)/C) (by positivity)).and hκ).exists; obtain ⟨y,W⟩:= Vz (κ i) v₁; let H:=snag Y h S s (u i) (v (κ i))
 have hy(n:ℕ): dist (H (f n)) (P S s (f n)) ≤ ε/2:= by rw [dist_eq_norm]; apply ((H-P S s).le_opNorm (f n)).trans; exact (mul_le_mul W (hc' _) (norm_nonneg _) (by positivity)).trans (div_mul_cancel₀ (ε/2) hc.ne').le
 filter_upwards [((concerto Y h S s _ _ f C hc hc' t₀ y).eventually (Metric.ball_mem_nhds _ (half_pos ht)))] with j U; have hz:dist (H (f j)) 0<ε/2:=Metric.mem_ball.mp U; rw [dist_comm]; let z:= dist_triangle 0 (H (f j)) (P S s (f j)); rw [dist_comm 0] at z; -- order rw [dist_comm 0] rewrites LHS first -> fail
 exact (dist_triangle _ (H (f j)) _).trans_lt ((add_lt_add_of_lt_of_le (show dist 0 (H (f j))<ε/2 from (dist_comm ..).trans_lt hz) (hy j)).trans_eq (by ring))
#print axioms PhysK
end


-- ∴ uniform receipt in actual morphology.
variable (X:ℕ→W (tent Y h))(xLoc:∀ i,Locator (tent Y h) (X i) S)(C:ℝ)(hc:0<C)
include R K A
lemma flex (t:SupplyP Y h S s (fun i=>reading (tent Y h) S (X i) (xLoc i)))(C':∀ i, ‖reading (tent Y h) S (X i) (xLoc i)‖≤ C)(hC:0<C) (p:0<ε): ∀ᶠ n in atTop,∀ (Φ:ℕ→ W (tent Y h)→ₗ[ℂ]ℂ),Sphere Y h K R A Φ → ‖Φ s (X n)‖ ≤ ε :=by
 let W:= GridStep Λ l S; obtain ⟨B,hB,H⟩:= route_price Y h W (s+1) 3 K R (A 3)
 have t₀:= PhysK Y h K R S s (fun i=>reading (tent Y h) S (X i) (xLoc i)) C hC C' t -- parse
 filter_upwards [t₀.eventually (Metric.ball_mem_nhds _ (div_pos p hB))] with i V Φ H'; rw [← H'.cohere]; apply (H'.stamp (s+1) _ 3).trans; let X':= Charm.next Y h s K R (X i); have hp:= H X' 0 (locate_next Y h S s K R (X i) (xLoc i)) (locate_zero (tent Y h) W); rw [map_zero,dist_zero_right,show reading (tent Y h) W 0 _=0 from compose_inj _ (tent Y h) ((reading_p ..).trans (map_zero _).symm), show reading (tent Y h) W X' _=P S s (reading (tent Y h) S (X i) (xLoc i)) from ascending_ord Y h S s K R (xLoc i)] at hp -- tune _ occurrence
 exact hp.trans ((mul_le_mul_of_nonneg_left (Metric.mem_ball.mp V).le hB.le).trans_eq (by field_simp))
#print axioms flex
end Stratus
end YM.CF.Buffered.Afterglow.Hierarchy.Eight
