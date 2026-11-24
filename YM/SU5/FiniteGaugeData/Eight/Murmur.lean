import YM.SU5.FiniteGaugeData.Eight.Melt
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
open scoped Classical
-- chop at fixed observing params and cover through THE operator. Bound even on OP version. proof uses compactness(paid). 
section
variable (Q: Finset (Face ℤ))
private lemma onwardG {c t:Side}(G:Ratio c t)(U:StepData (More c) (More t))(y b e:ℝ)(ζ:Chi)(R_:Loom c) (j:ℕ)(u:Op SU.Slot)(M:Male)(ho:Odd G.count.val)(F:Mark c) (g:ℕ→Mark c)(r:ℕ)(q:LaurentRadius j G.count r)(w:0<b)(v:2*b<firstRadius SU.group)(t':Measurable R_)(p:U.patch.Branches U.kernel SU.group) (x:Fields t)(F': Envelope F)(h':∀ i:ℕ, Envelope (g i))(J':∀ (n:ℕ)(j:Orbit c), (g n) (drawn R_ j)= amber (germB n) Q (onC c j.1) • F (drawn R_ j)):
 Tendsto (fun i:ℕ=> pushMark G U j u M ho ζ b y R_ (g i) x) atTop (𝓝 (pushMark G U j u M ho ζ b y R_ F x)):= by
 let Z(F:Mark c) (z:Orbit c):=U.density y x.1 z.1 • gathered G j u M ho ζ b F x (drawn R_ z)
 have he {F:Mark c}(tP:Envelope F):Integrable (Z F) (city c):= Env.integrableX (Env.scale (Env.along (slice_env U y p x.1) measurable_fst) (Env.along (g:= fun z:Orbit c=> (x,drawn R_ z)) (env_gathered G j u M ho ζ b q w v F tP) (measurable_const.prodMk (drawn_m _ t')))) _
 have ht(i:ℕ)(t:Orbit c) : Z (g i) t= amber (germB i) Q (onC c t.1) • Z F t:=by unfold Z gathered avgF before; simp_rw [J',map_smul,← Finset.smul_sum]; rw [smul_comm (_:ℝ) (amber ..),smul_comm (_:ℝ) (amber ..)]
 simp_rw [outright G U j u M ho ζ b y R_ q t' p w v _ F' x,show ∀ t:ℕ,pushMark G U j u M ho ζ b y R_ (g t) x= ∫ u:Orbit c,Z (g t) u ∂city c from fun i=> outright G U _ _ _ ho ζ b y R_ q t' p w v (g i) (h' i) x]
 exact tendsto_integral_of_dominated_convergence (fun t:Orbit c=>‖Z F t‖) (fun i=>(he (h' i)).1) (he F').norm (fun i=>Eventually.of_forall fun x=>by rw [ht,norm_smul]; exact mul_le_of_le_one_left (norm_nonneg _) (amber_bounded ..)) ((amber_house Q).mono (fun x he=> tendsto_const_nhds.congr' (he.mono fun i h=>by dsimp only; rw [ht,h,one_smul]))) -- tune defeq binder
abbrev sheer (n:ℕ): Family Kₜ:= shineB (germB n) Q (tent Y h)
lemma sheerC(m:ℕ): Durable Kₜ (sheer Y h Q m):= roseColor _ (show GaugeInvariant (amber (germB m) Q) from fun i x=>by unfold amber; simp_rw [face_gauge,SU.group.chord_conj]) Kₜ
variable (P':carpet Q⊆ S) {x:Family (tent Y h)} (X:InTest (tent Y h) true S false x)
include P'
lemma sheerFund (r:ℕ): InTest (tent Y h) true S false (sheer Y h Q r):= ((InTest.seed (amber_cost ..) : InTest Kₜ false (carpet Q) false _).widen).mono P'
include X
local notation "Dθ" n:max=> (sheer Y h Q n*x)
local notation "σ"=> sold Y h s i
local notation "V"=> (tent Y h).c
local notation "Jθ"=> GridStep Λ l S
lemma onwardH (e:Offered Y S s i k) (p:Fields (side Y i (s+1))) : Tendsto (fun j:ℕ=> ingress Y s i k (sold Y h s i (Dθ j)) p) atTop (𝓝 (ingress Y s i k (sold Y h s i x) p)):=by
 let h' := (apt (Y.ir i) Λ.block Λ.R.L s); let u:= fullness Y i k e.calendar; let z:=crease Y s i k e.calendar e.age; let M:=((Y.voyage i).CapeT s)
 exact onwardG Q h' _ _ Λ.J.d 0 Chi.canonical _ _ _ _ Λ.R.odd_side _ (fun i'=> (σ) (Dθ i')) _ (Journey.legal Λ) z.1 z.2 ((Y.voyage i).ownership s).paid.bill (u.cap_grant.branch s e.age) p (sold_affair Y h S s i X).env (fun j=> (sold_affair Y h S s i ((sheerFund Y h S Q P' j).mul X)).env) (fun n v=>by rw [sold_mult, show sheer Y h Q n=dutiful (tent Y h) (amber (germB n) Q) from rfl,flagValue Y h i s (amber (germB n) Q),Pi.mul_apply]; unfold Mirage.canv; rw [Algebra.smul_mul_assoc,one_mul]; rfl)
-- apply WP1 compact to get OP convergence for this fading sequence.When DCT onward, use one valuation α on all h' selected.Prices. 
local notation "A₀"=> certifyAs S Kₜ x X
-- do without same orientation of f.Divider. Family norm→reading at next sheers.
abbrev gasU (n:ℕ) : Catalog S:= certifyAs S Kₜ (sheer Y h Q n*x) (InTest.mul (sheerFund Y h S Q P' n) X)
#check gasU
lemma GasBound : ∃ C:ℝ,0<C ∧ ‖certifyAs S Kₜ x X‖ ≤ C∧∀ n, ‖gasU Y h S Q P' X n‖≤ C:=by
 let C:= duration S*‖A₀‖; have ht:0≤C:=mul_nonneg (duration_pos _).le (norm_nonneg _); let d:= C+‖A₀‖+1; have hx:= norm_nonneg A₀; obtain ⟨m,u⟩:= (roomy_sides S Kₜ).exists; refine ⟨d,?_,?_,fun n=>?_⟩; · unfold d; linarith
 · unfold d; linarith
 apply offered_bound S Kₜ _ (roomy_hosp _ u); intro w; rw [gasU, Hierarchy.certified]; change ‖((Dθ n)) m w‖ ≤ _; apply (norm_mul_le (sheer Y h Q n m w) _).trans; have hv: ‖x m w‖ ≤ C:= Hierarchy.certified S Kₜ x X ▸ compose_price S Kₜ A₀ _ _; exact (mul_le_of_le_one_left (norm_nonneg _) (show ‖sheer Y h Q n m w‖ ≤ 1 from amber_r ..)).trans (hv.trans (by unfold d; linarith))
omit P' X in
lemma evalTransit (S:Finset Cover)(s i:ℕ)(x:Fields (side Y i s)): Continuous (fun y:Catalog S=> (sold Y h s i (composeQ Kₜ S y)) x):= by
 let P:= (LinearMap.proj (R:=ℂ) (φ:=fun _ : Fields (side Y i s)=> FC (Single (side Y i s))) x).comp ((sold Y h s i).comp (composeQ Kₜ S))
 exact (P.mkContinuous (duration S) (fun _=> sold_q_bound ..)).continuous
-- subseq via frequently h. 
omit P' X in
private lemma compact_tendsto {X:Type*}[TopologicalSpace X][FirstCountableTopology X][T2Space X]{F: Set X}{y:ℕ→ X}{x:X} (v:IsCompact F)(e:∀ n,y n∈F)(p:∀ (m:ℕ→ℕ), StrictMono m→∀ t∈F,Tendsto (y ∘ m) atTop (𝓝 t)→ t=x) : Tendsto y atTop (𝓝 x):=by
 refine tendsto_def.mpr (fun i t=>?_ ) -- def syntax
 by_contra h
 obtain ⟨w,z,t₀⟩:= extraction_of_frequently_atTop (show ∃ᶠ n in atTop,y n∉i from by exact (@not_eventually _ (fun n=> y n∈ i) _).mp h); obtain ⟨z',ht,m,q,L⟩:= v.tendsto_subseq (x:=y ∘ w) (fun i=>e _); obtain rfl:= p (w∘m) (z.comp q) z' ht L; obtain ⟨i,f⟩:= (L.eventually (show ∀ᶠ t in 𝓝 z', t∈i from t)).exists; exact (t₀ (m i) f)
lemma signature (e:Offered Y S s i k): Tendsto (fun n=> snag Y h S s i k (gasU Y h S Q P' X n)) atTop (𝓝 (snag Y h S s i k (certifyAs S Kₜ x X))):=by
 obtain ⟨C,p,z,c⟩:= GasBound Y h S Q P' X; let a:PaidPt Y S s:= ⟨(i,k),e⟩; let f:=gasU Y h S Q P' X; let W₀:= GridStep Λ l S; let U:=transitionQ Y h S s a; let K₂:= closure (Set.range (⇑U ∘ f)); let EV:=fun y=> (sold Y h (s+1) i) (composeQ Kₜ W₀ y); have he(y):EV (U y)=ingress Y s i k (sold Y h s i (composeQ Kₜ S y)):=by unfold EV U; rw [transitionQ_apply]; exact exchanged ..
 rw [snag_pay Y h S s i k e]; refine compact_tendsto (F:=K₂) (collective Y h S s (fun _=>a) f C c) (fun n=> subset_closure ⟨n,rfl⟩) (fun m p t _ v=>?_ ); apply sold_catalog_inj Y h W₀ (s+1) i (roomy_hosp _ e.bill.upper); funext y; change EV t y=EV (U (certifyAs S Kₜ x X)) y; rw [he, Hierarchy.certified]
 refine tendsto_nhds_unique (((evalTransit Y h W₀ _ _ y).continuousAt (x:=t) |>.tendsto).comp v) (((onwardH Y h S s i k Q P' X e y).comp p.tendsto_atTop).congr' (Eventually.of_forall (fun i'=>?_)))
 change ingress Y s i k _ y=EV (U (gasU Y h S Q P' X (m i'))) y; rw [he,gasU, Hierarchy.certified]; -- tune
include K R
lemma motionCut : Tendsto (fun i=> P S s (gasU Y h S Q P' X i)) atTop (𝓝 (P S s (certifyAs S Kₜ x X))):=by
 obtain ⟨κ,hκ⟩:= eligible_exists Y u _ K.pick.grow_k; let A:=gasU Y h S Q P' X
 obtain ⟨C,p,z,t⟩:= GasBound Y h S Q P' X; let P₁:= P S s; let U:= certifyAs S Kₜ x X
 refine Metric.tendsto_nhds.mpr fun ε ht=>?_ ; let ε':= ε/3; have he:0<ε':=by positivity -- probably ε' unfold
 obtain ⟨i,⟨z0,Vz⟩,v₁⟩:= ((hired Y h S s K R (ε'/C) (div_pos he p)).and hκ).exists; obtain ⟨y,W⟩:= Vz (κ i) v₁
 let H:=snag Y h S s (u i) (v (κ i)); have hy(f:Catalog S)(v:‖f‖ ≤ C): dist (H f) (P₁ f) ≤ ε':= by
    rw [dist_eq_norm]; apply ((H-P₁).le_opNorm f).trans; exact (mul_le_mul W v (norm_nonneg _) (by positivity)).trans (div_mul_cancel₀ ε' p.ne').le
 filter_upwards [((signature Y h S s _ _ Q P' X y).eventually (Metric.ball_mem_nhds _ he))] with j W
 have hz:dist (H (A j)) (H U)<ε':=Metric.mem_ball.mp W; have hp:dist (P₁ (A j)) (H (A j)) ≤ ε':=by rw [dist_comm]; exact hy _ (t _)
 change dist (P₁ (A j)) _<_; linarith only [hp,hz,hy U z,dist_triangle (H (A j)) (H U) (P₁ U),dist_triangle (P₁ (A j)) (H (A j)) (P₁ U), show 3*ε'=ε from by unfold ε'; ring]
-- to every Φ. actually uniform.Pay.Statement. Choice use with lottery Phase.CAS.
include A
variable (M: Durable (tent Y h) x)
open Hills
include M
lemma spoken (t:0<ε) : ∀ᶠ n in atTop,∀ (Φ:ℕ→W (tent Y h)→ₗ[ℂ]ℂ),Sphere Y h K R A Φ → ‖Model Y h Φ s (sheer Y h Q n*x) - Model Y h Φ s x‖ ≤ ε:=by -- include M
 obtain ⟨B,t',u⟩:= route_price Y h Jθ (s+1) 3 K R (A 3); let H:=motionCut Y h K R S s Q P' X
 filter_upwards [H.eventually (Metric.ball_mem_nhds _ (show 0<ε/B from div_pos t t'))] with i z Φ hS
 let x':W Kₜ:=⟨x,⟨⟨S,X⟩,by simp⟩,M⟩; let tX:= sheerFund Y h S Q P' i; let y:W Kₜ:= ⟨sheer Y h Q i,⟨⟨S,tX⟩,by simp⟩,sheerC Y h Q i⟩; let xK:= y*x'; let p(v:W Kₜ):=Charm.next Y h s K R v; rw [show sheer _ _ _ _*x = _ from (rfl:xK.val=sheer Y h Q i*x).symm]; change ‖Model Y h Φ s xK.val-Model Y h Φ s x'.val‖ ≤ _; rw [Modell,Modell,← hS.cohere s xK,← hS.cohere s x',←map_sub]
 apply (hS.stamp (s+1) (p xK-p x') 3).trans; rw [map_sub, ←dist_eq_norm]; let q:=locate_join Kₜ _ (show Locator Kₜ y S from tX) (show Locator Kₜ x' S from X)
 have he:= locate_next Y h S s K R x' X; have hz':= locate_next Y h S s K R xK q; apply (u (p xK) (p x') hz' he).trans
 rw [show reading _ _ (p xK) hz'=P S s (gasU Y h S Q P' X i) from ?_, show reading _ _ (p x') he=P S s A₀ from ?_]; exact (mul_le_mul_of_nonneg_left (Metric.mem_ball.mp z).le t'.le).trans_eq (by field_simp) -- lemma?
 · exact compose_inj _ _ ((reading_p Kₜ Jθ (p x') he).trans (next_cert Y h S s K R x' X _ (Hierarchy.certified S Kₜ x X)))
 exact compose_inj _ _ ((reading_p Kₜ Jθ (p xK) hz').trans (next_cert Y h S s K R xK q (gasU Y h S Q P' X i) (Hierarchy.certified ..)))
#print axioms signature
#print axioms spoken
end
end YM.CF.Buffered.Afterglow.Hierarchy.Eight
