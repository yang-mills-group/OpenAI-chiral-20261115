import WakeRoad.Twilight
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark SatinVerification Vacancy Tapestry
open CF.Pannier.Chancel
open Preparation.Yoke EmberWind Jewel
open Lamour.Bridge.Celeste Morn
open Ballad
open SpinReceipt Shuttle
open Papal (Weaver household)
open WakeInvestment
open Gleam Gleam.Wake YM.WakeRoad CF.Hiro Hearth
open Precision Regis.Head.Brecht Regis.Circuit Exterior
namespace GramSignal
open Dial Pressure
open Stationary (Gaia)
set_option quotPrecheck false
open Onyx
variable {E:ℝ}{Mc n:ℕ}{P:Spine}{K:P.Register} {r f:ℕ→ℕ}
local notation "Y"=>P.run
local notation "Λ"=>P.par
local notation "iA" n:max=> P.period (P.projection.rows (f n))
local notation "kA" n:max=> P.cutoff (P.projection.columns (f n))
local notation "ν" s:max n:max=> side Y (iA n) s
local notation "Gξ" s:max n:max=> (Λ).V.L.H ((Y).uv (kA n)-s)
local notation "rξ" s:max n:max=> flatSea Y s (iA n) (kA n)
variable (Q: Spine.PreparedInvestment P K E Mc)

variable {β:ℕ→ℝ} (HM: Pooling P.run (P.period ∘ P.projection.rows) (P.cutoff ∘ P.projection.columns) f β)
variable (G:ℕ→ Fin n → Staff)(L:Fin n→Twah.DirSpin)(D:Fin n→ PlaqAxes)(O:Fin n→ Gaia)
structure casting (d w:ℕ)(I:ℝ):Prop where
    paid:∀ s i,(G s i).Pays d w
    shelter: ∀ᶠ s:ℕ in atTop,∀ᶠ k:ℕ in atTop, ∃ (j:ℕ)(o:Seat (ν s k)),(j:ℝ) ≤ sPow P.par s I ∧ ∀ i,(G s i).tenancy (ν s k) d Staff.clearance j o

lemma toll_me (I:ℝ)(n:ℕ)(h:∀ᶠ s:ℕ in atTop, (r s:ℝ)≤ sPow P.par s I):
    Tendsto (fun s:ℕ=> ‖staffWeight (r s)^n‖*chip (hat P.par.R.L P.par.x s) (-3)) atTop (𝓝 0):=by
 -- reuse when n=2? generic
 have he:Tendsto (fun x:ℝ=> 4^n*(BProof.coin x 0 I 0)^(5*n)*chip x (-3)) atTop (𝓝 0) := by
    simp_rw [mul_assoc, chip, BProof.coin_pow,BProof.coin_mul]
    have hz:=BProof.coin_purchases (a:=0*↑(5*n:ℕ) + -3/400000) (b:=I*↑(5*n:ℕ)+0) (c:=0*↑(5*n:ℕ)+0) (Or.inl (by norm_num))
    simpa using hz.const_mul (4^n)
 have hf (t:ℕ): ‖staffWeight t^n‖ = 4^n*((t:ℝ)^5)^n:=by
    rw [norm_pow,staffWeight,norm_mul,norm_pow,norm_pow,Complex.norm_real,Real.norm_of_nonneg (by positivity),Complex.norm_natCast,←mul_pow]; congr 1; ring
 simp_rw [hf]
 apply squeeze_zero' (Eventually.of_forall (fun s=>by have := chip_pos (hat P.par.R.L P.par.x s) (-3); positivity)) (h.mono (fun s h=>?_)) (lift_to he)
 let ψ:= hat P.par.R.L P.par.x s; change _*(chip ψ (-3)) ≤ (4^n*(sPow P.par s I)^(5*n))*chip ψ (-3)
 have hp:0≤ chip ψ (-3):= (chip_pos ..).le; rw [←pow_mul]; gcongr
where lift_to {u:ℝ→ℝ}(s:Tendsto u atTop (𝓝 (0:ℝ))): Tendsto (u ∘ fun s:ℕ=>hat P.par.R.L P.par.x s) atTop (𝓝 0):= s.comp (turnover P.par)

abbrev crewFilm (P:Spine)(β:ℕ→ℝ)(d:ℕ)(s:ℕ): Weaver:= YM.WakeRoad.serve fun i=> choiceWeave P β (G s i) d s
private lemma serve_crew {α:Type*}{X:α→Type*}{n:ℕ}[∀ i,Monoid (X i)](G:Fin n→(i:α)→ X i)(t:α):YM.WakeRoad.serve G t=YM.WakeRoad.serve (fun i=>G i t):=by
 induction n with| zero=>rfl|succ n ih=> rw [YM.WakeRoad.steam,YM.WakeRoad.steam,Pi.mul_apply,ih]; rfl
private lemma at_crew (d m:ℕ) (Q:Side):setUp (G m) Q (κFix β m) d (temp (hat P.par.R.L P.par.x m))= crewFilm G P β d m Q:= by unfold crewFilm; rw [serve_crew]; rfl

variable {I:ℝ}{d w:ℕ}
lemma tag_crew (H:∀ i t,(G t i).Pays d w)(s:ℕ): TestFamily P.calibration true (household P.calibration (crewFilm G P β d s)):=by
 -- generic on family
 let T:=(P.calibration); suffices h:TestFamily T true (YM.WakeRoad.serve (fun i=> household T (choiceWeave P β (G s i) d s))) by
    let x(i:Fin n):=choiceWeave P β (G s i) d s; have ht: household T (YM.WakeRoad.serve x)= YM.WakeRoad.serve (fun i=>household T (x i)):=by funext m; rw [serve_crew (X:=fun m=>Mark (T.c m)) (fun i=>household T (x i)) m]; exact serve_crew _ _
    change TestFamily T true (household T (YM.WakeRoad.serve x)); rwa [ht]
 exact generic _ (fun i=>paidStaff P β s d w (G s i) (H i s))
where
 generic {A:Calibration}{n:ℕ}(x:Fin n → Family A)(h:∀ i,TestFamily A true (x i)): TestFamily A true (YM.WakeRoad.serve x):=by
    induction n with|zero=> simp only [YM.WakeRoad.serve,List.ofFn_zero,List.prod_nil]; exact TestFamily.oneT|succ n ih=>rw [YM.WakeRoad.steam]; exact (h 0).mul (ih (x∘Fin.succ) (fun i=> h i.succ))

include Q HM
lemma castPrice (p:0<I)(h:∀ᶠ s:ℕ in atTop,(r s:ℝ)≤ sPow P.par s I)(q:casting (P:=P) (f:=f) G d w I):
    let M:= fun sn:ℕ×ℕ=>Journey.compass Y (iA sn.2) (kA sn.2) sn.1 ((crewFilm G P β d sn.1) (ν sn.1 sn.2))
    Tendsto (fun sn:ℕ×ℕ=> staffWeight (r sn.1)^n * (M sn - tideSeat (P:=P) (f:=f) (β:=β) G sn)) stairs (𝓝 0):=by
 intro M
 obtain ⟨v,T⟩:= Q.investment
 rw [tendsto_zero_iff_norm_tendsto_zero]; simp_rw [norm_mul]
 apply squeeze_zero' (Eventually.of_forall fun s=> mul_nonneg (norm_nonneg _) (norm_nonneg _)) _ (liftStair (toll_me I n h))
 apply eventually_curry_iff.mpr; filter_upwards [title (n:=n) Y P.law P.history T Q.dispatch Q.rocky.merit p,q.shelter,grow_e I (w:ℝ) p P.par] with s v₀ q' k
 filter_upwards [HM.up.tendsto_atTop.eventually v₀,q'] with m z e
 obtain ⟨B,o,t,q₀⟩:=e; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); have he:= z.1.cost (G s) (q.paid s) (paidFix Y HM P.large s) B o q₀ t k
 unfold setUp at he; change ‖Journey.compass Y (iA m) (kA m) s ((crewFilm G P β d s) _)-_‖≤ _; rw [←at_crew]; exact he

lemma crew_limit (p:0<I)(h:∀ᶠ s:ℕ in atTop,(r s:ℝ)≤ sPow P.par s I)(q:casting (P:=P) (f:=f) G d w I){x:ℂ}(H: Tendsto (fun sn:ℕ×ℕ => staffWeight (r sn.1)^n*tideSeat (P:=P) (f:=f) (β:=β) G sn) stairs (𝓝 x)):
    Tendsto (fun s:ℕ=> staffWeight (r s)^n *P.E s (household P.calibration (crewFilm G P β d s))) atTop (𝓝 x):= by
 let M:= fun sn:ℕ×ℕ=>Journey.compass Y (iA sn.2) (kA sn.2) sn.1 ((crewFilm G P β d sn.1) (ν sn.1 sn.2))
 have ht:= (castPrice Q HM G p h q).add H; rw [zero_add] at ht
 exact passStair (g:=fun sn:ℕ×ℕ=> staffWeight (r sn.1)^n*M sn) (ht.congr fun s=>by ring) (fun s=>e_pass _ _ (tag_crew _ (fun i s=>q.paid s i) s) HM.up _)
omit Q HM
variable (a:ℕ→Fin n→ Cover){X:Fin n→Gaia}
local notation "rβ"=> zoomR P.par I
abbrev troops (s:ℕ)(i:Fin n): Staff:=localStaff (a s i) (L i) (D i)
lemma local_casting (u:StrictMono f)(p:0<I)(h:∀ i,Appoint P.par I (fun s=> a s i) (X i)): casting (P:=P) (f:=f) (troops L D a) 4 0 (I+2):=by
 let z s i:=nodeC (a s i); let R:= 4+Staff.clearance+8
 refine ⟨fun _ _=>ready_local ..,?_⟩
 let x:Cover:=0
 -- separation to zero via same node basis gaugeRise
 let g(i:Fin n)(j:Axis)(s:ℕ):= ((z s i j:ℤ):ℝ) /(sPow P.par s I)
 have hg (i j): Tendsto (g i j) atTop (𝓝 (X i j)):= (show Continuous fun i:Gaia=>(i j:ℝ) by fun_prop).continuousAt.tendsto.comp (h i)
 let T:ℝ:= ∑ i:Fin n, ‖X i‖; let A:= T+1; have ht:0≤T:=sum_nonneg (fun _ _=>norm_nonneg _)
 let m(i:Fin n)(s):= Signal.Interval.separationCost (z s i) x
 have ha(i:Fin n)(j): |X i j| < A:= ((PiLp.norm_apply_le (X i) j).trans (single_le_sum (f:=fun i=> ‖X i‖) (fun _ _=> norm_nonneg _) (mem_univ i))).trans_lt (lt_add_one T)
 have hb(i:Fin n)(j): ∀ᶠ s:ℕ in atTop,((z s i j).natAbs:ℝ) ≤ A*sPow P.par s I:=by filter_upwards [(hg i j).abs.eventually (gt_mem_nhds (ha i j))] with s v; rw [Nat.cast_natAbs,Int.cast_abs]; unfold g at v; rw [abs_div,abs_of_pos (show 0<sPow P.par s I from BProof.coin_pos ..)] at v; exact (le_div_swap v.le (BProof.coin_pos ..))
 let d(s):= univ.sup fun i:Fin n=>m i s
 have hc:∀ᶠ s:ℕ in atTop,(d s:ℝ) ≤ A*sPow P.par s I:=by
    filter_upwards [Filter.eventually_all.mpr (fun i:Fin n=> Filter.eventually_all.mpr (hb i))] with s e
    cases isEmpty_or_nonempty (Fin n) with
    | inl p=> rw [show d s=0 by simp [d],Nat.cast_zero]; apply mul_nonneg (by unfold A; linarith) (BProof.coin_pos ..).le
    | inr p=>
        obtain ⟨i,_,c⟩:= exists_mem_eq_sup _ (univ_nonempty (α:=Fin n)) (fun i=>m i s); unfold d; rw [c]; obtain ⟨j,_,h'⟩:= exists_mem_eq_sup _ (univ_nonempty (α:=Axis)) (fun j=>((z s i-x) j).natAbs); unfold m Signal.Interval.separationCost; rw [h',show (z s i-x)=z s i from sub_zero _]; exact e i j
 filter_upwards [hc,grow_e I 1 p P.par,(turnover P.par).eventually (BProof.coin_budget (a:=0) (d:=0) (b:=I) (c:=0) (f:=0) (e:=I+2) (Or.inr (Or.inl ⟨rfl,by linarith⟩)) (A+ ↑R) 1 zero_lt_one)] with s v g' h'
 let S':=insert x (univ.image (z s))
 filter_upwards [(steps_sides P f u s).eventually (liftMoney S')] with k h0; let l:=wrap (More (ν s k)); refine ⟨R+d s,l x,?_,?_⟩
 · push_cast; change (A+↑R)*sPow P.par s I<1*sPow P.par s (I+2) at h'; nlinarith only [h',v,g', Nat.cast_nonneg (α:=ℝ) R]
 intro i v u
 apply blocks_test.mpr
 change v ∈ Lattice.halo R ({l (z s i)}:Finset _) at u; obtain ⟨y,j,e⟩:=halo_spec.mp u; rw [mem_singleton.mp j] at e; have hk: separation (l x) (l (z s i))≤ d s:=by rw [separation_comm,h0 _ (mem_insert_of_mem (mem_image_of_mem _ (mem_univ _))) _ (mem_insert_self ..)]; exact Finset.le_sup (f:=fun i=> m i s) (mem_univ _)
 exact (separation_triangle (l x) (l (z s i)) v).trans ((add_le_add hk e).trans_eq (Nat.add_comm ..))
where le_div_swap {x H y:ℝ}(h:|x|/y ≤ H)(p:0<y): |x|≤ H*y:=(div_le_iff₀ p).mp h
#print axioms local_casting
lemma ion (p:0<I)(h:∀ i,Appoint P.par I (fun s=> a s i) (X i))(i j:Fin n):
    Tendsto (fun s=>riseX (rβ s) (((troops L D a) s i).u-((troops L D a) s j).u)) atTop (𝓝 (X i-X j))∧
    Tendsto (fun s=>riseX (2*(rβ s:ℝ)) (((troops L D a) s i).face.1-((troops L D a) s j).face.1)) atTop (𝓝 (X i-X j)):=by
 let w(i:Fin n)(s:ℕ):=a s i
 have he(l): Tendsto (fun s=>riseX (rβ s) (w l s)) atTop (𝓝 (X l)):= (appoint_as P.par p (fun s=> a s l) (X l)).mp (h l)
 have hx:Tendsto (fun s=>riseX (rβ s) (w i s-w j s)) atTop (𝓝 (X i-X j)):= ((he i).sub (he j)).congr (fun s=>by ext t; simp [riseX,moor,sub_div])
 exact ⟨hx,Spine.fireGauge (w i) (w j) _ (zoom_grows P.par p) (zoom_pos I) _ hx⟩
include Q HM
abbrev partyValue (P:Spine)(β:ℕ→ℝ)(I:ℝ)(s:ℕ):=staffWeight ((zoomR P.par I) s)^n *P.E s (household P.calibration (crewFilm (troops L D a) P β 4 s))
lemma evening (a:ℕ→Fin 4→ Cover)(L:Fin 4→Twah.DirSpin)(D:Fin 4→ PlaqAxes){X:Fin 4→Gaia}(p:0<I)(h:∀ i,Appoint P.par I (fun s=> a s i) (X i))(e:Injective X): Tendsto (partyValue L D a P β I) atTop (𝓝 (galaTarget X L D)):=by
 let z(s i):=localStaff (a s i) (L i) (D i); have hv:=ion L D a p h
 have he:= GalaRank Q HM (zoom_grows P.par p) (zoom_pos (P:=P) I) z L D X (fun i j=>(hv i j).1) (fun i j=>(hv i j).2) (fun _ _=>rfl) (fun _ _=>rfl) e
 exact crew_limit Q HM z (show (0:ℝ)<I+2 by linarith) ((zoom_pays (P:=P) I p).mono (fun i h=>h.trans (exponent_monotone (by linarith) _ _))) (local_casting L D a HM.up p h) he
lemma afternoon (a:ℕ→Fin 2→ Cover)(L:Fin 2→Twah.DirSpin)(D:Fin 2→ PlaqAxes){X:Fin 2→Gaia}(p:0<I)(h:∀ i,Appoint P.par I (fun s=> a s i) (X i))(e:Injective X): Tendsto (partyValue L D a P β I) atTop (𝓝 (duoTarget X L D)):=by
 let z(s i):=localStaff (a s i) (L i) (D i); have hv:=ion L D a p h
 have he:= DuoRank Q HM (zoom_grows P.par p) (zoom_pos (P:=P) I) z L D X (fun i j=>(hv i j).1) (fun i j=>(hv i j).2) (fun _ _=>rfl) (fun _ _=>rfl) e
 exact crew_limit Q HM z (show (0:ℝ)<I+2 by linarith) ((zoom_pays (P:=P) I p).mono (fun i h=>h.trans (exponent_monotone (by linarith) _ _))) (local_casting L D a HM.up p h) he
#print axioms evening
#print axioms afternoon
end GramSignal
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
