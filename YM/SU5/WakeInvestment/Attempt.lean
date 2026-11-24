import YM.SU5.WakeInvestment.OriginalState
import YM.SU5.Six.RawWard
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option maxRecDepth 2500
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Morn
open YM.Stationary (Gaia)
open Spine Ballad SpinReceipt Yoke Shuttle
variable (P:Spine) {A:ℝ}
open SitSpin
open Papal (household)
abbrev showOne (P:Spine) (A:ℝ)(s:ℕ)(z:Ballad.Lead.Clan)(u:Cover) : P.Test := P.tuneK (pill_voice P.par A s z u 0)

-- Earlier appointment is physically a theta3 test; use here IC orientation of that label, so can keep the node positions even when issuing from a future (oriented) layout elsewhere.
lemma showing (A:ℝ)(s:ℕ)(z:Ballad.Lead.Clan)(u:Cover) : let X:= P.showOne A s z u
     X=P.reflectTest 3 (P.showOne A s z (Shuttle.flip u)) ∧
     X.val=(sPow P.par s A:ℂ)^3 • (household P.calibration (qRaw z u)) ∧
     TestFamily P.calibration false X.val ∧ CovCover P.calibration X.val ∧ Six.PureMatter P.calibration X:=by
 intro X; let G:= qRaw z u; let v:= (pill_voice P.par A s z u 0); let W:=pill P.par A s z u 0
 have ht: X.val=household P.calibration W:=rfl
 constructor; swap
 · have hF:= pill_q P.par A s z u; refine ⟨ht.trans (show household P.calibration W= _ from ?_),⟨⟨_,v.1.narrow _⟩,fun _=> Filter.Eventually.of_forall (fun m _=> v.2 _)⟩,fun m=> v.2 _, fun _ _ _=>rfl⟩
   unfold W; rw [hF]; rfl
 apply Subtype.ext; funext m; change W _= reflMark 3 0 (pill P.par A s z (Shuttle.flip u) 0 _); rw [pill_theta]; unfold Shuttle.flip; rw [flee_twice]

-- revenue for first and pair
variable (A)
abbrev panel (z:Ballad.Lead.Clan)(x:ℕ→ Cover) (s:ℕ):= P.showOne A s z (x s)
def selectedPanel (f g:P.Test) (s:ℕ)(x:P.Spectrum0 3) :ℂ:= let Z0:=P.singleState 3 s x; Z0 (f*g)-Z0 f*Z0 g
-- purchase of geometry: keep actual normalized $R_s^3$, location at *stamp* at nodeC(u(s)) (may be 1 offset in coordinates at scale). approximate from any pose-pitch integer and fixed origin coset, both parameters after budget; thus can buy actual pillar expectations with this layout
open Onyx (riseX)
structure PencilLease (x y:Gaia) (u v:ℕ→ Cover) : Prop where
 p0:Appoint P.par A u x
 p1:Appoint P.par A v y
 touch: x=y → ∀ᶠ s:ℕ in atTop,u s=v s
variable {A}

/-- All mesh offsets at this U. m is in **matter grid units**, Step e.g. 8B, permits $t_s=16Bh_s$. -/
def advice (P:Spine) (A:ℝ)(m:ℕ)(D:Cover)(x: Gaia): ℕ→ Cover:=fun s i=>m*⌊x i*(zoomR P.par A s/m:ℝ)⌋+ D i
lemma announces (m:ℕ)(p:0< m)(t:0<A)(D:Cover)(x:Gaia) : Appoint P.par A (advice P A m D x) x ∧
    ∀ s i, (m:ℤ) ∣ (advice P A m D x s i-D i) := by
 constructor; swap; · intro s i; unfold advice; simp
 apply (appoint_as P.par t _ _).mpr; let a(s):ℝ:=zoomR P.par A s; have hr:Tendsto a atTop atTop:= tendsto_natCast_atTop_atTop.comp (zoom_grows P.par t); let y:=advice P A m D x; let F(s):= riseX (a s) (y s); have hu:0 <(m:ℝ):=Nat.cast_pos.mpr p
 have he (i:Axis): Tendsto (fun r=> F r i) atTop (𝓝 (x i)):=by
    let q:=(x i:ℝ); let t(c:ℝ):= fun s=> q+c/a s; have h(c:ℝ): Tendsto (t c) atTop (𝓝 q):=by simp_rw [t,div_eq_mul_inv]; simpa using (tendsto_const_nhds (x:=q)).add ((tendsto_inv_atTop_zero.comp hr).const_mul c)
    let e(c:ℝ):ℝ:= q*c/m; let v:=m; let b:ℝ:=D i
    have hf(s:ℕ): F s i= ((m:ℝ)*(⌊e (a s)⌋:ℤ)+b)/a s:=by unfold F y riseX advice; change (↑((_ : ℤ)+ _):ℝ)/ a s= _; push_cast; unfold b e a q; ring_nf
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (h (b-m)) (h b)
    · filter_upwards [hr.eventually_gt_atTop 0] with s g; rw [hf]; let z:=a s; let l:=e (a s); change q+ (b-m)/ z ≤ ((m:ℝ) * ↑⌊l⌋ + b)/z; rw [add_div' _ q _ g.ne', div_le_div_iff_of_pos_right g] -- maybe add_div' x h
      have ht:l*m=q*z:=div_mul_cancel₀ _ hu.ne'; nlinarith only [ht, mul_le_mul_of_nonneg_left (Int.sub_one_lt_floor l).le hu.le]
    filter_upwards [hr.eventually_gt_atTop 0] with s g; rw [hf]; change _≤ q+_/_; have ht:e (a s)*(m:ℝ)=q*a s:=div_mul_cancel₀ _ hu.ne'; rw [add_div' _ q _ g.ne', div_le_div_iff_of_pos_right g]; nlinarith only [ht,mul_le_mul_of_nonneg_left (Int.floor_le (e (a s))) hu.le]
 exact (PiLp.continuous_toLp 2 _).continuousAt.tendsto.comp (tendsto_pi_nhds.mpr he)

variable (V:P.Register) {E v:ℝ}(Q:Investment P.par E v)(L_:Dispatchers P.par)(K:Meritorious P.par)(p:0<A)
variable (a b:Gaia)(u w:ℕ→ Cover)(Z W:Ballad.Lead.Clan)
local notation "μ" => P.pillars 3
include Q L_ K p
lemma windowPoll (h:Appoint P.par A u a) : WakePoll P (P.panel A Z u) 0:=by
 let f(s):=P.panel A Z u s; let X(s:ℕ)(_:Fin 1):=u s; let y(_:Fin 1):=a; let g(_:Fin 1):=Z; let v:List (Fin 1):=[0]
 let F(s):=P.readPill g v (X s) A s; have ht:F=f:=funext fun s=> Subtype.ext (show (F s).val=(f s).val from ?_); swap
 · exact congrArg (household P.calibration) (mul_one (Yoke.pill P.par A s Z (u s) 0))
 change WakePoll P f 0; rw [←ht, ←one_payment y (0:Fin 1→Twah.DirSpin) Z (0:Fin 1)]; exact ⟨fun χ pχ=> P.realPoseP Q L_ K X v g y p (fun i=>h) (fun i j _=>Filter.Eventually.of_forall (fun _=>rfl)) pχ⟩
abbrev duet (P:Spine)(A:ℝ)(Z W:Ballad.Lead.Clan)(u w:ℕ→ Cover)(s:ℕ):=P.panel A Z u s*P.panel A W w s
lemma doublePoll (h:P.PencilLease A a b u w): WakePoll P (duet P A Z W u w) (componentPrice a b Z W):=by
 let X s: Fin 2→ Cover:=![u s,w s]; let Y:Fin 2→Gaia:=![a,b]; let z: Fin 2→ Ballad.Lead.Clan:=![Z,W]; let F s:=P.readPill z [0,1] (X s) A s
 have he: F= duet P A Z W u w:= by funext s; apply Subtype.ext; change household P.calibration (pill _ _ _ _ _ _ * (pill _ _ _ _ _ _ * 1))= _; rw [mul_one]; rfl
 have hf:= two_payment Y z (0:Fin 2) 1; rw [←he]; change WakePoll P F (componentPrice (Y 0) (Y 1) (z 0) (z 1)); rw [←hf]; refine ⟨fun c zχ=> P.realPoseP Q L_ K X [0,1] z Y p (fun i=>?_) ?_ zχ⟩
 · fin_cases i; exact h.p0; exact h.p1
 intro i j; fin_cases i <;> fin_cases j
 all_goals first| exact fun _=>Filter.Eventually.of_forall (fun _=> rfl)| skip
 · exact h.touch
 exact fun v=>(h.touch v.symm).mono (fun i e=>e.symm)
-- Estimate then apply to covariance and its determinant after election.
variable {f:ℕ→ℕ} (u':StrictMono f)
structure Holding (P:Spine)(A:ℝ)(c:ℕ→ℕ)(x:P.Spectrum0 3)(a b:Gaia)(u w:ℕ→ Cover) :Prop where
 one_f(i:Ballad.Lead.Clan): Tendsto (fun s=>P.singleState 3 (c s) x (P.panel A i u (c s))) atTop (𝓝 0)
 one_s(i:Ballad.Lead.Clan): Tendsto (fun s=>P.singleState 3 (c s) x (P.panel A i w (c s))) atTop (𝓝 0)
 cost(i j:Ballad.Lead.Clan): Tendsto (fun s=>P.singleState 3 (c s) x (duet P A i j u w (c s))) atTop (𝓝 (componentPrice a b i j))
include u'
lemma window_hold (h:P.PencilLease A a b u w)
    {J:Type}[Countable J](R:J→ℕ→P.Test)(T:J→ℂ)(hp:∀ i,WakePoll P (R i) (T i)) :
    ∃ c:ℕ→ℕ,StrictMono c ∧ (∀ᵐ x:P.Spectrum0 3 ∂μ, Holding P A (f∘c) x a b u w ∧ ∀ i,Tendsto (fun r=>P.singleState 3 (f (c r)) x (R i (f (c r)))) atTop (𝓝 (T i))) := by
 let X:=Ballad.Lead.Clan⊕Ballad.Lead.Clan⊕Ballad.Lead.Clan×Ballad.Lead.Clan; let G:X→ℕ→P.Test:= Sum.elim (fun Z=>P.panel A Z u) (Sum.elim (fun Z=>P.panel A Z w) fun ⟨Z,W⟩=> duet P A Z W u w); let F:X→ℂ:= Sum.elim 0 (Sum.elim 0 (fun ⟨Z,W⟩=>componentPrice a b Z W))
 have hZ(i:J⊕X): WakePoll P (Sum.elim R G i) (Sum.elim T F i):=by
   rcases i with i|(i|i|⟨i,j⟩) -- pattern parser; simplify
   exact hp i
   exact P.windowPoll Q L_ K p a u i h.p0
   exact P.windowPoll Q L_ K p b w i h.p1
   exact P.doublePoll Q L_ K p a b u w i j h
 obtain ⟨c,t,q⟩:= P.polls_calendar f _ _ hZ u'; refine ⟨c,t,q.mono fun x q'=>?_⟩; exact ⟨⟨fun i=> q' (.inr (.inl i)),fun i=>q' (.inr (.inr (.inl i))),fun i j=> q' (.inr (.inr (.inr (i,j))))⟩,fun i=>q' (.inl i)⟩ -- else type elaborators

omit Q L_ K p u'
abbrev CClan := Ballad.Lead.Clan
def plotPanel (P:Spine)(x:P.Spectrum0 3)(A:ℝ)(u w:ℕ→ Cover)(s:ℕ) : Matrix CClan CClan ℂ := Matrix.of fun i j=> P.selectedPanel (P.panel A i u s) (P.panel A j w s) s x
abbrev matrixPaid (a b:Gaia): Matrix CClan CClan ℂ:= Matrix.of (componentPrice a b)
lemma dim_at_e (Z:CClan): dimf Z=if Z.2 then 10 else 5:=rfl
lemma six_price_axis(p:a 3 < b 3)(v:a 2 < b 2): 0 < (componentPrice a b Z Z).im:=by
 let X:= b-a; have ht:0 < X 3:= sub_pos.mpr p; have hu:0 < X 2:=sub_pos.mpr v; have hX:X≠0:=by intro w; rw [w] at ht; exact (lt_irrefl 0) ht
 let u:ℝ:=(Real.pi^2*‖X‖^4)⁻¹; have he:0 < u:=by unfold u; positivity
 let U:=X 3; let Y:=X 2; change 0 < Complex.im (if Z=Z then (dimf Z:ℂ)*(((u:ℂ)/2)*((U:ℂ)+(Y:ℂ)*Complex.I))^2 else 0)
 rw [if_pos rfl,show (u:ℂ)/2=(↑(u/2:ℝ):ℂ) from by push_cast; rfl]; have hdim:(0:ℝ)< (dimf Z:ℝ):= by exact_mod_cast (dimf_pos Z)
 simp only [Complex.mul_im,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im, sq,Complex.add_im,Complex.add_re,Complex.I_re,Complex.I_im,Complex.natCast_im,Complex.natCast_re]; simp only [zero_mul,mul_zero,add_zero,zero_add,sub_zero, mul_one]; change 0< (dimf Z:ℝ)*( _+_) ; unfold U Y; positivity
lemma determinant_chiral (p:a 3 < b 3)(v:a 2 < b 2): (matrixPaid a b).det≠0:=by
 let f:=fun i:CClan=>componentPrice a b i i; rw [show matrixPaid a b= Matrix.diagonal f by ext i j; by_cases p:i=j<;> simp [matrixPaid,Matrix.diagonal,p, componentPrice,f],Matrix.det_diagonal]; apply Finset.prod_ne_zero_iff.mpr; intro i _ t; have hx:= six_price_axis a b i p v; change f i=0 at t; change 0 < (f i).im at hx; rw [t] at hx; exact lt_irrefl 0 hx

structure HoldRead (P:Spine)(A:ℝ)(c:ℕ→ℕ)(x:P.Spectrum0 3)(a b:Gaia)(u w:ℕ→ Cover) : Prop extends Holding P A c x a b u w where
 comparison : Tendsto (fun i=> P.plotPanel x A u w (c i)) atTop (𝓝 (matrixPaid a b))
 carries : a 3 < b 3 → a 2 < b 2 → ∀ᶠ i in atTop, (P.plotPanel x A u w (c i)).det≠0 ∧ ∀ j, 0< (P.plotPanel x A u w (c i) j j).im
lemma holdRead {f:ℕ→ℕ}{x:P.Spectrum0 3}(h: Holding P A f x a b u w) : HoldRead P A f x a b u w:=by
 let V n:=P.plotPanel x A u w (f n); have he(i j): Tendsto (fun s:ℕ=> V s i j) atTop (𝓝 (componentPrice a b i j)):=by
    have hp:=(h.cost i j).sub ((h.one_f i).mul (h.one_s j)); rw [zero_mul,sub_zero] at hp; exact hp
 have hf:Tendsto V atTop (𝓝 (matrixPaid a b)):=tendsto_pi_nhds.mpr fun i=> tendsto_pi_nhds.mpr (fun j=> he i j)
 refine { toHolding:=h, comparison:=hf, carries:=?_}; intro p q; have hc: Continuous (Matrix.det : Matrix CClan CClan ℂ→ ℂ):= continuous_id.matrix_det
 have ht:Tendsto (fun n:ℕ=>(V n).det) atTop (𝓝 (matrixPaid a b).det):= hc.continuousAt.tendsto.comp hf; filter_upwards [ht.eventually_ne (determinant_chiral a b p q), Filter.eventually_all.mpr (show ∀ j:CClan, ∀ᶠ i:ℕ in atTop, 0 < ((V i) j j).im from fun j=> (Complex.continuous_im.continuousAt.tendsto.comp (he j j)).eventually (lt_mem_nhds (six_price_axis a b j p q)))] with i a b; exact ⟨a,b⟩
include p
universe f'
-- allow additional price requests. Combine Vak selection purchases with *these estimates at these layouts*; first subsequence then x. This has *not* used Point Label projections; lives in s-Dome with actual unselected Wick comparisons, conull x of THIS `P`, actual sector fields/c readings needed later.
theorem achet {J:Type}[Countable J]{Mc:ℕ}{E:ℝ} (T:PreparedInvestment P V E Mc) (f:ℕ→ℕ)(r:StrictMono f) (h:P.PencilLease A a b u w) (R:J→ℕ→P.Test)(Z:J→ℂ)(H:∀ i, WakePoll P (R i) (Z i)) :
    ∃ c:ℕ→ℕ,StrictMono c∧∀ U:P.Spectrum0 3→Prop,(∀ᵐ x∂P.pillars 3, U x) → ∃ x,U x∧ JointTuple.{f'} P V x ∧ HoldRead P A (f∘c) x a b u w ∧ ∀ i,Tendsto (fun r=>P.singleState 3 (f (c r)) x (R i (f (c r)))) atTop (𝓝 (Z i)):=by
 obtain ⟨i,g⟩:=T.investment; obtain ⟨c,p,h⟩:= P.window_hold g T.dispatch T.rocky.merit p a b u w r h R Z H; refine ⟨c,p,fun U e=>?_⟩; obtain ⟨x,h,w⟩:= T.rocky.select _ (e.and h); exact ⟨x,h.1,w,P.holdRead a b u _ h.2.1,h.2.2⟩
omit p
#print axioms six_price_axis
#print axioms HoldRead
#print axioms achet
#print axioms showing
#print axioms announces
#print axioms window_hold
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.postureAtElection
