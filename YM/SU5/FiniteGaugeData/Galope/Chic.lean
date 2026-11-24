import YM.SU5.FiniteGaugeData.Galope.Cannoli
import YM.SU5.FiniteGaugeData.Galope.Age
import YM.Extra.WILSON_STARTUP.Clock
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 18000
set_option linter.flexible false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Galope
open Function Finset Filter MeasureTheory Matrix Lattice Wilson RG Next.Rank Spindle Next.SectorChange Wrist Lantern Lantern.Cup RouteM Recruit
open Pressure Precision Laurent Bloch Extra.Iteration Extra.Iteration.Scales Next.Fluctuations Rally Drachma.Tame Drachma.Tokens Poeme Haute
open scoped Topology InnerProductSpace Matrix ContDiff BigOperators Classical Kronecker Matrix.Norms.Frobenius
variable {n:Side}{G:Gauge} {s:Stage}{R:PathData G}{P:Bed}{M k w v:ℕ}{A:Finset (Cell n)}{Z:Finset (Site n)}{o:Site n}{γ C r x Λ α η τ μ a h ε β:ℝ}{J:ChartRatio G}
namespace Cold
abbrev DialF(F:Arms G s):= F.C -- tuning
abbrev Θb(x:ℝ):=2* (Press.balanceX (lic (radiusB x)) (temp x))
abbrev paid(F:Arms G s)(x:ℝ):= priceP F (radiusB x) (Θb x)
lemma lic_tiny : soft 0 (fun x:ℝ=> (lic (radiusB x):ℝ)):=by
 unfold lic coreN; push_cast; apply soft.zero; exact (((soft.radius.pow tendsto_id 3).add ((Tiny.const tendsto_id 2 (by norm_num)).mul soft.radius tendsto_id) tendsto_id).add (Tiny.const tendsto_id 10 (by norm_num)) tendsto_id)
lemma debt(k:ℕ)(L:ℕ): debit k L = k+2*L+10 := by unfold debit roomCard; omega
lemma runθ : soft (1/2) Θb := by unfold Θb Press.balanceX; exact ((soft.θA.at_const (lic_tiny.price 4 (by norm_num))).price 2 (by norm_num)) -- use lic_tiny
lemma run(F:Arms G s):soft 1 (paid F):=by
 have hh : soft (1/2) (fun x=> widen (radiusB x) (Θb x) s.width) := (runθ.at_const (soft.zero Tiny.cover_size)).plus (soft.snows _ _ s.width_pos)
 have he:= (runθ.price F.C F.pos.le).times hh; have hm: 1/2+(1/2:ℝ)=1:=by norm_num
 rw [hm] at he; exact he.plus ((soft.snows _ s.width s.width_pos).price (2*s.paths) (by have :=s.paths_pos; positivity))
lemma great_pos (F:Arms G s)(hL:0 ≤ Λ)(ha:0<α)(u:0<ε): ∀ᶠ x in atTop,∀ β:ℝ,x/2≤β→β ≤2*x →∀ p:BudgetPoint,p.threshold=temp x → ∀ n:Side, greatF F n (radiusB x) (lic (radiusB x)) p β α Λ ≤ ε*ser n:=by
 -- full tax in denom (all face count)
 let U(x:ℝ):= (Fintype.card PlaqAxes:ℝ)*(paid F x^2/α); let k(x:ℝ):= s.paths*((temp x)^3+(temp x)^4); let z(x:ℝ):= Λ* temp x^2; let K(x:ℝ):= 2*x*(U x+k x)+z x
 have hu : soft (1+1) U:=by
    simp only [U,sq,div_eq_mul_inv]; exact (((run F).times (run F)).payC _ (inv_nonneg.mpr ha.le)).price _ (Nat.cast_nonneg _)
 have hv := soft.θA; have hx: (1/2:ℝ)+1/2=1:=by norm_num
 have ho:= hv.times hv; rw [hx] at ho; have hk: soft (3/2) k:=by
    unfold k; simp_rw [pow_succ _ 3,pow_succ _ 2,pow_two]; apply soft.price _ _ s.paths_pos.le; have ht:1+(1/2:ℝ)=3/2:=by norm_num
    have hp:= ho.times hv; rw [ht] at hp; exact hp.plus ((hp.times hv).classP (by norm_num))
 have he: soft (1/2) K:=by
    have ht:= (soft.identity.price 2 (by norm_num)).times ((hu.classP (q:=3/2) (by norm_num)).plus hk); rw [show -1+(3/2:ℝ)=1/2 by norm_num] at ht; unfold K z; simp_rw [sq]; exact ht.plus ((ho.price Λ hL).classP (by norm_num))
 filter_upwards [eventually_gt_atTop (0:ℝ), (he.close (by norm_num)).eventually (ge_mem_nhds u)] with x hx hz β ht hq p hh n
 have hw0:0<β:= (half_pos hx).trans_le ht; have hv:0≤ ser n:=Nat.cast_nonneg _; let V:=ser n
 have ho : 0≤U x+k x:=by have hb:=s.paths_pos; unfold U k; rw [← hh]; have hv:=p.threshold_pos; positivity
 have hE: (Fintype.card (Cell n):ℝ)=V*Fintype.card PlaqAxes:=by rw [Fintype.card_prod,Nat.cast_mul] -- tune
 calc
    _ =V*(β*(U x+k x)+z x):=by
       have hV: (n.val:ℝ)^4=V:=by rw [← Nat.cast_pow,← site_card]
       unfold greatF CF.Graph.taxY heightK U k z paid Θb; rw [hh,hV,hE]; ring
    _ ≤ V*K x:=_root_.mul_le_mul_of_nonneg_left (add_le_add_left (_root_.mul_le_mul_of_nonneg_right hq ho) _) hv -- tune
    _ ≤ ε*ser n:= (_root_.mul_le_mul_of_nonneg_left hz hv).trans_eq (mul_comm V ε)
lemma atFar(s:Stage): ∀ᶠ x:ℝ in atTop, 2≤temp x * Real.exp ((radiusB x:ℝ)/s.clip.relaxation):=by

 filter_upwards [eventually_gt_atTop (0:ℝ), Real.tendsto_log_atTop.eventually (WilsonStartup.Timing.cut s.clip)] with x hx ht -- tune temp
 have he: radiusB x=WilsonStartup.Timing.balls (Real.log x):=rfl
 have hp: (Real.sqrt x)⁻¹= Real.exp (-(Real.log x/2)):=by rw [Real.exp_neg, Real.sqrt_eq_rpow,Real.rpow_def_of_pos hx]; congr 2; ring
 have hz: temp x= WilsonStartup.Timing.temp (Real.log x):=by unfold Pressure.temp WilsonStartup.Timing.temp; rw [hp,Real.exp_add] -- tune
 apply ht.trans; rw [hz]; apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le; apply Real.exp_monotone; apply div_le_div_of_nonneg_right _ s.clip.radius_pos.le; exact_mod_cast (he.symm ▸ (Nat.sub_le (WilsonStartup.Timing.balls (Real.log x)) 2)) -- tune
lemma attainer (F:Arms G s)(hc:LocalRatio J)(hx:1<μ)(h0:0<α)(hw:α<1): ∀ᶠ x:ℝ in atTop, ∀ β:ℝ,x/2≤β→∀ p:BudgetPoint,p.threshold=temp x →∀ n:Side, Intro n (radiusB x) → Attains F J n p β α μ (lic (radiusB x)) (coreN (radiusB x)) (radiusB x) ∧ primeShare (radiusB x) s≤α:=by
 obtain ⟨δ,p,v⟩:= marginM hc hx
 have hy:Tendsto (fun x=> primeShare (radiusB x) s) atTop (𝓝 0):= by
    have hz:= ((((soft.snows 1 _ s.width_pos).price _ s.paths_pos.le).close zero_lt_one).pow 2).const_mul (Fintype.card PlaqAxes:ℝ); simpa only [zero_pow (Nat.succ_ne_zero _), mul_zero,zero_div] using hz.div_const s.clip.direct -- tune
 have hθ := runθ.close (by norm_num)
 filter_upwards [eventually_gt_atTop (0:ℝ), atFar s, hθ.eventually (ge_mem_nhds p),hθ.eventually (ge_mem_nhds F.realR),hθ.eventually (ge_mem_nhds (F.allowance.radius)),hy.eventually (ge_mem_nhds h0)] with x u w wV w' w₂ z β p' q h n c
 have hz:0<β:=lt_of_lt_of_le (half_pos u) p'; refine ⟨⟨hz,h0,hw, (mul_pos (pow_pos (sub_pos.mpr hw) _) hz).trans_le (unite hz hw z),by rw [debt]; exact le_rfl,c.2.1,zero_lt_one.trans hx, ?_, ?_,?_,?_⟩,z⟩ -- tune
 · unfold heightK; rw [h]; exact v _ wV
 · unfold heightK; rw [h]; exact w'
 · rw [h]; change 2*Press.balanceX (lic (radiusB x)) (temp x) ≤ _ at w₂; linarith only [w₂,F.allowance.radius]
 rw [h]; exact w
lemma committed(h:LocalRatio J)(K:ℝ):∃ U:ℝ,0≤U∧∀ᶠ x:ℝ in atTop,∀ β:ℝ,x/2≤ β→β≤2*x→ tempLost J β K≤ U*radiusB x:=by
 let Q:=dozer G; have hQ:0≤Q:=Nat.cast_nonneg _; let z:=Real.log J.scale+Q*Real.log (2*Real.pi)/2; let U:= |z|+Q/2*Real.log (sheetB K); have hu:0≤U:=by unfold U; exact add_nonneg (abs_nonneg _) (by have :=sheet_log K; positivity)
 refine ⟨U+Q,add_nonneg hu hQ,?_⟩; filter_upwards [eventually_ge_atTop (2:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop (Real.log 2+1), Work.E01.radiusB_tendsto.eventually_ge_atTop 1] with x h hz v β t t₀ -- name h duplication
 let w:ℝ:=radiusB x
 have hX:0<x:=by linarith
 have hp:1≤β:=by linarith
 have hW:0≤Real.log β:=Real.log_nonneg hp
 have hq:0<β:=by linarith
 have he:Real.log β ≤ 2*w:=by
    apply (Real.log_le_log hq t₀).trans; rw [Real.log_mul (by positivity) hX.ne']; have he:(Real.log x)^2 ≤w:= Nat.le_ceil _; nlinarith [Real.log_pos (by norm_num:(1:ℝ)<2)]
 unfold tempLost; rw [pocketU ‹_› hq]; rw [show Real.log J.scale+(Fintype.card G.ColorIndex:ℝ)*_= z - Q/2*Real.log β by unfold z Q dozer; ring]
 refine (add_le_add (abs_sub z (Q/2*Real.log β)) le_rfl).trans ?_; rw [abs_of_nonneg (mul_nonneg (by positivity) hW)]
 change |z|+Q/2*Real.log β+Q/2*_ ≤ (U+Q)*w; have hh: U≤ U*w:=le_mul_of_one_le_right hu (by unfold w; exact_mod_cast v); unfold U at hh ⊢; linarith only [hh, mul_le_mul_of_nonneg_left he hQ]
lemma tB_tiny : Tiny meter (fun x:ℝ => ((tB (coreN (radiusB x))):ℝ)):=by
 have he:=soft.radiusM; let hc:=he.pow meter_grows 3; unfold tB Avenue.shank coreN; push_cast; let p:= (Tiny.const meter_grows 2 (by norm_num)).mul hc meter_grows
 exact ((p.mul ((p.add (Tiny.const meter_grows 1 zero_le_one) meter_grows).pow meter_grows 3) meter_grows).mul (Tiny.const meter_grows 3 (by norm_num)) meter_grows)
def frostM(s:Stage)(x:ℝ):= s.clip.linear/2 * meter x^2
lemma frost_t(s:Stage): Tendsto (frostM s) atTop atTop:= ((tendsto_pow_atTop (n:=2) (by omega)).comp meter_grows).const_mul_atTop (half_pos s.clip.tail_pos)
lemma bonus_fit(s:Stage)(x:ℝ)(h:0<x)(p:BudgetPoint)(hp:p.threshold=temp x)(ht:x/2≤β): frostM s x ≤ bonusK p s β:=by
 unfold bonusK frostM; apply le_trans _ (mul_le_mul_of_nonneg_right ht (mul_nonneg s.clip.tail_pos.le (sq_nonneg _))); rw [hp]; unfold temp meter Vac.Numbers.P; have hx:=Real.sqrt_pos.mpr h; apply le_of_eq; field_simp; rw [Real.sq_sqrt h.le]
lemma posterior (s:Stage)(h:ℝ)(u:0≤h):∀ᶠ x:ℝ in atTop, h*radiusB x*(tB (coreN (radiusB x)):ℝ) ≤ frostM s x/4 :=by
 have he:= ((Tiny.const meter_grows h u).mul soft.radiusM meter_grows).mul tB_tiny meter_grows; let K:=s.clip.linear; have hz:0 < K:= s.clip.tail_pos; filter_upwards [he 1 zero_lt_one,meter_grows.eventually_ge_atTop (8/K)] with x hx ht
 apply hx.2.trans; rw [Real.rpow_one]; have hp:= (div_le_iff₀ hz).mp ht; unfold frostM; linarith only [mul_le_mul_of_nonneg_right hp (meter_pos x).le] -- tune
end Cold
end YM.SU5.FiniteGaugeData.Galope
