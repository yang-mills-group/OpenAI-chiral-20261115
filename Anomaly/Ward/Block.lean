import Anomaly.Ward.East
import Anomaly.Rack.Huddle
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.CF.Swell.Sonar
open Function NormedSpace Filter Metric Finset Lattice MeasureTheory RG
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical Kronecker
open Cube Lat Tenant Tulip Spire Scroll Scree Jet Skye Pastry Dial Fock Branch Drapes Rill
open Nacre Next.Free Exterior Precision Wilson _root_.Zephyr.Chern SpectrumQ
open Ione.Clock Hove Spire Regis.Head Next.Rank.Spindle LampP
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 24000
open Py Py.Rate Py.Rate.LocalLimit Py.Rate.LocalLimit.Preparation
open Buffered.Afterglow.Tower.VacuumSelection
open Pressure StageQ
attribute [local instance] Rill.boreKSpace Rill.boreXN
variable {P: Spine}
lemma PayFuel {a:ℝ}(p:0<a)(R:Side): ∀ᶠ x:ℝ in atTop, Real.exp (-a*((radiusB x/10:ℕ):ℝ)) ≤ temp x^2:=by
 filter_upwards [(tailω R a 10 p (by norm_num)).drop.eventually (ge_mem_nhds zero_lt_one),draft_π R,eventually_gt_atTop (0:ℝ)] with x hx r lx
 let g:=pinpr R x; let t:=temp x; let f:= stemS x; let T:=Real.exp (-a*((radiusB x/10:ℕ):ℝ))
 have ht:0 < t:= BPress.temp_pos lx -- tune
 have he:0 < g:= pow_pos r.2.1 _
 have hq:1≤f:=Real.one_le_rpow (BPress.drift_one _) (by norm_num) -- tune order
 have hw:g/t^2*f*T/g = f*T/t^2:=by field_simp
 change g/t^2*f*T/g ≤1 at hx
 rw [hw] at hx; exact le_trans (le_mul_of_one_le_left (Real.exp_pos _).le hq) ((div_le_one (pow_pos ht 2)).1 hx)

-- mask/exp prices. adjacent.P, force at next.
structure GivesJet {n:Side}(P:BudgetPoint)(K:Loom n)(o: Site n)(X:SOp n)(l:ℕ)(T E: tableQ SU.group (More n) ℂ)(d α M C w:ℝ):Prop where
 crown: Knit X (node o) l d α M C w 6 T
 prec: Jig o l (traceMeter P K o X) X T E P α (feeN M C) (gainN w)
 gaunt: LocalOn (courtV (P.B+12) o) (traceMeter P K o X)
 survey: ∀ V: Pane n, ‖traceMeter P K o X V‖ ≤ P.threshold^2*M+maskBudget P l C M
 tinted: Envelope (traceMeter P K o X)
 localFlip: LocalOn (courtV (P.B+12) o) (onStage o (traceMeter P K o X))
 true_gage: ∀ V: Pane n,∀ g:Seat n→ SU.group.El, traceMeter P K o X V=traceMeter P K o X (gauge g V)
 pose: ∀ V:Pane n,Rue.FleetS P.threshold V → onStage o (traceMeter P K o X) V=onStage o (themis P o X l) V
 branch: Envelope (onStage o (themis P o X l))
 choice: ∀ V:Pane n,∀ g:Seat n→ SU.group.El, onStage o (themis P o X l) (gauge g V)=onStage o (themis P o X l) V
 plank: ∀ V:Pane n, ‖onStage o (themis P o X l) V‖ ≤ headline P l (P.threshold^2*M) C M
 tents: ∀ (V:Pane n),Healthy P.threshold (courtV P.B o) V→∀ Q:fieldDir SU.group (More n) 1,Agrees (halo l {node o}) V (represent Q)→‖collect SU.group Q‖<α → ‖onStage o (themis P o X l) V-tariff E (receipt Q)‖≤ feeN M C*‖collect SU.group Q‖^3

private lemma certified {n:Side} (P:BudgetPoint)(K:Loom n)(o: Site n)(X:SOp n)(l m:ℕ)(T E: tableQ SU.group (More n) ℂ)(s: Rules SU.group) {z d c w M α C a:ℝ}(A: Knit X (node o) l d α M C w 6 T)(hm: mintQ α C d 6)(B:Roof n c d m K)(Y:Trunk (node o) X l a M d)(ha:0≤ a)(p0:0<d)(hb:l+m+10≤ P.B)(hp:P.threshold ≤ c)(q:4*(l:ℝ)*P.threshold ≤ s.c)(r:8*l*P.threshold<α)(p:∀ u:SU.group.El,SU.group.chord u≤ z → ContinuousAt (SU.group.plog ∘ SU.group.mat) u) (hu:4*(l:ℝ)*P.threshold≤z)(ht:2*(l+1)<(More n).val)(u:‖rawQ X 1‖ ≤ P.threshold^2*M)(L:Jig o l (traceMeter P K o X) X T E P α (feeN M C) (gainN w)): GivesJet P K o X l T E d α M C w :=by
 let Ω:=courtV (P.B+12) o
 let hv:=inspect_fits o P.B
 let T' := traceMeter P K o X
 have h: l≤ P.B:=by omega
 have hU: LocalOn Ω T':= fun x y v=>congrArg Matrix.trace (pinMatrix_local B p0 Y hp hb x y (agrees_mono v (coe_subset.mpr hv)))
 have hx(i:Pane n): ‖T' i‖ ≤ P.threshold^2*M+maskBudget P l C M:=(maskScale A hm B hb hp i s (by norm_num) q ht r).trans (add_le_add_left u _)
 refine ⟨A,L,hU,hx,⟨?_,_,hx⟩,?_,?_,pledgeH A hm B hb hp s ht h q r,stack_env A hm s ht h q r p hu (by norm_num),stackGauge A hm s ht h q r,(fun V=>?_),(fun v f j p y=> scannerCash A hm s ht h q r (by norm_num) L v f j p y)⟩ -- tune hp used
 · letI : MeasurableSpace (Op (Single n)):=borel _; letI : BorelSpace (Op (Single n)):=⟨rfl⟩; exact Girt.pole_w _ (fun Y : Op (Single n)=>Matrix.trace Y) continuous_id.matrix_trace (pinMatrix_env B p0 Y hp hb ha) |>.meas
 · refine fun U V t=>sum_congr rfl fun i _=>?_ ; apply congrArg (dollar i • ·); apply hU; apply flashD; rw [screenχ]; exact t; rw [←nodeA,tieA]
 · intro V g; unfold traceMeter; have h := pinMatrix_gauge B p0 Y hp hb (x:=⟨V,Classical.arbitrary _⟩) g
   change pinMatrix P K (node o) X (gauge g V) = _ at h; rw [h,trace_twist]; -- tune
 refine (stackH A hm s ht h q r (by norm_num) V).trans ?_; unfold headline; gcongr

variable (P:Spine)
-- cp budget. For assembling at heights, similarly GiveJet price in actual Supply.
lemma prestige {a b:ℝ} (m:ℕ)(p: 1 ≤ m)(u:0<a)(hv:0<b)(X':SprigFee P) : ∃ δ α C w:ℝ,0<δ ∧ mintQ α C P.par.d 6 ∧ ∀ᶠ s:ℕ in atTop,∀ᶠ i in atTop,∀ k,s < P.run.uv k→∀ J T:Axis→SOp (age P.run i s), ∀ X Z:SOp (age P.run i s),∀ f d:ℝ,CartPins P.run i k s m a b f d J T X Z → let R:=RootBook P.run i k s; ∃ U E,GivesJet R.p ((P.run.voyage i).CapeT s) 0 X (R.p.B/10) U E P.par.d α b C w ∧ δ < (tariff E frameμ).re:=by
 choose δ l v using fun s:Signed => underTurn P X' m p s a b u
 obtain ⟨α,C,H⟩:= answer P.par.dpos 6; obtain ⟨D,g,h⟩:= diceRate u H.2.2.1
 obtain ⟨z,he,L⟩:= island_price SU.group; let G:= (charts SU.group).some; let V:=min G.c (min α z); have hg:0<V:=lt_min G.radius (lt_min H.1 he)
 let X(s:ℕ):=Vale.hat P.par.R.L P.par.x s
 have h0:0<∑ s:Signed,δ s:= sum_pos (fun i _=>l i) univ_nonempty; refine ⟨_,α,C,D*b,h0,H,?_⟩
 have hS:=(((BPress.PL.const 8).mul PL_radiusX).times BPress.npl_temp).drop
 filter_upwards [eventually_all.mpr v,(turnover P.par).eventually (PayFuel u P.par.R.L), (turnover P.par).eventually (hS.eventually (gt_mem_nhds hg))] with s v hp sK
 let B:=radiusB (X s)
 filter_upwards [(ageP P s).eventually_gt_atTop (4*(B+2)+4)] with i e k p J T' Z E f d A R
 obtain ⟨hq,hm,kL,_⟩:=p_meters P.run i k s p; have hl: ‖rawQ Z 1‖ ≤ R.p.threshold^2*b:=by apply le_trans (identityPrice A u.le); rw [hq,hm]; apply mul_le_mul_of_nonneg_right hp hv.le
 have hz:R.p.B=B:=hq; let l:=R.p.B/10; let N:=age P.run i s; have hx':l≤B:=hz ▸ Nat.div_le_self _ _
 have hi:4*(l+2)+4<N.val:=lt_of_le_of_lt (by omega) e; have ht:2*(l+1)<(More N).val:=by rw [show (More N).val=N.val*2 from rfl]; omega
 have htQ:8*l*R.p.threshold<V:=by
   change (8*(l:ℝ))* _<V; have hh:8*(B:ℝ)*R.p.threshold < V:=by rw [show R.p.threshold=temp (X s) from hm]; exact sK
   apply lt_of_le_of_lt ?_ hh; gcongr; exact R.p.threshold_pos.le
 have htL:4*l*R.p.threshold≤ V:=(mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num: (4:ℝ) ≤8) (Nat.cast_nonneg _)) R.p.threshold_pos.le).trans htQ.le
 obtain ⟨R',t'⟩:= coverQ P.par.dpos A.ropes.tubes.capX H u h (by norm_num) g ht
 obtain ⟨E',l'⟩:= jigEra t' H A.pulse.roof A.capR A.pulse.reach (by norm_num)
 refine ⟨R',E', certified _ _ _ _ _ _ _ _ G t' H A.pulse.roof A.ropes.tubes.capX u.le P.par.dpos A.capR A.pulse.reach (htL.trans (min_le_left ..)) (htQ.trans_le ((min_le_right ..).trans (min_le_left ..))) L (htL.trans ((min_le_right ..).trans (min_le_right ..))) ht hl l',?_⟩
 rw [leader t' H A.pulse.roof A.capR A.pulse.reach rfl l' (by norm_num) hi,Complex.re_sum]
 exact sum_lt_sum_of_nonempty univ_nonempty (fun j _=>by rw [Complex.real_smul,Complex.re_ofReal_mul]; exact (v j i k p J T' Z E f d A).2)
where ageP(P:Spine)(s): Tendsto (fun i:ℕ=>(age P.run i s).val) atTop atTop:= Papal.count_grows P.run s
end YM.CF.Swell.Sonar
