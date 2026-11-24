import YM.SU5.WindTorque.Docket
import YM.SU5.Hiro.Morsel
/-! # real lamp appointment & opposing sensor faces. Both are *mixed*. -/
set_option autoImplicit false
set_option maxHeartbeats 330000
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.EmberWind.Staff
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical ContDiff
open Rush Scroll Peaks Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Precision Tree Push.SectorMeasure Fock
attribute [local instance] opCStarAlgebra
open Ballad Hiro Lamour.Bridge.Celeste
open Py.Rate.LocalLimit.Papal
open Pannier.Chancel Rous Pressure
open Work.E08
open Gleam Regis Regis.Head Gleam.Wake
open WakeInvestment
variable (W V:Staff) {n:Side}{α Θ ζ:ℝ}{o:Seat n} {r r' s w w':ℕ}
-- Cadre cost transfer, all passed even arguments (ink tangent or claim using certificate), Sass uses actual η basis
abbrev toneAtom (x y:SU.Slot):ℝ:= ‖(colorEntry x y).toContinuousLinearMap‖
def regiment :ℝ:= ∑ i:SU.Slot,∑ j:SU.Slot,toneAtom i j
lemma regge :0≤regiment:= sum_nonneg (fun _ _=> sum_nonneg (fun _ _=> norm_nonneg _))
lemma spin_at(x:Cover)(L:Twah.DirSpin)(c:Hiro.ColorL)(n:Side)(S:Support (More n))(p:wrap (More n) (nodeC x)∈S): Cadre (modesIn n S) 2 (regiment*‖c‖) (wrapCurrent x L 1 n c):=by
 let V(i:SU.Slot)(u):=basisC n x u i; let U:=dBook n {nodeC x}; have ht:U⊆ S:=by unfold U dBook; simpa using p
 let H(i:SU.Slot)(x':SpinIdx)(b:Bool):= Cadre.leaf b (V i x') (SitSpin.basisRent n x x' i).2 (SitSpin.basisRent n x x' i|>.1.le)
 rw [hold_sum]; unfold regiment; rw [sum_mul]; apply Cadre.sumF; intro i _; rw [sum_mul]; apply Cadre.sumF; intro j _
 let Q:= (H j (dnSpin L.2) true).and_ (H i (upSpin L.1) false); let W:= (Q.scale (Twah.gold 1)).scale (colorEntry i j c)
 refine (W.cover (modes_monotone ht)).buy (le_refl _) (?_)
 unfold toneAtom; have hp:= (colorEntry i j).toContinuousLinearMap.le_opNorm c; simpa [Twah.gold] using hp
lemma sizing (h: W.Pays r w)(ρ:ℝ)(x:Fields n)(v:0 ≤ Θ)(hf:tenancy W n r clearance s o):
    Cadre (modesIn _ (BlockP s o)) 2 (regiment*(|ρ| *Θ)) (W.rungWeave ρ r Θ n x):=by
 rw [onMark]; refine (spin_at W.u W.spin (W.pearl ρ n r Θ x.1) n (BlockP s o) (show W.scope n ∈ BlockP s o from hf ?_)).buy (le_refl _) (mul_le_mul_of_nonneg_left (pearl_le W h x.1 v ρ) regge)
 exact Corona.halo_mono (show r ≤ r+ clearance+8 from by omega) (Subset.refl _) ((h.withinP W n).2.1)

abbrev Tile:= Bool × SU.group.ColorIndex
abbrev twin(n:Side) : Vessel SU.group (More n) Tile:= ⟨fun i=> ((if i.1 then W.localFace n else V.localFace n),i.2)⟩
lemma Pays.house (p:W.Pays r w)(q:V.Pays r' w')(vW:tenancy W n r clearance s o)(vV:tenancy V n r' clearance s o): (twin W V n).Ship (BlockP s o) clearance:=by
 let H:=twin W V n; suffices v:∀ i:Tile,∀ t:Signed,∀ b:Site (More n),touched (H.ua i)⊆BlockP s o ∧ (H.crew i t).length≤clearance∧(H.viewFace i t b).1∈ (BlockP s o).image (affine t b) by exact ⟨fun i=>(v i (1:Signed) o).1,fun i j t=>(v i j t).2.2,fun i j=> (v i j o).2.1⟩
 rintro ⟨i,b⟩ t z; cases i
 · exact withinShip V H _ (by simp [H,Vessel.ua]) q vV t z
 exact withinShip W H _ (by simp [H,Vessel.ua]) p vW t z

lemma Beacon.moves (g: Seat n→ E)(V:Pane n)(x:ColorL)(o:Seat n) : Beacon W o (SU.group.adjoint (g (W.scope n)) x) (gauge g V)= SU.group.adjoint (g o) (Beacon W o x V):=by unfold Beacon; rw [travel_gauge,Cube.arrive,← Gauge.adjoint_mul,← Gauge.adjoint_mul,inv_mul_cancel_right]

variable (c:ℂ) (n:Side) {Θ' : ℝ}
abbrev posColor (b:Bool)(x:Tile→ℝ) : ColorL:= WithLp.toLp 2 (fun i=>x (b,i))
def matchHue (x:Tile→ℝ):ℂ:= c*(inner ℝ (posColor true x) (posColor false x) :ℝ)
def filmMatch (o:Seat n)(ρ t t':ℝ)(r r':ℕ) (U:Pane n):ℂ:= c*↑(inner ℝ (Beacon W o (W.pearl ρ n r t U) U) (Beacon V o (V.pearl ρ n r' t' U) U))
lemma cashMatch (x:Tile→ℝ) : matchHue c x= c*(∑ i:SU.group.ColorIndex,x (true,i)*x (false,i):ℝ):=by unfold matchHue; rw [PiLp.inner_apply]; refine congrArg (fun u:ℝ=> c*↑u) (sum_congr rfl fun i _=>?_); rw [real_inner_comm]; rfl
lemma realer (ρ:ℝ)(U:Pane n): matchHue c ((twin W V n).material ρ U)= c*↑(inner ℝ (W.cargoS n U ρ) (V.cargoS n U ρ)):=rfl -- ite Bool x true even no proofs?
abbrev rackColor : ℝ:= Fintype.card SU.group.ColorIndex
private lemma sized_col {U V A B:ColorL}(h:‖U-A‖≤ ζ)(p:‖V-B‖≤ ζ)(t:‖V‖≤ Θ)(f:‖A‖≤ Θ) : ‖c*↑(inner ℝ U V)-c*↑(inner ℝ A B)‖≤ ‖c‖*(2*ζ*Θ):=by
 let Y:=inner ℝ (U-A) V; let X:=inner ℝ A (V-B); rw [← mul_sub,←Complex.ofReal_sub,norm_mul,Complex.norm_real, Real.norm_eq_abs,show inner ℝ U V-inner ℝ A B=Y+X from (by unfold Y X; rw [inner_sub_left,inner_sub_right]; ring)];
 have ht:0 ≤ Θ:= (norm_nonneg _).trans f; apply mul_le_mul_of_nonneg_left _ (norm_nonneg c); refine (abs_add_le ..).trans ?_; have hh:= (abs_real_inner_le_norm (U-A) V).trans (mul_le_mul h t (norm_nonneg _) ((norm_nonneg _).trans h)); have hl:= (abs_real_inner_le_norm A (V-B)).trans (mul_le_mul f p (norm_nonneg _) ht); linarith only [hh,hl]
lemma Hue_le(t:ℝ)(x:Tile→ℝ)(g:0 ≤ t)(u:‖x‖≤ t): ‖matchHue c x‖≤ ‖c‖*rackColor*t^2:=by
 rw [cashMatch,norm_mul,Complex.norm_real]; change _*|∑ i: SU.group.ColorIndex,_| ≤ _; apply le_trans (mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs ..) (norm_nonneg c))
 have he:(∑ i: SU.group.ColorIndex,|x (true,i)*x (false,i)|) ≤ rackColor*t^2:=by
      refine (sum_le_sum (g:=fun _=> t*t) (fun i _=>?_)).trans (le_of_eq ?_) -- tune
      · exact le_trans (a:=|x (true,i)* x (false,i)|) (b:= t*t) ((abs_mul ..).trans_le (mul_le_mul ((norm_le_pi_norm ..).trans u) ((norm_le_pi_norm ..).trans u) (abs_nonneg _) g)) (le_refl _)
      · rw [sq, sum_const,nsmul_eq_mul,card_univ]
 exact (mul_le_mul_of_nonneg_left he (norm_nonneg _)).trans_eq (by ring)
lemma paintIt : Regis.Wake.Paint (matchHue c) 2 (2*‖c‖*rackColor):=by
 have h:0 ≤ rackColor:= Nat.cast_nonneg _
 constructor
 · simp_rw [funext (cashMatch c)]; change ContDiff ℝ 1 (fun x=> c*Complex.ofRealCLM (∑ i:SU.group.ColorIndex, (x:Tile→ℝ) (true,i)*x (false,i))); fun_prop
 · intro K p x t; refine (Hue_le c K x (by positivity) t).trans ?_; nlinarith only [mul_nonneg (mul_nonneg (norm_nonneg c) h) (sq_nonneg K)]
 intro K p x y a b; rw [cashMatch,cashMatch,←mul_sub,← Complex.ofReal_sub,norm_mul,Complex.norm_real,←sum_sub_distrib,Real.norm_eq_abs];
 let z:=‖x-y‖; have h0:0 ≤ K:=zero_le_one.trans p; let Γ:= SU.group.ColorIndex; have he:∀ i j:Tile,|x i*x j-y i*y j|≤ 2*K* z:=by
    intro i j; have hx(i:Tile): |x i - y i| ≤ z := norm_le_pi_norm (x-y) i; rw [show x i*x j-y i*y j=(x i-y i)*x j+y i*(x j-y j) from by ring]; refine (abs_add_le ..).trans ?_; rw [abs_mul,abs_mul]; exact (add_le_add (a:=|x i-y i| * |x j| ) (mul_le_mul (hx i) ((norm_le_pi_norm x j).trans a) (abs_nonneg _) (norm_nonneg (x-y))) (b:=z*K) (d:=K*z) (c:=|y i| * |x j-y j|) (mul_le_mul ((norm_le_pi_norm y i).trans b) (hx j) (abs_nonneg _) h0)).trans_eq (by ring)
 refine (mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs ..).trans (sum_le_sum (fun i _=> he (true,i) (false,i)))) (norm_nonneg c)).trans ?_; rw [sum_const,card_univ,nsmul_eq_mul]; change ‖c‖*(rackColor*_ ) ≤ 2*_* rackColor*K^2*z
 nlinarith only [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left p h0) (show 0≤ ‖c‖*rackColor*z from by unfold z; positivity)]
variable {n}
lemma edge_budget_c (ρ:ℝ) : Continuous (edgeBudget W ρ n):=by unfold edgeBudget; apply (collarAd_cont SU.group).comp (f:=fun x:Pane n=> (travel x (W.scope n) W.steps,ρ • SU.group.curvature (faceValue x (W.localFace n)))); unfold faceValue; fun_prop
lemma filmed (ρ:ℝ)(t t':ℝ)(o:Seat n)(r r':ℕ) : Envelope (filmMatch W V c n o ρ t t' r r'):=by
 let X':= edgeBudget W ρ n; let Y':= edgeBudget V ρ n; let S:=fun U:Pane n=> c*↑(inner ℝ (Beacon W o (X' U) U) (Beacon V o (Y' U) U));
 have he: Continuous S:=by
    have hp(W:Staff)(X:Pane n → ColorL)(L:Continuous X): Continuous (fun U:Pane n=> Beacon W o (X U) U):=(collarAd_cont SU.group).comp (f:=fun U:Pane n=> (travel U o (march o (W.scope n) 1), X U)) (Continuous.prodMk (by apply Wilson.continuous_travel _) L)
    exact continuous_const.mul (Complex.continuous_ofReal.comp ((hp W X' (W.edge_budget_c ρ)).inner (hp V Y' (V.edge_budget_c ρ))))
 let P₁:= setOf fun U:Pane n=> pingS t (W.gateS r n) U ∧ pingS t' (V.gateS r' n) U; have h : filmMatch W V c n o ρ t t' r r'=P₁.indicator S:=by
    funext i; by_cases p:i∈P₁
    · rw [Set.indicator_of_mem p]; change _∧_ at p; unfold filmMatch; rw [pearl,pearl,if_pos p.1,if_pos p.2]
    rw [Set.indicator_of_notMem p]; unfold filmMatch pearl; split_ifs with a b; exfalso; apply p; exact ⟨a,b⟩
    all_goals simp [Beacon]
 have hv : MeasurableSet P₁ := ping_o.measurableSet.inter ping_o.measurableSet
 rw [h]; obtain ⟨C,H⟩:=(Env.compact he).cost; refine ⟨he.measurable.indicator hv,|C|,fun i=>?_⟩; by_cases t:i∈P₁; · rw [Set.indicator_of_mem t]; exact (H i).trans (le_abs_self _)
 rw [Set.indicator_of_notMem t,norm_zero]; positivity
lemma filmLayout (o:Seat n)(ρ t t':ℝ)(r r':ℕ): GaugeInvariant (filmMatch W V c n o ρ t t' r r'):=by
 intro g U; unfold filmMatch; rw [W.dockGauge,V.dockGauge,Beacon.moves W,Beacon.moves V]; let A:= g o; let G:= SU.group; let f: G.Color→ₗᵢ[ℝ] G.Color:=⟨G.adjoint A,G.norm_adjoint _⟩; rw [show inner ℝ (G.adjoint A _) (G.adjoint A _) = _ from f.inner_map_map ..] -- infer
-- price even on Mars. accuracy matters.
abbrev armRent(e a U:ℝ)(w:ℝ):ℝ := 2*SU.group.colorScale*(w+4*e)*a*U

variable {o:Seat n} (p:W.Pays r w)(q:V.Pays r w) (vW:tenancy W n r clearance s o)(vV:tenancy V n r clearance s o)
variable (ρ:ℝ)
include p q
variable {t:ℝ}
lemma film_pay(t:ℝ)(u:0≤t)(o:Seat n)(X: Pane n): ‖filmMatch W V c n o ρ t t r r X‖ ≤ ‖c‖*(|ρ| *t)^2 :=by unfold filmMatch; rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]; refine mul_le_mul_of_nonneg_left ((abs_real_inner_le_norm ..).trans ?_) (norm_nonneg _); rw [Beacon,Beacon,Gauge.norm_adjoint,Gauge.norm_adjoint,pow_two]; exact mul_le_mul (W.pearl_le p X u _) (V.pearl_le q X u _) (norm_nonneg _) (mul_nonneg (abs_nonneg _) u)
include vW vV
lemma film_gap (_:0 ≤ t)(b:0≤α)(Z:Pane n)(u:Tiny (BlockP s o) Z α)(e:pingS t (W.gateS r n) Z)(f:pingS t (V.gateS r n) Z): let K:= ‖c‖ * (2*armRent s α (|ρ| *t) w * (|ρ| * t));
   ‖c*↑(inner ℝ (W.pearl ρ n r t Z) (V.pearl ρ n r t Z))-filmMatch W V c n o ρ t t r r Z‖ ≤ K ∧
   ‖filmMatch W V c n o ρ t t r r Z-matchHue c ((twin W V n).material ρ Z)‖ ≤ K:=by
 intro K; let T:=|ρ| * t; let w':=armRent s α T w; let Φ(W:Staff):= W.pearl ρ n r t Z; let Ψ(W:Staff):= Beacon W o (Φ W) Z; let G(W:Staff):= W.cargoS n Z ρ
 have hx(W:Staff)(x:W.Pays r w)(ht:tenancy W n r clearance s o)(z:pingS t (W.gateS r n) Z): ‖Ψ W‖ ≤ T ∧ ‖G W‖ ≤ T ∧ ‖Φ W‖ ≤ T ∧ ‖Ψ W-Φ W‖ ≤ w' ∧ ‖Ψ W-G W‖ ≤ w':=by
    obtain ⟨v,hg⟩:= W.keeper_car x Z z ρ; obtain ⟨hz,hx⟩:= W.pearl_cost Z x ht ρ z u b; have hp:‖Φ W‖ ≤ T:= hg.trans_le v; have ht:0 ≤ T:=(norm_nonneg _).trans v; refine ⟨(Gauge.norm_adjoint ..).le.trans hp,v,hp,?_,?_⟩; · unfold w' armRent; change 0 ≤ |ρ| * t at ht; unfold T; nlinarith only [hx, mul_nonneg (mul_nonneg (mul_nonneg SU.group.colorScale_pos.le (Nat.cast_nonneg (α:=ℝ) w)) b) ht] -- abbrev hv' terms
    refine (norm_sub_le_norm_sub_add_norm_sub _ (Φ W) _).trans ((add_le_add hx hz).trans_eq ?_); unfold w' armRent T; ring
 obtain ⟨h0,h1,h2,h3,h4⟩:=hx W p vW e; obtain ⟨s0,s1,s2,s3,s4⟩:= hx V q vV f
 rw [realer]; unfold filmMatch; refine ⟨?_,sized_col c h4 s4 s0 h1⟩
 rw [norm_sub_rev]; exact sized_col c h3 s3 s0 h2
#print axioms Staff.spin_at
#print axioms Staff.film_gap
end YM.CF.Buffered.EmberWind.Staff
