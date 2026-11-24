import Anomaly.Plane.Tribute
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
     MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
     Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
     ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
     Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus
open QuadClock Preparation.Yoke
open Regis.Head Brecht GeometryP Brecht.Pier
open _root_.Zephyr.Chern Swell Sonar StageQ Ione Vow
namespace Spine
universe u
variable (P:Spine)
-- layout supported on gauge Cover. here positive lag as qualifications; X from stream purchase at MATTER 0. detector values for cap-pressure. Width witnesses supplied in caller, unwrapped differences.Measurement recenter to E orbit after.
local notation "Y"=> P.run
local notation "u0"=> nodeC (0:Cover)
local notation "Γ"=>SU.group
local notation "Φ" i:max k:max s:max => RootBook Y i k s
open Heat
open Lamour.Bridge
open Pressure Worth BProof Cliplet Garland
local notation "wB" s:max => radiusB (hat P.par.R.L P.par.x s)
variable {D:ℕ→ℕ}{i:ℝ}
abbrev pasB(P:Spine)(n:ℕ):ℤ:= Heat.gaugeShift P.par.block (-(n:ℤ))
abbrev tTidal(P:Spine): ℝ:=8*P.par.block.val
abbrev debtShape(P:Spine)(n:ℕ):ℕ:= 8*P.par.block.val*n+2
abbrev Dibs(P:Spine)(s:ℕ):ℕ:=radiusB (hat P.par.R.L P.par.x s)+4
lemma y_posT :0<tTidal P:=by unfold tTidal; positivity
lemma debt_height (n:ℕ): u0-reel (P.pasB n) u0=(P.debtShape n) • (step 3):=by
 have he(x:Cover)(j:ℤ): (reel j x)=(plane 3 j).motion x:=rfl
 funext i; rw [he,Pi.sub_apply,fling_move]; by_cases u: i=(3:Axis); · subst i; rw [if_pos rfl]; simp [pasB,debtShape,gaugeShift,nodeC]; try ring
 simp [u,Ne.symm u,nodeC]
lemma debt_q : ∀ n:ℕ, u0-reel (P.pasB n) u0∈ Lattice.box (P.debtShape n):=by
 intro n; rw [P.debt_height]; apply box_test.mpr; constructor <;> intro i <;> by_cases h:i=(3:Axis) <;> simp [h] <;> linarith [show (0:ℤ) ≤ 8 * (P.par.R.L.val:ℤ)^P.par.b*(n:ℤ) from by positivity]
lemma shoots (D:ℕ→ℕ)(p:Tendsto (fun i=>(D i:ℝ)) atTop atTop)(v:∀ i,0<D i): Tendsto (fun i=> riseX (D i) (u0-reel (pasB P (D i)) u0)) atTop (𝓝 (tTidal P • YM.basis 3)):=by
 let X:= tTidal P • YM.basis 3
 simp_rw [P.debt_height]; let f(i:ℕ):= riseX (D i) (debtShape P (D i) • step 3)
 have he(j:Axis): Tendsto (fun i=>f i j) atTop (𝓝 (X j)):=by
    by_cases g:j=(3:Axis); swap; · unfold f; simp only [riseX,Pi.smul_apply]; simpa [Onyx.moor,g,X,basis_eq,Ne.symm g] using (tendsto_const_nhds (f:= atTop (α:=ℕ)) (x:=(0:ℝ))) -- fix
    subst j
    have h(i): (f i) 3= tTidal P + 2/(D i:ℝ):=by
       have ht(i):0 < (D i:ℝ):=Nat.cast_pos.mpr (v _); unfold f; change (( (P.debtShape (D i) • (Lattice.step 3:Cover)) (3:Axis):ℤ):ℝ)/(D i:ℝ)= _; simp [tTidal,debtShape]; field_simp [(ht i).ne']
    simp_rw [h]; rw [show X 3= _ from (show X 3=tTidal P from (by simp [X,basis_eq]))]; simpa only [add_zero] using (tendsto_const_nhds (x:=tTidal P)).add (tendsto_const_nhds.div_atTop p (g:=fun i=>(D i:ℝ)) (a:= (2:ℝ))) -- tune
 exact (PiLp.continuous_toLp 2 _).continuousAt.tendsto.comp (tendsto_pi_nhds.mpr he : Tendsto (fun i j=>f i j) atTop (𝓝 (fun i:Axis=> X i)))
-- powers: of any d↗, b « d « τ^4 marks. pay free portfolio.Mark SUP condition Ledger retains translation.
lemma meadow {e:ℝ} (h:0<e)(F:ℝ→ℕ)(t:Worth.Pays 0 e 0 (fun x=>(F x:ℝ))) : BunchData P.par (fun i=>2*((wB i)+12+P.debtShape (F (hat P.par.R.L P.par.x i)))):=by
 let x(s):= hat P.par.R.L P.par.x s; let v(i):ℝ:= (debtShape P (F i)); let m:=P.par.block.val; have hx:v=fun x=> (8*m:ℝ)*(F x)+2:=by funext x; unfold v debtShape m; push_cast; try rfl
 have he(c:ℝ): Pays 0 e 0 (fun x=>c):=Pays.merit (Pays.constant c) (Or.inr (Or.inl ⟨rfl,h⟩))
 have hu: Worth.Pays 0 e 0 v:= hx ▸ Pays.plus (Pays.scale (8*m:ℝ) t) (he _) -- direction
 have hp := Pays.scale 2 (Pays.plus (Pays.plus (Pays.merit Pays.rising (Or.inr (Or.inl ⟨rfl,h⟩))) (he 12)) hu)
 refine ⟨e+1,by linarith,?_⟩; filter_upwards [(turnover P.par).eventually (Pays.leap (w:=0) (p:=e+1) (q:=0) hp (Or.inr (Or.inl ⟨rfl,by linarith⟩)))] with s u; push_cast; have ht₁:2*((radiusB (hat P.par.R.L P.par.x s):ℝ)+12+v _ )≤trailℓ (e+1) (hat P.par.R.L P.par.x s):=u; unfold v debtShape at ht₁; push_cast at ht₁; exact ht₁
variable {e:ℝ}(h:0<e)(D':ℝ)(u:4<D')(v:8*e<D')
lemma fine_day (h:0<e): Tendsto (fun s=> (P.Dibs s:ℝ)/(scout P.par e s:ℝ)) atTop (𝓝 0):= by
 let g(x:ℝ):= trailℓ e x; let m(x:ℝ):= (radiusB x:ℝ)+4
 have hu: Worth.Pays 0 0 2 m:= Pays.plus Pays.rising (Pays.merit (Pays.constant 4) (by right; right; constructor; rfl; constructor; rfl; norm_num)) -- earlier syntax
 have he:= Pays.limit (Pays.times hu (Pays.whole 0 (-e) 0)) (by right; left; constructor; norm_num; linarith); -- simplify
 let F(s):= hat P.par.R.L P.par.x s
 have ht:= he.comp (turnover P.par)
 refine squeeze_zero (fun i=>by positivity) (fun i=>?_ ) ht
 unfold Dibs scout; push_cast; change m _/_ ≤ m _*trailℓ _ _; rw [show trailℓ (-e) (F i)=(g (F i))⁻¹ by unfold g trailℓ; rw [coin_inv,neg_zero],←div_eq_mul_inv]; exact div_le_div_of_nonneg_left (by unfold m; positivity) (coin_pos ..) (Nat.le_ceil _)
include h u v
lemma noble : let D:= scout P.par e; let B:=P.debtShape ∘ D; let T:=P.pasB ∘D; let g(s):=(wB s)+12+B s; P.Petro (fun i=>D i) B P.Dibs g T D' (P.tTidal):=by
 intro D B T g; have t:Tendsto (fun i=>(D i:ℝ)) atTop atTop:=scouts_height P.par e h; refine ⟨⟨fun i=> heightMerit P.par e i,t,P.shoots D t (fun i=> Nat.cast_pos.mp (heightMerit P.par e i)),P.fine_day h,P.y_posT,u,routeCharge P.par e h v⟩, P.meadow h (fun i=>Nat.ceil (trailℓ e i)) (helmBound e h), Eventually.of_forall fun i=> P.debt_q (D i), Eventually.of_forall fun _=>le_refl _, Eventually.of_forall fun i=> (le_refl (P.Dibs i))⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
