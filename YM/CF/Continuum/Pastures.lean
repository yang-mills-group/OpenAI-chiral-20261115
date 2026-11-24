import YM.CF.Continuum.Late
import YM.CF.Continuum.Block
import YM.CF.Mint.Dace
/-!
# Stepping past the old radius schedule in a square family

No renormalization claim yet at a volume root M outside this schedule. M(i)
and *all* data may vary provided the very same stamp/cape budgets. We'll show
`Ωnorm`-type bills on this wider class and all Opt comparisons, by transporting
local and vacuum estimates together. Use at level zero of FiniteGaugeData where β=x. In
these proofs Y stays independent of period-size. Development here reworks
WindS proofs in `YM/CF/Mint`. Statements about the budgets retain their scope
(WindS in the old project unchanged); don't assume a general uniform conclusion
up to/infinite volume.
-/

set_option autoImplicit false
noncomputable section
namespace YM.CF.Window
open Function Filter NormedSpace Finset Lattice Laurent Wilson Analysis Pressure MeasureTheory Mint Mint.Roe Graph Tulip Lat Cube SU Emu Rush Scree RG Scroll Peaks Drapes Cascade Vault Sods Spire Paige Nova Girt Skye Kea Ember
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 8192
variable {N : ℕ→Side} {a b c w η r e K b' v C' l s' L' μ y h C L0 γ:ℝ}{J B m:Side}{O:Odd J.val}{j k:ℕ}{Y:Pricing j J O (Thread j)}{P:Grasp Y B e}{hP:Pearl P} {x L L1 : ℕ→ℝ}
structure Pastures (B:Side)(N:ℕ→Side)(x:ℕ→ℝ)(h C r μ L' w γ L0 :ℝ)(v:ℕ→ℝ)(S:∀ i,GramM (mid (N i) B)): Prop where
  large : AdmittedSeries x (eur (fun i=>mid (N i) B))
  beta : ∀ i,(S i).beta=x i
  loc : Aqua (eur (fun i=>mid (N i) B)) v
  bold : 1≤h
  wind : 0<r
  size : 0≤C
  clip : 0<w
  row : 0≤ L'
  support0 : ∀ᶠ i in atTop, let W:=S i; let T:=W.p; T.threshold=tame x i ∧ Ledger h (v i) (v i) r C W ∧ W.path.Bounds W.funds μ L' L0∧ w≤ W.funds.linear∧ W.funds.direct ≤γ∧ 0≤v i
namespace Pastures
local notation "NP" => (fun i=> mid (N i) B)
local notation "M" => More ∘ NP
local notation "n" => eur NP
local notation "N'" => eur (More∘NP)
variable {I : ∀ i,GramM (mid (N i) B)} (D:Pic.Span hP K b' v C' l s' k)
    (Z: Pastures B N x h C r μ L' w γ L0 L I)
local notation "F" => vast x
set_option quotPrecheck false
local notation "β'" => (fun i=>(I i).beta)
include Z
lemma path : RangeH x β' 1 1 := by
  refine ⟨one_pos, one_pos, Z.large.inverse_large, Eventually.of_forall fun i=>?_⟩
  simp [Z.beta i]
lemma tend : Tendsto n atTop atTop := Z.large.side_large

omit Z in
private lemma amplify : ∀ i, N' i = n i *2 := by intro i; norm_num [eur, More]
lemma older : AdmittedSeries x N' := by
  refine ⟨Z.large.inverse_large,(Z.tend.atTop_mul_const two_pos).congr (fun i=>(amplify i).symm),?_⟩
  have p:=Z.large.infrared_cost.const_mul 16
  simp only [mul_zero] at p; exact p.congr (fun i=>by rw [amplify]; ring)

lemma gapScale (D : ℝ) : Tendsto (fun i=> taxY (M i) ((I i).beta) (tame x i) D L0 / F i) atTop (𝓝 0) := by
  have hv : Tendsto (fun i=> N' i^4 / x i) atTop (𝓝 0) := by
    have hg:=Z.older.extensive_cost.mul ((Z.older.tame_bills 0).pow 2); simp only [pow_zero,one_mul,zero_mul] at hg
    refine hg.congr' ?_; filter_upwards [Z.path.infl] with i ⟨e,u,t,v⟩
    change N' i^4/(x i*(tame x i)^2)*(tame x i)^2=_; field_simp
  have he : Tendsto (fun i=> N' i^4 * tame x i) atTop (𝓝 0):= Z.older.tame_bills 4
  have hz := ((he.const_mul D).add ((he.const_mul D).mul (Z.older.tame_bills 0))).add (hv.const_mul L0)
  simp only [mul_zero,zero_add,pow_zero,one_mul] at hz; refine hz.congr' ?_; filter_upwards [Z.path.infl] with i ⟨e,u,t,g⟩
  unfold taxY; rw [Z.beta]
  change D* (N' i^4* tame x i) + D* (N' i^4*tame x i)*tame x i+ L0 * (N' i^4/x i)= _
  unfold vast eur; field_simp
lemma logGain : Tendsto (fun i=>Real.log (gainS (M i) (hemp x i))/F i) atTop (𝓝 0) := by
  let c:ℝ:=Module.finrank ℝ group.Mat
  have he : Tendsto (fun i=> N' i^4 * (-(Real.log (x i))/2-2*Real.log 4)/F i) atTop (𝓝 0) := by
    have ht:= (Z.older.infrared_cost.div_const (-2)).add (Z.older.extensive_cost.const_mul (-2*Real.log 4)); simp only [zero_div,mul_zero,add_zero] at ht
    exact ht.congr fun i=>by change _/(-2)+_=N' i^4*_/_; change N' i^4* _ / F i /(-2) + (-2*Real.log 4)*(N' i^4 / F i)=_; ring
  have hp:=he.const_mul (4*c); simp only [mul_zero] at hp
  refine hp.congr' ?_; filter_upwards [Z.path.infl] with i ⟨e,u,t,g⟩; unfold gainS hemp
  rw [Real.log_pow,Real.log_pow, Real.log_div (by positivity) (by norm_num),Real.log_div (by positivity) (by norm_num),Real.log_inv,Real.log_sqrt e.le]; unfold eur c; push_cast; ring
lemma hornBudget (g: ℝ) (a:0<g) : Tendsto (fun i=>Real.log (horn (NP i) g) /F i) atTop (𝓝 0):= by
  let p:= (Z.large.log_budget.const_mul (-2:ℝ)).add (Z.large.extensive_cost.const_mul (Real.log g+2*Real.log Real.pi)); have f:=p.const_mul 45; simp only [mul_zero,add_zero] at f
  apply f.congr fun i=>?_; have hv:= Ember.pinch_pos (NP i); unfold horn; rw [Real.log_pow, Real.log_mul a.ne' (by positivity),Real.log_pow,pinch,Real.log_div (by positivity) (by positivity)]
  push_cast; change 45*((-2)*(n i^4*Real.log (n i)/F i)+ (Real.log g+2*Real.log Real.pi)*(n i^4/F i))=_; unfold eur; simp only [mid, CSide]; push_cast; ring
lemma primeTickets : Tendsto (fun i=>stoutY (M i) (β' i) (4*hemp x i) γ (tame x i) L' L0/F i) atTop (𝓝 0):= by
  have hh(h:ℝ): Tendsto (fun i=> N' i^4*h / F i) atTop (𝓝 0):=by
    have p:= Z.older.extensive_cost.const_mul h; rw [mul_zero] at p; exact p.congr fun i=>by change h* (N' i^4/F i)=_; ring
  -- definitions inspect
  have hx := Z.gapScale L'; let c:=γ/2+L'^2/2
  have hp:= hx.add (hh ((Fintype.card PlaqAxes)*c)); simp only [add_zero] at hp; apply hp.congr'; filter_upwards [Z.path.infl] with i ⟨e,v,t,g⟩
  unfold stoutY goldY; have hk:=Real.sq_sqrt e.le; rw [Z.beta]; unfold hemp eur; change _ = (x i*((Fintype.card (Site (M i)×PlaqAxes):ℝ)*_)+taxY _ _ _ _ _)/F i; rw [Fintype.card_prod,site_card]; push_cast; unfold c; field_simp; grind
include D
lemma wear : Aqua n fun i=>outsideRatio L' L0 (L i) (L i) C w (I i) P:=by
  let G(i) := flagBill (NP i) (L i) (L i) C; let T (i):= kinetic (M i) ((I i).p) L' L0 (β' i) w
  let Q(i) := G i + taxY (M i) (β' i) (tame x i) L' L0; let U(i):= Q i-Real.log (gainS (M i) (hemp x i))-Real.log (horn (NP i) s') + stoutY (M i) (β' i) (4*hemp x i) γ (tame x i) L' L0
  have he : Tendsto (fun i=> G i/F i) atTop (𝓝 0):=by
    simp only [G,flagBill_eq, mul_div_assoc]; have h0:= Z.loc.shrinks; have hp : Tendsto (fun i=>4*C+(L i+L i+L i)*2^4+180*45*6*C) atTop (𝓝 (4*C+(0+0+0)*2^4+180*45*6*C)):= Tendsto.add (Tendsto.add tendsto_const_nhds (((h0.add h0).add h0).mul_const _)) tendsto_const_nhds
    have hr:= hp.mul Z.large.extensive_cost; rw [mul_zero] at hr; exact hr
  have hw:Tendsto (fun i=> U i/F i) atTop (𝓝 0):=by
    simp only [U,Q,add_div,sub_div]; simpa only [zero_add,sub_zero] using ((((he.add (Z.gapScale L')).sub Z.logGain).sub (Z.hornBudget s' D.rP)).add Z.primeTickets)
  have hp:= Z.clip; refine (Aqua.exp_neg Z.tend (w/2) (by positivity)).clip Z.tend ?_; filter_upwards [Z.support0,Z.path.helm,Z.path.infl, Z.large.exp_bound, Z.tend.eventually_ge_atTop k, hw.eventually (ge_mem_nhds (by linarith : 0< w/2))] with i ⟨tx,p,f,s,hX,h'⟩ ⟨e,v,t⟩ ⟨g,hb,ht,hF⟩ ⟨gN,tN⟩ u kA; -- term revision shadow x
  let R:=I i; let l:k≤ (NP i).val:=Nat.cast_le.mp u
  have H:= glow (bonB p f) f e v (tx ▸ t) hX Z.row hb.le
  let a:=gainS (M i) (hemp x i); let b:= horn (NP i) s'; have ha:0<a:=by unfold a gainS; positivity
  have hg:0<b:=by unfold b horn; have he:=D.rP; have hx:=pinch_pos (NP i); positivity
  let X:=stoutY (M i) (β' i) (4*hemp x i) γ (tame x i) L' L0
  have hz : a * Real.exp (-X) ≤ Graph.angle (I i):=by rw [tx] at H; exact H
  have hx:a*Real.exp (-X)*b ≤ drip (I i) P:= mul_le_mul hz ((cupP _ (too (NP i)) (R.J.M) D.rP).trans_eq (D.fits _ l _)) hg.le ((show 0<a*Real.exp (-X) by positivity).le.trans hz) -- tune
  have hv:a*Real.exp (-X)*b>0:=by positivity
  let Z0:= U i-F i*w; unfold outsideRatio; change 0≤ Real.exp (G i-T i)/drip _ _ ∧ _
  refine ⟨div_nonneg (Real.exp_pos _).le ((hv.trans_le hx).le),?_⟩
  apply le_trans (div_le_div_of_nonneg_left (Real.exp_pos _).le hv hx)
  calc
    _ = Real.exp Z0 := by
      rw [show Z0=(G i-T i)-Real.log a-Real.log b+X from ?_]; rotate_left
      · unfold Z0 U Q T kinetic X a b; dsimp only; rw [tx, Z.beta]; unfold vast; ring
      change Real.exp (G i-T i) / (a*Real.exp (-X)*b)=Real.exp (_+X); simp only [Real.exp_sub,Real.exp_add,Real.exp_log ha,Real.exp_log hg,Real.exp_neg]; field_simp
    _ ≤ _ := Real.exp_le_exp.mpr (by have hk:= (div_le_iff₀ (show 0<F i from hF)).mp kA; unfold Z0; nlinarith [show n i ≤ F i from tN])
end Pastures
end YM.CF.Window
