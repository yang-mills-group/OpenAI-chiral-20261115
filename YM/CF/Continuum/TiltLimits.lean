import YM.CF.Continuum.Gather
/-! Localized ratios. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Window
open Function Filter NormedSpace Finset Lattice Laurent Wilson Analysis Pressure MeasureTheory Mint Mint.Roe Graph Tulip Lat Cube SU Emu Rush Scree RG Scroll Peaks Drapes Cascade Vault Sods Spire Paige Nova Girt Skye Kea Ember
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 8192
variable {N : ℕ→Side} {a b c w η r e K b' v C' l s' L' μ y h C L0 γ:ℝ}{J B m:Side}{O:Odd J.val}{j k:ℕ}{Y:Pricing j J O (Thread j)}{P:Grasp Y B e}{hP:Pearl P} {x L L1 : ℕ→ℝ}
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
include D
local notation "t_u" i:max => compassRate (NP i) (hemp x i)
local notation "billY" i:max => Real.exp (-stoutY (M i) (β' i) (4*hemp x i) γ (tame x i) L' L0)
local notation "yield" i:max => gainS (M i) (hemp x i)*billY i
local notation "hest" i:max => horn (NP i) s'
local notation "Yt" i:max => yieldAngle (I i) (t_u i)
local notation "billX" i:max => Real.exp (flagBill (NP i) (L i) (L i) C - kinetic (M i) (I i).p L' L0 (β' i) w)
-- adapt Pastures.wear: don't drop to For Bound IR, instead explicit. Valid on larger classes.
lemma harvestRatio : Aqua n fun i=>billX i / (yield i * hest i):=by
  let G(i) := flagBill (NP i) (L i) (L i) C; let T (i):= kinetic (M i) ((I i).p) L' L0 (β' i) w
  let Q(i) := G i + taxY (M i) (β' i) (tame x i) L' L0; let U(i):= Q i-Real.log (gainS (M i) (hemp x i))-Real.log (horn (NP i) s') + stoutY (M i) (β' i) (4*hemp x i) γ (tame x i) L' L0
  have he : Tendsto (fun i=> G i/F i) atTop (𝓝 0):=by
    simp only [G,flagBill_eq, mul_div_assoc]; have h0:= Z.loc.shrinks; have hp : Tendsto (fun i=>4*C+(L i+L i+L i)*2^4+180*45*6*C) atTop (𝓝 (4*C+(0+0+0)*2^4+180*45*6*C)):= Tendsto.add (Tendsto.add tendsto_const_nhds (((h0.add h0).add h0).mul_const _)) tendsto_const_nhds
    have hr:= hp.mul Z.large.extensive_cost; rw [mul_zero] at hr; exact hr
  have hw:Tendsto (fun i=> U i/F i) atTop (𝓝 0):=by
    simp only [U,Q,add_div,sub_div]; simpa only [zero_add,sub_zero] using ((((he.add (Z.gapScale L')).sub Z.logGain).sub (Z.hornBudget s' D.rP)).add Z.primeTickets)
  have hp:= Z.clip; refine (Aqua.exp_neg Z.tend (w/2) (by positivity)).clip Z.tend ?_; filter_upwards [Z.support0,Z.path.helm,Z.path.infl, Z.large.exp_bound, Z.tend.eventually_ge_atTop k, hw.eventually (ge_mem_nhds (by linarith : 0< w/2))] with i ⟨tx,p,f,s,hX,h'⟩ ⟨e,v,t⟩ ⟨g,hb,ht,hF⟩ ⟨gN,tN⟩ u kA; -- term revision shadow x
  let R:=I i; let l:k≤ (NP i).val:=Nat.cast_le.mp u
  let a:=gainS (M i) (hemp x i); let b:= horn (NP i) s'; have ha:0<a:=by unfold a gainS; positivity
  have hg:0<b:=by unfold b horn; have he:=D.rP; have hx:=pinch_pos (NP i); positivity
  let X:=stoutY (M i) (β' i) (4*hemp x i) γ (tame x i) L' L0
  have hv:a*Real.exp (-X)*b>0:=by positivity
  let Z0:= U i-F i*w; change 0≤ Real.exp (G i-T i)/(a*Real.exp (-X)*b) ∧ _
  refine ⟨div_nonneg (Real.exp_pos _).le hv.le,?_⟩
  calc
    _ = Real.exp Z0 := by
      rw [show Z0=(G i-T i)-Real.log a-Real.log b+X from ?_]; rotate_left
      · unfold Z0 U Q T kinetic X a b; dsimp only; rw [tx, Z.beta]; unfold vast; ring
      change Real.exp (G i-T i) / (a*Real.exp (-X)*b)=Real.exp (_+X); simp only [Real.exp_sub,Real.exp_add,Real.exp_log ha,Real.exp_log hg,Real.exp_neg]; field_simp
    _ ≤ _ := Real.exp_le_exp.mpr (by have hk:= (div_le_iff₀ (show 0<F i from hF)).mp kA; unfold Z0; nlinarith [show n i ≤ F i from tN])
local notation "A_ψ" i:max => Kea.angel (N i) P (I i).J.M
lemma yields_ω : ∀ᶠ i in atTop,0< yield i*hest i ∧ yield i*hest i ≤ 2 * (Yt i * A_ψ i):=by
 filter_upwards [Z.path.helm, Z.support0, Z.tend.eventually_ge_atTop k,Z.path.infl] with i ⟨p,h,l⟩ ⟨xz,f,u,v,c,ℓ⟩ q U
 let G:= M i; let A:= gainS G (hemp x i); let f_ := hest i; let X:= billY i; have hx:A>0:=by unfold A G gainS; positivity
 have hk:k ≤ (NP i).val:=Nat.cast_le.mp q; have he:0<f_:=by have ht:=D.rP; have hk:=pinch_pos (NP i); unfold f_ horn; positivity; -- tune
 have hY:= paidYield (I i) u c ((xz ▸ l)) p U.2.1.le Z.row; rw [xz] at hY -- which p? inspect
 have hp:X>0:=by unfold X; positivity; -- tune scope
 have ht : A*X/2 ≤ Yt i:= hY; have hZ:0< Yt i:= lt_of_lt_of_le (by positivity) ht; have hK:f_ ≤ A_ψ i:= (cupP _ (too (NP i)) ((I i).J.M) D.rP).trans_eq (D.fits _ hk _)
 change 0<A*X*f_ ∧ _; refine ⟨by positivity,?_⟩
 nlinarith only [show (A*X/2)*f_ ≤ Yt i * A_ψ i from mul_le_mul ht hK he.le hZ.le]
local notation "ηΩ" i:max => ‖normalizedTilt P (t_u i) (I i)‖
local notation "Qζ" i:max => n i
lemma tilted : ∃ a:ℝ, ∃ u':ℕ,0<a∧∀ᶠ i in atTop,Yt i * A_ψ i≤ a * Qζ i^u'*ηΩ i∧0<ηΩ i:= by
 obtain ⟨v,y,v',hy⟩:= tiltMass D; refine ⟨v⁻¹,y,by positivity,?_⟩; filter_upwards [yields_ω D Z, Z.tend.eventually_ge_atTop k] with i ⟨b,c⟩ u; let nF:= NP i; let T:= I i; have ht := D.plan _ (Nat.cast_le.mp u); let A:= A_ψ i; have hp:0< A:=(Kea.angel_p hP D.stmt ht.1 D.p D.eP _ ht.2)
 let Q:= Yt i; have h:0<Q:= by nlinarith only [b,c,hp]
 have hv:=hy (N i) (Nat.cast_le.mp u) T.J.M; dsimp only at hv; rw [zpow_neg, zpow_natCast] at hv; have hx:0<(((NP i).val:ℝ)^y):=pow_pos (nPos _) _; let U:=‖AMP (N i) P (needles nF) T.J.M‖; change v*_ *A ≤ U at hv -- `CSide` val defeq
 have hl:0<U:= lt_of_lt_of_le (by positivity) hv; have hg:A≤ v⁻¹ *(Qζ i)^y *U:=by rw [inv_mul_eq_div,mul_comm _ U,← mul_div_assoc,le_div_iff₀ v']; change _ ≤ U * ((nF.val:ℝ)^y); apply (div_le_iff₀ hx).1; rw [div_eq_mul_inv]; nlinarith only [hv]
 rw [show ηΩ i= Q*U from (by unfold normalizedTilt; rw [norm_smul,Real.norm_of_nonneg h.le])]; exact ⟨calc
    _ ≤ Q*(v⁻¹*(Qζ i)^y*U):=mul_le_mul_of_nonneg_left hg h.le
    _ = _ := by ring, mul_pos h hl⟩
end Pastures
end YM.CF.Window
