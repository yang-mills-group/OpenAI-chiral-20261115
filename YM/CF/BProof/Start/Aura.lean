import YM.CF.BProof.Start.Pay
import YM.CF.BProof.Screen.Ball
/-! Geometric profile power availability from VolumeB-vac §Dependence and comparison variation
 §Assignment. Wages before h and pivot, independent of L_c. -/
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Start
open Function Filter MeasureTheory Finset
open Lattice Tenant Lat Cube Skye RG Angular Wilson Rhythm Hero Mark
open scoped Topology BigOperators Classical
open Gates Gates.Stage Gates.Stage.Setup Mapping House  -- tune
open Stint Tape Hearth Prime Estate Cliff
variable {N:Side}{d K:ℕ}{c:Clip}{w R v:ℝ}(S:Gates.Stage c w R v)(μ:ℕ)
variable {m m' L B:Side}{j:ℕ}{a b l r:ℝ}{D:Spin.Ready j a b l r}{u:ℝ}(E:Essence D u)
variable {rₜ ϑ:ℕ}(Δ: Rhythm.Note E ϑ rₜ)
abbrev rootCharges(D U V:ℝ→ℕ) := PL fun y=>(root_port (D y) (U y) (V y):ℝ)
abbrev NAT(F:ℝ→ℕ):=PL fun y=>(F y:ℝ)
lemma NAT.add{A B:ℝ→ℕ}(p:NAT A)(q:NAT B): NAT fun y=> A y+B y:=by unfold NAT; push_cast; exact PL.add p q
lemma NAT.mul{A B:ℝ→ℕ}(p:NAT A)(q:NAT B): NAT fun y=> A y* B y:=by unfold NAT; push_cast; exact PL.mul p q
lemma rootsBill {D U V:ℝ→ℕ}(p:NAT D)(h:NAT U)(v:NAT V): NAT fun y=> root_port (D y) (U y) (V y) :=by unfold NAT root_port; push_cast; exact ((PL.add p ((PL.const _).mul h)).add (PL.const _)).mul (PL.pow v 3)
abbrev acV(y:ℝ) := Scope.acL μ (r_F y S.scene.size) S.F.size 1 -- orientation tune
lemma ac_pat : NAT (acV S μ):=by
 unfold acV NAT Scope.acL House.upward House.rate allowD memory; push_cast; exact ((PL.const _).mul ((PL.const _).add ((PL.const _).mul ((PL.const _).mul (((PL.const _).mul ((PL.const _).add (((PL.const _).add (F_pl S.scene.size (one_pos.trans_le S.scene.target))).mul (PL.const _)))).add (PL.const _)))))).mul (PL.const _) -- tune
-- enough eventually Choose Clock's \xi cutoff threshold. NPL follows from Month.fast profile
abbrev cutξ (z:ℝ) := Gauss.Bin.stride (fun _=>1) (fun _=> 2*z) 3
lemma tailP{z:ℝ}(u:0<z): NAT (cutξ z) ∧ NPL fun y=> Primer.expL z (cutξ z y):=by
 have V:= Gauss.Month.fast (fun _=>1) (fun _=> 2*z) (PL.const 1) (PL.const _) (fun i=>by positivity)
 refine ⟨V.1,?_⟩; let f y:= Real.exp (-(2*z)/2*(cutξ z y))*1; refine NPL.by_le (f:=fun y=>Primer.expL z (cutξ z y)) (g:=f) V.2 ?_; exact Eventually.of_forall fun y=> Eq.le (by unfold f Primer.expL; ring_nf)
lemma smallMoney (ξ:ℝ→ℕ)(p:NAT ξ) : NPL (fun y=>money_θ D S y (ξ y)) :=by
 have F:=Rhythm.Lease.wearPL S; unfold money_θ wealthX baseΦ; simp_rw [div_eq_mul_inv]; exact NPL.add (((PL.mul p (PL.const _)).muln ((PL.const _).muln F)).mulp (PL.const _)) (PL.muln p ((PL.const _).muln (((PL.const _).muln F).mulp (PL.const _)))) -- tune
open Economy
lemma interior{δ:ℝ}(v:0<δ): ∀ᶠ y:ℝ in atTop, Inside S E δ (lipBill S.K.C) y:=by
 let t:S.K.C=S.K.C:=rfl; have T:= Rhythm.Lease.wearPL S; have Z:= (PL.const S.K.C).muln T; let Θ(y:ℝ):=Κξ (Rhythm.Lease.wearC S y) S.K.C; have h:NPL Θ:=(PL.const _).muln Z
 let f(y):=3*xm*Θ y; filter_upwards [T.limit.eventually (ge_mem_nhds S.K.positive),Z.limit.eventually (ge_mem_nhds S.K.admitted),((PL.const xm).muln (h.mulp (PL.const 4))).limit.eventually (ge_mem_nhds v),((PL.const (3*xm)|>.muln h).limit.eventually (gt_mem_nhds (show 0<u-E.H.yC from sub_pos.mpr E.H.y_small)))] with y hy hz H1 H2 -- positive names tune
 exact ⟨⟨Rhythm.Lease.wear_p _,hy,hz,le_rfl⟩,H1, by change f y< _ at H2; change _+f y< _; linarith⟩
-- o_Rum sums
abbrev qϕ(B n l ξ:ℝ→ℕ)(C z f h:ℝ)(y:ℝ):= House.root_port (B y) (n y+ξ y) (l y)*(2*(Primer.expL z (ξ y)*C))
lemma island{p r t:ℕ}(q e:ℝ)(B G:ℝ→ℕ){κ:ℝ→ℝ}(P:NAT B)(T:PL (fun y=>(κ y)⁻¹))(h:∀ y,0<κ y)(U:∀ y,κ y≤1): PL (fun y=>Scope.total p r (B y) (κ y)):= by exact Mapping.factor_table 4 (House.up 8) _ _ 4 (rootsBill (p:=PL.const _) (h:=PL.const _) (U:=fun _=>r) P) T h U -- tune

abbrev gas_α (b:ℝ→ℕ)(q:Pay)(y:ℝ):= Oasis.feeα b q y/12
lemma αPL {B:ℝ→ℕ}(q:Pay)(p:NAT B): PL (fun y=>(gas_α B q y)⁻¹):=by unfold gas_α; simp_rw [inv_div,div_eq_mul_inv]; exact (PL.const _).mul (Oasis.α_bill _ p) -- Tune ambiguous inv_div
lemma gas_p (b:ℝ→ℕ)(q:Pay)(y:ℝ): let T:=Oasis.feeα b q y; 0<gas_α b q y ∧ gas_α b q y ≤ 1 ∧ 3*gas_α b q y≤T/4:=by
 intro T; have he:= Oasis.ratesT b q y; dsimp only at he; unfold gas_α; unfold T; constructor <;> [skip;constructor] <;> linarith only [he.1,he.2.2.1]
end YM.CF.BProof.Start
