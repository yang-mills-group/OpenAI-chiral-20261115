import GaugeFieldConstruction.Tiptop
import GaugeFieldConstruction.Elea
import YM.SU5.Regis.Archive

/-! # Pay gauge rent under localized aggregate mark perturbation. Adapt Inlets & Danube,
     determinant of unperturbed already licensed. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 50000
noncomputable section
namespace YM.Gleam
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix Module Regis
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ:ℝ}{U:Config G n}{A:Support c}{o x z:Site n}{f m:ℕ} {X:T.Slice G}{Y:LinkArray G (Blip T (univ : Finset T.Free))} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}{J:ChartRatio G}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L:Floor H q n δ w)(D:LocalRatio J)

namespace clocks
open Work.E09 AnalyticBridge.Annulus1AD
open CF.BProof (coin coin_scale coin_mul coin_pow scaleY)
open CF.BProof.PricePort
abbrev gratuity:ℝ:= 1/10000
abbrev callE:ℝ:=gratuity/4
abbrev tileN:= Rrp gratuity
abbrev Marked (x:ℝ)(w:Side)(L:Side) := tileN x ≤ w.val ∧ (w.val:ℝ) ≤ 2*L.val*tileN x
-- precise P2 gauge phase definition
abbrev badgeDust (x:ℝ):= Rrp (6*gratuity) x*temp x
abbrev suitCost (L:Side)(x:ℝ) := (8*(2*L.val*tileN x)+1)*(4*badgeDust x*(1+2*L.val*tileN x))
lemma suit_sizing (L:Side) {x:ℝ}(p:0<x){W:Side}(m:Marked x W L) : suitedFee W.val (badgeDust x)≤ suitCost L x:=by
 have ht:=temp_pos p; have he:0< Rrp (6*gratuity) x:=CF.BProof.coin_pos ..; unfold suitedFee suitCost; have hw:0<badgeDust x:=mul_pos he ht; have hv:=m.2; have ho:0 ≤ tileN x:=(CF.BProof.coin_pos ..).le; gcongr
lemma tile_bill (L:Side) : RunRate (8*gratuity-1/2) 1 (suitCost L):=by
 have h:= RunRate.coins gratuity 0 0
 have he : RunRate (6*gratuity + -(1/2)) (0+1) badgeDust:= (RunRate.coins ..).mul RunRate.temps
 have hh : RunRate gratuity 0 (fun x:ℝ=>2*L.val*tileN x):= h.cmul _
 have hf := (RunRate.const (1:ℝ)).relax (u':=0) (H:=show 0 < gratuity by unfold gratuity; norm_num)
 exact (by convert ((hh.cmul 8).add hf).mul ((he.cmul (4:ℝ)).mul (hf.add hh)) using 1 <;> ring)
abbrev hairFee (x:ℝ) := Rrp (-(1/4)) x
lemma hair_proc (L:Side)(R:Rules G)(J:ChartRatio G)(D:LocalRatio J): ∀ᶠ x in atTop, suitCost L x ≤ R.c ∧ 2*suitCost L x<J.radius∧(∀ u:G.Color, ‖u‖≤2*suitCost L x → J.J u ≤ Real.exp (hairFee x)):=by
 obtain ⟨c,hc,h⟩:= ((D.germ 0 (mem_ball_self D.patch)).differentiableAt (by simp)).hasFDerivAt.isBigO_sub.exists_pos
 obtain ⟨r,hr,H⟩:= Metric.nhds_basis_closedBall.eventually_iff.1 h.bound
 let V:=suitCost L
 have hp : Tendsto V atTop (𝓝 0):= (tile_bill L).tends (by unfold gratuity; norm_num)
 have ht : Tendsto (fun x=> 2*V x) atTop (𝓝 0):=by simpa only [mul_zero] using hp.const_mul (2:ℝ)
 filter_upwards [hp.eventually (ge_mem_nhds R.radius),ht.eventually (gt_mem_nhds D.patch), ht.eventually (ge_mem_nhds hr),logPrice _ _ (((tile_bill L).cmul 2).cmul c) (c:=-(1/4)) (d:=0) (w:=0) (by unfold gratuity; norm_num) one_pos] with x v i u z
 refine ⟨v,i,fun y t=>?_⟩
 have ht:|J.J y-1|≤ c*‖y‖:= by simpa [Real.norm_eq_abs,D.anchored] using H (show y∈closedBall (0:G.Color) r from mem_closedBall_zero_iff.mpr (t.trans u))
 have hu:= le_abs_self (J.J y-1); change c*(2*suitCost L x) ≤ 1*hairFee x at z
 linarith only [hu,ht,z,mul_le_mul_of_nonneg_left t hc.le,Real.add_one_le_exp (hairFee x)]
lemma badge_ok : ∀ᶠ x:ℝ in atTop, temp x ≤ badgeDust x:=by
 filter_upwards [(Rrp_high (a:=6*gratuity) (by norm_num [gratuity])).eventually_ge_atTop 1,eventually_gt_atTop (0:ℝ)] with x h t; exact le_mul_of_one_le_left (temp_pos t).le h
abbrev tauTicket (q:Clip)(β x:ℝ):= β*q.linear*temp x^2 -- exempt /10 and reserve /4 + query /100 in uses
abbrev boldTicket (q:Clip)(β x:ℝ):= β*q.linear* temp x * badgeDust x
lemma boat (L:Side)(q:Clip)(R:Rules G)(J:ChartRatio G)(D:LocalRatio J) :
 ∀ᶠ x:ℝ in atTop, ∀ w:Side, Marked x w L → ∀ β:ℝ,0≤β → ∀ p:BudgetPoint,p.threshold=temp x→ ∀ κ k:ℝ,κ ≤ tauTicket q β x/8 → k ≤ boldTicket q β x/8 →
    TopPrice J R q p w.val (height x) β κ k (tauTicket q β x/4) (boldTicket q β x/4) (suitCost L x) (hairFee x) (badgeDust x):=by
 filter_upwards [eventually_gt_atTop 0,badge_ok,hair_proc L R J D,parliament (G:=G) q] with x h qA s t W m β l p hp κ k u v
 have ht₀:0 ≤ tauTicket q β x:=by unfold tauTicket; have ht:=q.tail_pos; positivity
 have ht:0 ≤ boldTicket q β x:=by unfold boldTicket; have ht:=q.tail_pos; have he:=temp_pos h; have hv:0<badgeDust x:=he.trans_le qA; positivity
 refine ⟨hp.symm ▸ qA,t _ hp,suit_sizing L h m,s.1,s.2.1,s.2.2,?_,?_,(CF.BProof.coin_pos ..).le⟩
 · rw [hp]; unfold tauTicket at *; linarith only [ht₀,u]
 rw [hp]; unfold boldTicket at *; linarith only [ht,v]
lemma heightT : RunRate 0 0 (fun x=> (height x:ℝ)):= ceiling_b (CF.BProof.PL.log_y.pow 2) (Eventually.of_forall fun x=>sq_nonneg _)
lemma hallC (x:ℝ): hallBill (height x)=2* height x+8:=by unfold hallBill Sequest; omega
lemma hallT : RunRate 0 0 (fun x=> (hallBill (height x):ℝ)):= by
 simp_rw [hallC]; simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]; exact (heightT.cmul _).add (RunRate.const _)
local notation "Yrate" f:max => RunRate 0 0 f
lemma wall_matures (L:Side):∀ᶠ x in atTop,∀ W:Side,Marked x W L → hallBill (height x) ≤ W.val/2:=by
 filter_upwards [logPrice _ _ (hallT.cmul 2) (c:=gratuity) (d:=0) (w:=0) (by norm_num [gratuity]) one_pos] with x h w m
 have he: 2*(hallBill (height x):ℝ) ≤ w.val:= h.trans ((one_mul (tileN x)).le.trans m.1)
 have ht:2*hallBill (height x)≤ w.val:=by exact_mod_cast he
 omega
-- Taylor bill over all data, proof via grade alone
include G in
lemma trailFees (e:0<η) : RunRate (-(1:ℝ)) 0 (fun x:ℝ=>trail η (height x)):=by
 refine ⟨0,?_⟩; filter_upwards [tail_gone (G:=G) η e,eventually_gt_atTop 0] with x h t -- SU import? G include
 rw [abs_of_pos (show 0<trail η _ from Real.exp_pos _),show coin x (-1) 0 0=x⁻¹ from ?_]; · exact h
 refine (Rrp_out (-1) x t).trans ?_; rw [Real.rpow_neg t.le,Real.rpow_one]
lemma taylor_bill (q:Clip)(L:Side)(R:Rules G)(p:0<η)(C:ℝ) : RunRate (-(1/4)) 0 (fun x:ℝ=> x*Δ₁ R q (suitCost L x) (height x) η C):=by
 let X:=fun x:ℝ=>Δ₁ R q (suitCost L x) (height x) η C
 let V:=suitCost L; let v:ℝ:=8*gratuity-1/2
 have h: RunRate v 1 V:=tile_bill L
 have hp:RunRate (-5/4) 0 X:=by
    have he(y:ℝ)(f:ℝ→ℝ)(q':ℝ)(w:RunRate y q' f)(t:y ≤ v+v+v): RunRate (-5/4) 0 f:= w.relax (lt_of_le_of_lt t (by unfold v gratuity; norm_num))
    let D':= fun x=> faceCutError R (V x)
    have hd : RunRate (v+v) (1+1) D':=by unfold D' faceCutError; convert (h.pow 2).cmul _ using 1 <;> push_cast <;> ring
    let Z:=fun x=> slotError R (height x) (V x)
    have hz: RunRate (v+v) (1+1) Z:= by
       apply hd.add; convert ((heightT.cmul (8*G.colorScale)).mul (h.pow 2)) using 1 <;> push_cast <;> ring
    let F:=fun x:ℝ=> trail η (height x);
    have ht: RunRate (-1) 0 F:=trailFees (G:=G) p
    let E:= fun x=> acry R (V x) (height x) η C
    have hw: RunRate (v+v) (1+1) E:=by
       apply (RunRate.cmul (RunRate.add hz ?_))
       exact (((RunRate.const 2).add (((h.cmul 2).cmul 4).relax (u':=0) (by unfold v gratuity; norm_num))).mul ht).relax (by unfold v gratuity; norm_num)
    exact (((he _ _ _ (((hd.mul ((h.cmul 2).cmul 4))).cmul q.direct) le_rfl).add (he _ _ _ (hw.mul (((h.cmul 2).cmul 4).cmul C)) le_rfl)).add (he _ _ _ (((((h.cmul 2).cmul 4).mul ht|>.cmul C).pow 2).divc 2) (by unfold v gratuity; norm_num)))
 convert RunRate.xm.mul hp using 1 <;> norm_num <;> ring
lemma tax_V (L:Side)(q:Clip)(R:Rules G) (p:0<η)(w:0≤ C)(S:ℝ) : ∀ᶠ x:ℝ in atTop,∀ β:ℝ,β ≤ 2*x → ∀ p':BudgetPoint,p'.threshold=temp x → ∀ n:Side,taxΔ R q n p' β (suitCost L x) η C S (height x) ≤ Rrp (-1/5) x*(Fintype.card (Site n):ℝ):=by
 let T:= YM.Pressure.temp; let V:= suitCost L
 let Y(x:ℝ):=2*x*(C*T x^3+C*T x^4)+ S*T x^2+ (Fintype.card PlaqAxes:ℝ)*(2*(x*Δ₁ R q (V x) (height x) η C))
 have he:=RunRate.temps
 have hy: RunRate (-(1/4)) 0 Y:=by
    unfold Y T; apply RunRate.add _ (((taylor_bill q L R p C).cmul 2).cmul (Fintype.card PlaqAxes:ℝ)); exact (( (RunRate.xm.cmul 2).mul (((he.pow 3).cmul C).add (((he.pow 4).cmul C).relax (by norm_num))) ).relax (by norm_num)|>.add (((he.pow 2).cmul S).relax (by norm_num)))
 filter_upwards [logPrice _ _ hy (c:= -1/5) (w:=0) (d:=0) (by norm_num) one_pos,badge_ok,eventually_gt_atTop 0] with x t u m β b p' i n
 let N:ℝ:= Fintype.card (Site n); have hg:= temp_pos m; have hs: 0 ≤ V x:=by
    have he':0 < badgeDust x:=hg.trans_le u; have h:= CF.BProof.coin_pos x gratuity 0 0; unfold V suitCost tileN Rrp; positivity
 have hf: 0 ≤ Δ₁ R q (V x) (height x) η C:= Δ_pos hs w
 apply le_trans _ (mul_le_mul_of_nonneg_right (show Y x ≤ Rrp (-1/5) x by simpa only [one_mul] using t) (show 0≤ N from Nat.cast_nonneg _))
 unfold Y T V N taxΔ CF.Graph.taxY; rw [show Fintype.card (Cell n)= Fintype.card (Site n)*Fintype.card PlaqAxes from Fintype.card_prod .., Nat.cast_mul, site_card,i]; push_cast
 unfold V at hf; nlinarith only [mul_le_mul_of_nonneg_right b (show 0 ≤ (n.val:ℝ)^4*(C*temp x^3+C*temp x^4) by positivity),mul_le_mul_of_nonneg_right b (show 0 ≤ (n.val:ℝ)^4*(Fintype.card PlaqAxes:ℝ)* _ from mul_nonneg (by positivity) hf)]
end clocks
end YM.Gleam
end
