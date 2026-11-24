import Merino.Corolla.Curtain
import YM.SU5.Exchange.Pace.Moon

set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 360000
noncomputable section
namespace YM.CF.Merino.Corolla
open Finset Lattice RG Scree Skye Vow
open scoped Topology Classical Matrix Matrix.Norms.L2Operator
open Cadre Sour Push.AbsoluteSums.Trees Vow.TreasuryFog

open Pressure
open BPress (lscale PL NPL)
open Filter Py Roots
variable {F:ℝ→ℝ}
private lemma nabs(u:NPL F):NPL (fun x=>|F x|):= u.mono (by simp)
private lemma cheap(u:NPL F)(k:ℕ):∀ᶠ x in atTop, lscale x ^ k * F x ≤ 1:=
  (u.vanish k).eventually (ge_mem_nhds one_pos)
private lemma pl_visit (m:ℕ): PL fun x=> visits m (radiusB x) :=by
 have h:PL (fun x:ℝ=>(ringSize (radiusB x):ℝ)):= by
   simp only [ringSize,Nat.cast_mul, Nat.cast_ofNat]
   exact ((PL.const _).mul PL_radiusX).mul PL_radiusX
 simp only [visits,pearl,Nat.cast_pow,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
 simp only [ringSize,Nat.cast_mul] at h; exact ((((h.add h).add (PL.const _)).pow _).mul (PL.const _)).mul (PL.const _)
private lemma vp (m b:ℕ): 0≤visits m b:=by
 unfold visits
 refine mul_nonneg (Nat.cast_nonneg _) (tsum_nonneg fun i=>?_)
 unfold Next.Scheduling.decay; positivity

open Rive

private def sip (p o k:ℕ):ℝ := Nor.reserveT p o k (k:ℝ)⁻¹
private lemma sip_pos(p o k:ℕ):0 ≤ sip p o k:=by
 unfold sip Nor.reserveT Nor.coin_n Nor.stilK
 positivity
private lemma pl_sip(p o:ℕ):PL fun x=>sip p o (radiusB x):=by
 have r:=PL_radiusX
 have h:=((PL.const 5).mul (r.add (PL.const 1))).pow p
 have i: PL (fun x=> Real.exp (radiusB x:ℝ)⁻¹) := by
    apply (PL.const (Real.exp 1)).mono
    filter_upwards [BPress.lscale_late.eventually_ge_atTop 2] with x hx
    rw [abs_of_pos (Real.exp_pos _),abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (inv_le_one_of_one_le₀ (by unfold lscale at hx; linarith only [hx]))
 simp only [sip,Nor.reserveT,Nor.coin_n,Nor.stilK,inv_inv]
 exact (h.mul ((PL.const _).mul (((PL.const 2).mul h).pow _))).mul (((r.pow _).mul (PL.const _)).mul i)


private lemma budget {P:BudgetPoint}{L k m:ℕ}{h f d v Q z l:ℝ}(hx:Girdle P h (accent L*f) (accent L*(d*Q)) v (z*Q) m)
 (hb:18*m≤P.B)(hxq:0≤Q)(hl:1≤l)
 (ht:l^k*(nectar P*accent L*d) ≤1)
 (hv:l^k*(nectar P*z*2) ≤1)
 (hw:l^k*(Real.exp (2*m)*(nectar P*(z*200))) ≤ 1):
   Tuning P L h f (d*Q) v (z*Q) (Q/l^k) m :=by
  have hh:0<l^k:=by positivity
  have win(a:ℝ)(e:l^k*a ≤1):a*Q ≤ Q/l^k:=(le_div_iff₀ hh).mpr <| by
    rw [mul_right_comm,mul_comm a]
    exact mul_le_of_le_one_left hxq e
  refine ⟨hx,by exact_mod_cast hb,by rw [←mul_assoc,←mul_assoc]; exact win _ ht,by positivity,?_,?_⟩
  · set y:=sigma ((P.B:ℝ)⁻¹+(P.B:ℝ)⁻¹) P.B
    have hy:y≤1:=by
       unfold y sigma
       apply Real.exp_le_one_iff.mpr
       exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (by positivity)) (by norm_num)
    set t:=hx.toThimble
    set s:=(1-degreePrice P.B (z*Q) (P.B:ℝ)⁻¹)⁻¹


    have hs:=hush t
    have hh:0≤nectar P:=sip_pos ..
    refine le_trans ?_ (win _ hv)
    change y*(nectar P*(z*Q*s)) ≤ nectar P*z*2*Q
    rw [mul_left_comm, show nectar P*z*2*Q=nectar P*(2*(z*Q)) from by ring, mul_comm (z*Q) s,←mul_assoc y]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
       ((mul_le_of_le_one_left (le_of_lt <|inv_pos.mpr hs.2.1) hy).trans hs.1) t.grant.le) hh
  · refine le_trans ?_ (win _ hw)
    change Real.exp (2*(m:ℝ))*(nectar P*((1:ℝ)⁻¹*(z*Q*200))) ≤ _; norm_num; apply le_of_eq; ring


abbrev cur (R:Side)(k:ℕ)(x:ℝ):ℝ:=pinpr R x/lscale x^k
/-- Generic bids including pressure-slack powers. -/
theorem seasons (p o L k m:ℕ)(R:Side)(h:ℝ)(hh:1≤h)
 {D V:ℝ→ℝ}(w:NPL F)(u:NPL D)(r:NPL fun x=>V x/pinpr R x):
 ∀ᶠ x in atTop,∃ g,∀ P:BudgetPoint, P.B=radiusB x→P.supportExponent=1→P.power=p→P.order=o→
   Tuning P L h |F x| (|D x| *pinpr R x) (V x) g (cur R k x) m :=by
 let Q:=pinpr R; let A:=accent L; let b(x:ℝ):ℝ:=radiusB x; let T (x:ℝ):=visits m (radiusB x)
 let C:=chi_f o
 have hA:0 ≤ A:=(Real.exp_pos _).le
 have hQ:=nq R
 let J:=sip p o; let hr(x):=4*b x*T x*A
 let G (x):=hr x*|D x| + |C*(V x/Q x)|+Q x
 have t:=pl_visit m
 have y:=PL_radiusX
 have hG:NPL G:=by
    have hu:PL hr:=(((PL.const 4).mul y).mul t).mul (PL.const _)
    exact ((hu.times (nabs u)).add (nabs (r.const_mul _))).add hQ
 have c1:= cheap (((pl_sip p o).mul (PL.const A)).times (nabs u)) k
 have c2:= cheap (((pl_sip p o).times hG).mul (PL.const 2)) k


 have c3:= cheap (((pl_sip p o).times (hG.mul (PL.const 200))).const_mul (Real.exp (2*(m:ℝ)))) k
 have c4:= ( (( ((hG.mul hQ.pl).const_mul 800).mul PL_spanV).mul y).drop).eventually (ge_mem_nhds (show (0:ℝ)<1 by simp))
 have c5:= ((((t.times ((nabs w).const_mul A)).mul y).mul ((PL.const 4).mul PL_spanV)).mul y).drop.eventually (ge_mem_nhds (show (0:ℝ)<1 by simp))
 filter_upwards [Next.Scheduling.Clock.counting.eventually_ge_atTop (10 + 18*m),draft_π R,c1,c2,c3,c4,c5] with x B e c1 c2 c3 c4 c5
 have hq:0<Q x :=pow_pos e.2.1 _
 refine ⟨G x*Q x,?_⟩
 rintro P E Ep rfl rfl
 suffices H:Girdle P h (accent L*|F x|) (accent L*(|D x| *Q x)) (V x) (G x*Q x) m by
   refine budget H (by rw[E]; exact le_trans le_add_self B) hq.le (BPress.lscale_one x)
      (by simp only [nectar,E]; exact c1) (by simp only [nectar,E]; exact c2)
      (by simp only [nectar,E]; exact c3)
 change 10+18*m≤radiusB x at B
 have ha:0 ≤ hr x:=mul_nonneg (mul_nonneg (by unfold b; positivity) (vp ..)) hA


 let Vpart:= C*(V x/Q x)
 have hp:0<G x:= add_pos_of_nonneg_of_pos (add_nonneg (mul_nonneg ha (abs_nonneg _)) (abs_nonneg _)) hq
 have hg:0 < G x*Q x:=by positivity
 have be:10 ≤ b x:=by unfold b; norm_cast; omega
 have h:0 < (radiusB x:ℝ):=by linarith only [be]
 refine ⟨⟨le_of_eq Ep,hg,?_⟩,hh,by omega,?_,?_,?_,?_,mul_nonneg hA (abs_nonneg _),
         mul_nonneg hA (by positivity)⟩
 · rw [E,inv_eq_one_div,le_div_iff₀ h]
   linarith only [show 800*(G x*Q x)*spanV (radiusB x)*(radiusB x:ℝ)≤1 from c4]
 · rw [lapel,E,Ep]; linarith only [show 5/(radiusB x:ℝ) ≤ 1/2 from (div_le_iff₀ h).mpr (by linarith only [be])]


 · have hc: Vpart*Q x= chi_f P.order*V x:=by unfold Vpart C; field_simp
   rw [←hc]; apply mul_lt_mul_of_pos_right _ hq
   have:0≤ hr x*|D x|:=by positivity
   exact lt_of_le_of_lt (le_abs_self _) ((le_add_of_nonneg_left this).trans_lt (lt_add_of_pos_right _ hq))
 · rw [E,zpay,inv_eq_one_div, mul_one_div,le_div_iff₀ h]; -- tune


   have hv:= (puck P).2.2; rw [E] at hv
   rw [le_div_iff₀ (by positivity), le_div_iff₀ h]
   unfold A at c5; linarith only [c5]
 · rw [E,bpay]
   have hvV:hr x*|D x| ≤ G x:= (le_add_of_nonneg_right (abs_nonneg _)).trans (le_add_of_nonneg_right hq.le)
   rw [le_div_iff₀ (by norm_num : (0:ℝ)<4), mul_comm _ (G x * Q x),←div_eq_mul_inv,le_div_iff₀ h]
   have hv:=mul_le_mul_of_nonneg_right hvV hq.le
   unfold hr T b A at hv
   linarith only [hv]
end YM.CF.Merino.Corolla

