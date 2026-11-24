import GaugeFieldConstruction.Tarp
import GaugeFieldConstruction.Narrows
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 25000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.Gleam
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix Module Regis
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ:ℝ}{U:Config G n}{A:Support c}
namespace Guide
open CF.BProof (coin coin_scale coin_mul coin_pow scaleY)
open CF.BProof.PricePort clocks
-- soft against smaller calls. compact.
variable {a b c₀ d:ℝ}{F:ℝ→ℝ}
lemma RunLoose (q:Clip)(L:Side)(X:ℝ→ℝ)(p:RunRate a b X)(e:a<0)(hv:∀ᶠ x:ℝ in atTop,0≤ X x) (ε₁ ε₂:ℝ)(h1:0<ε₁)(h2:0<ε₂): ∀ᶠ x in atTop, ∀ {n c:Side}(β:ℝ), x/2≤β→∀ R:Ratio c n,Odd R.count.val → Marked x R.count L →∀ Wa Da:Flaws n, X x* (wallTax (grid_break R Da) Wa R (hallBill (clocks.height x)):ℝ) ≤ saveZ x*Fintype.card (Site n) + ε₁*tauTicket q β x * Wa.card + ε₂*boldTicket q β x*Da.card:=by
 -- use Fringe even at coefficient one. |Wa| expansion counts etc.
 let Y(x:ℝ):=(2* (hallBill (clocks.height x):ℝ)+1)^4; let Z(x:ℝ):=(21:ℝ)^4*((2*(L.val:ℝ)*tileN x))^4
 have he: RunRate 0 0 Y:=by unfold Y; convert (((hallT.cmul 2).add (RunRate.const 1)).pow 4) using 1 <;> ring
 have hg: RunRate (4*gratuity) 0 Z:=by unfold Z; convert ((((RunRate.coins gratuity 0 0).cmul (2*(L.val:ℝ))).pow 4).cmul (21^4:ℝ)) using 1 <;> push_cast <;> ring
 let v:=q.linear; have hv:0<v:=q.tail_pos
 filter_upwards [logPrice _ _ he (w:=0) (d:=2) (c:=0) (by norm_num) (show 0<ε₁*v/2 by positivity),logPrice _ _ hg (w:=0) (d:=2) (c:=6*gratuity) (by norm_num [gratuity]) (show 0<ε₂*v/2 by positivity), (p.tends (Or.inl e)).eventually (ge_mem_nhds zero_lt_one), wall_matures L,eventually_gt_atTop 0,logPrice _ _ (hallT.cmul 8) (w:=0) (d:=0) (c:= -gratuity/2+gratuity) (by norm_num [gratuity]) one_pos] with x A B H s E t n c β l R b Q Wa Da
 let w:= R.count.val; let d:=hallBill (clocks.height x); let m:= (w:ℝ); let P:ℝ:=Fintype.card (Site c); let V:ℝ:=Fintype.card (Site n)
 have hP:V=P*m^4:=by unfold V P m w; rw [site_card,site_card,R.exact_size]; push_cast; ring
 apply le_trans (mul_le_of_le_one_left (Nat.cast_nonneg _) (show X x≤1 from H)); unfold wallTax;
 have hz:(rimTax (grid_break R Da) R d:ℝ) ≤ saveZ x*V:=by
    unfold rimTax; rw [Nat.cast_mul]; apply (mul_le_mul_of_nonneg_left (wall_cheap b (s _ Q)) (Nat.cast_nonneg _)).trans
    have ht : 8*(d:ℝ) ≤ saveZ x*m:=by
       apply le_trans (b:=saveZ x*tileN x) (by unfold saveZ tileN Rrp; rw [coin_mul, zero_add]; simpa only [one_mul] using t) (mul_le_mul_of_nonneg_left Q.1 (CF.BProof.coin_pos ..).le)
    rw [hP]; change P*(8*(d:ℝ)*m^3) ≤ _; linarith only [mul_le_mul_of_nonneg_left ht (show 0≤P*m^3 from mul_nonneg (Nat.cast_nonneg _) (by unfold m; positivity))]
 let K':= ε₁*tauTicket q β x; let T':= ε₂*boldTicket q β x
 have hf: ((↑(grid_break R Da).card:ℝ)*m^4) ≤ T' * Da.card:=by
    have hx : ((grid_break R Da).card:ℝ) ≤ (Da.card:ℝ)*21^4:=by
       exact_mod_cast ((Corona.halo_size ..).trans (Nat.mul_le_mul_right _ Finset.card_image_le): (grid_break R Da).card ≤ Da.card*21^4) -- tune
    apply (mul_le_mul hx (pow_le_pow_left₀ (show 0≤ m from Nat.cast_nonneg _) Q.2 4) (pow_nonneg (show 0≤ m from Nat.cast_nonneg _) _) (by positivity)).trans
    have hp: Z x ≤ T':= B.trans (by unfold T' v; linarith only [mul_le_mul_of_nonneg_left (boldTrade q _ E l) h2.le])
    unfold Z at hp; linarith only [mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg (α:=ℝ) Da.card)]
 have hL: Y x ≤ K':= A.trans (by unfold K' v; linarith only [mul_le_mul_of_nonneg_left (tauTrade q _ E l) h1.le]);
 push_cast
 unfold rimTax at hz; rw [Nat.cast_mul] at hz; change ↑(Fintype.card (Site c)) * ↑(largerBill (R.count.val) d)+ ↑(#(grid_break R Da))* m^4 +Wa.card * Y x ≤ saveZ x * V + K' * Wa.card+T'* Da.card
 linarith only [hz,hf,mul_le_mul_of_nonneg_right hL (Nat.cast_nonneg (α:=ℝ) Wa.card)]

abbrev KeyTurn (x:ℝ) := Rrp (-callE/2) x -- =z
abbrev ClockTurn (x:ℝ) := Rrp (-callE/16) x -- =X^{-e*/16}
abbrev BeatTurn (x:ℝ):= Rrp (-callE/8) x
open CF.Fock.Flux
-- profile of L normalized by v,P; Gaussian cap sup up to W'. 
variable {F K V:ℝ→ℝ} {g h k:ℝ}
def planR (g K V F:ℝ→ℝ)(D u:ℝ)(m:ℕ)(x:ℝ) := let z:=KeyTurn x; let r:=BeatTurn x; let d:=hairFee x
    Tor r D u z (K x) m 1+2*(Crest (V x) (K x) z u m)^2 + (z*(d+d)+trend*(z*(F x))^2)+(10* saveZ x * g x) -- g x includes P_*^I for small incidence;
lemma sailR (p:RunRate 0 k F)(s:RunRate 0 g K)(b:RunRate 0 h V)(E:ℝ→ℝ)(r:RunRate 0 t E)(D u:ℝ)(m:ℕ):
    ∀ᶠ x in atTop,Crest (V x) (K x) (KeyTurn x) u m ≤1/2 ∧ planR E K V F D u m x ≤ KeyTurn x * ClockTurn x:=by
 let z:= -callE/2; let w:= ClockTurn; let e:= -callE/8; let k':= m; let X:=KeyTurn; have hz:RunRate z 0 X:=RunRate.coins ..; have he:RunRate e 0 BeatTurn:=RunRate.coins ..
 let c:= max h g; have ht: RunRate z (0+c) (fun x=>Crest (V x) (K x) (X x) u m):=by simpa only [c,add_zero] using hz.mul (((s.muc (u^m)).weaker (Or.inr ⟨rfl,le_max_right h g⟩)).add (b.weaker (Or.inr ⟨rfl,le_max_left h g⟩)))
 let d':= -callE/16; let f:= z+d'-callE/32
 have hp: RunRate f 0 (planR E K V F D u m):=by
    unfold planR
    have hv:RunRate f 0 (fun x=>Tor (BeatTurn x) D u (X x) (K x) m 1):=by
       unfold Tor
       have hw:RunRate f 0 (fun x=> X x*K x * (2*m*u^m*(D*BeatTurn x))):= ((hz.mul s).mul ((he.cmul D).cmul (2*m*u^m))).relax (by unfold f z d' e callE gratuity; norm_num)
       have hp:RunRate (-e) 0 (fun x=>2*(D/BeatTurn x)):= by
          simp_rw [div_eq_mul_inv, BeatTurn,Rrp,CF.BProof.coin_inv]; simp only [neg_zero]; exact (((RunRate.coins (-e) 0 0).cmul D).cmul 2)
       refine RunRate.muc (hw.add ?_) _; exact (((((hz.mul hp).mul s).muc (predrawn u m)).pow 2)).relax (by unfold f z d' e callE gratuity; norm_num)
    let W:= hairFee
    have hh:RunRate (-(1/4)) 0 W:=RunRate.coins ..
    exact (((hv.add (((ht.pow 2).cmul 2).relax (by unfold f z d' callE gratuity; norm_num))).add (((hz.mul (hh.add hh)).relax (by unfold f z d' callE gratuity; norm_num)).add ((((hz.mul p).pow 2).cmul trend).relax (by unfold f z d' callE gratuity; norm_num)))).add ((((RunRate.coins (-gratuity/2) 0 0).cmul 10).mul r).relax (by unfold f z d' callE gratuity; norm_num)))
 filter_upwards [(ht.tends (Or.inl (by unfold z callE gratuity; norm_num))).eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1/2)),logPrice _ _ hp (w:=0) (d:=0) (c:=z+d') (by unfold f; norm_num [gratuity,callE]) one_pos] with x h u'
 refine ⟨h,?_⟩; unfold KeyTurn ClockTurn Rrp; rw [coin_mul, zero_add]; exact u'.trans_eq (one_mul _)
end Guide
end YM.Gleam
end
