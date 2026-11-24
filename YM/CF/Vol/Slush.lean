import YM.CF.Vol.Celt
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vol
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Char Newt
open Push.SectorMeasure AnalyticBridge.RelativeLogdet.Ink
open Push Push.Uniform Hors Finset Laurent Bloch
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{K:Teller G}{F:Forest S.ratio}{X E B:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup B][NormedSpace ℝ B]{t x s D A C Q V r:ℝ}{i n l:ℕ}
open Tube Next.Fluctuations Work.F03 Nacre
open Next.SectorChange AnalyticBridge.GaussianFieldAlignment Oriented Rows
variable {k:S.Choices}{s': Signed}
variable (T:Tube G S)(x:ℝ)(F:Forest S.ratio)(k:S.Choices)(s: Signed)(l:ℕ)
local notation "ℿC"=> FK T x F k s l
local notation "ℿD"=> IK T x F k s l
local notation "ℿR"=> LX T x F k s l
local notation "ℿK"=> gloss T x F k
local notation "ℿZ"=> fX T x F k s l
local notation "ℿV"=> vX T F k s
local notation "ℿX"=> XX T x F k s
local notation "ℿr"=> Stores.till x
def freshB(i:Cell f)(u:Ark T F):ℝ:= KissP (ℿZ u) T i+(∑ t:Bool,(‖ℿC (i,t) u‖^2-‖ℿK (s,.inl (i,t)) u‖^2)/2)
def freshL(i:Bond c)(u:Ark T F):ℝ:= KissI (ℿZ u) (ℿV u) (choice s k) i+(‖ℿD i u‖^2-‖ℿK (s,.inr i) u‖^2)/2
def freshQ(i:Cell c)(u:Ark T F):ℝ:= -KissQ (ℿV u) T i
-- LD in true signs workD half. Keep per Bool. Assign residual back in loop.
def freshW(i:Twin c)(u:Ark T F):ℝ:= inner ℝ (ℿR i u) (ℿX i u)+ inner ℝ (DX T x F k s i u) (ℿX i u)/2
def freshY(i:Co c Gain)(u:Ark T F):ℝ:= ‖NX T x F k s i u‖^2 /2
variable {T x F k s l}
private def riseK(n:ℕ)(A:ℝ):= (1/2:ℝ)*(2^n*(A+A)*(A+A))
private lemma moon_s{f g:E→G.Color}{A t Y:ℝ}(h:∀ w, ‖w‖<t→ Jet.Allows n f w A)(p:∀ w,‖w‖<t→Jet.Allows n g w A)(hc: stance (f-g) Y)(he:g 0=0)(ht:0<t)(hn:2 ≤ n): KnotP (fun y=> (‖f y‖^2-‖g y‖^2)/2) n (Y*(A+A)) (riseK n A) t:=by
 have hh:=hc.origin; rw [Pi.sub_apply,he,sub_zero] at hh; have hπ: (f+g) 0=0:=by rw [Pi.add_apply, he,hh,add_zero];
 have hr:KnotP (fun y=>inner ℝ ((f-g) y) ((f+g) y)) n (2*Y*(A+A)) (2^n*(A+A)*(A+A)) t:= Yacht (f':= f-g) (g':=f+g) (fun y hy=> subtract_p (h _ hy) (p _ hy)) (fun y hy=> (h _ hy).add (p _ hy)) hc hπ ht hn
 rw [show (fun y=> (‖f y‖^2-‖g y‖^2)/2)=fun y=> (1/2:ℝ) • inner ℝ ((f-g) y) ((f+g) y) from funext fun y=>by simp only [Pi.sub_apply,Pi.add_apply,inner_add_right,inner_sub_left,inner_sub_right,real_inner_comm (g y),real_inner_self_eq_norm_sq,smul_eq_mul]; ring]
 have hx:=hr.scale (1/2) ht hn; rw [abs_of_pos (by norm_num : 0<(1/2:ℝ)),show 1/2*(2*Y*(A+A))=Y*(A+A) by ring] at hx; exact hx
private lemma mist {A b ε:ℝ}(h:Tabac T x F k s l n A b ε)(hn:2 ≤ n)(ht:0<ε): ∀ i,KnotP (freshB T x F k s l i) n ((A*(b+b))+(A*(b+b))) (b+(riseK n b+ riseK n b)) ε:=by
 intro i
 let J(z:Bool):=fun y:Ark T F=>(‖ℿC (i,z) y‖^2- ‖ℿK (s,.inl (i,z)) y‖^2)/2
 have hp(z:Bool): KnotP (J z) n (A*(b+b)) (riseK n b) ε:= moon_s (fun y hy=>(h.ears y hy).H (i,z)) (fun y hy=>(h.ears y hy).Y _) (h.funds.roof (i,z)) (h.J _) ht hn
 have hy: freshB T x F k s l i=(fun y=>KissP (ℿZ y) T i + (J true y + J false y)):=by ext1 y; unfold freshB; rw [Fintype.sum_bool]
 rw [hy]; exact ((knot3 (h.H i) (C:=b) (A:=0) (show 0≤(0:ℝ) from le_rfl) fun y hy=>(h.ears y hy).E i).addV ((hp true).addV (hp false) ht hn) ht hn).mono (zero_add _).le le_rfl le_rfl
private lemma dew{A b ε:ℝ}(h:Tabac T x F k s l n A b ε)(hn:2 ≤ n)(ht:0<ε): (∀ i,KnotP (freshL T x F k s l i) n (A*(b+b)) (b+riseK n b) ε) ∧∀ i, KnotP (freshQ T F k s i) n 0 b ε :=by
 constructor
 · intro i; exact ((knot3 (h.Tq i) (A:=0) le_rfl (fun y hy=>(h.ears y hy).C i)).addV (moon_s (fun y hy=>(h.ears y hy).Tq i) (fun y hy=>(h.ears y hy).Y _) (h.funds.jamb i) (h.J _) ht hn) ht hn).mono (zero_add _).le le_rfl le_rfl
 intro i; have hh:= (knot3 (h.P i) (A:=0) le_rfl (fun y hy=>(h.ears y hy).Q i)).scale (-1) ht hn; simp only [neg_one_smul,abs_neg,abs_one,mul_zero,one_mul] at hh; exact hh
lemma frost{A b ε:ℝ}(h:Tabac T x F k s l n A b ε)(hn:2 ≤ n)(ht:0<ε)(hb:0≤ b)(hA:0≤ A): (∀ i,KnotP (freshY T x F k s i) n (A*(b+b)) (riseK n b) ε) ∧∀ i,KnotP (freshW T x F k s l i) n (4*A*b) (2*(2^n*b*b)) ε:=by
 constructor
 · intro i; have hh:= h.funds.nPole i
   rw [← sub_zero (NX T x F k s i)] at hh; have he:= moon_s (fun y hy=>(h.ears y hy).N i) (g:=0) (fun y _=>Jet.allows_const y (by simpa using hb)) hh rfl ht hn; simp only [Pi.zero_apply,norm_zero,zero_pow (by norm_num : 2≠0),sub_zero] at he; exact he
 intro i; have hh:=Yacht (fun y hy=>(h.ears y hy).S i) (fun y hy=>(h.ears y hy).P i) (h.funds.letup i) (h.B i) ht hn; have hg:=(Yacht (fun y hy=>(h.ears y hy).D i) (fun y hy=>(h.ears y hy).P i) (h.funds.dPole i) (h.B i) ht hn).scale (1/2) ht hn
 rw [abs_of_pos (by norm_num : 0<(1/2:ℝ))] at hg; let L:=2^n*b*b; have hL:0 ≤ L:=mul_nonneg (mul_nonneg (by positivity) hb) hb
 simp_rw [smul_eq_mul,one_div, mul_comm (2:ℝ)⁻¹,← div_eq_mul_inv] at hg -- tune
 refine (hh.addV hg ht hn|>.mono ?_ ?_ le_rfl); nlinarith only [mul_nonneg hA hb]; change L+_ ≤ 2*L; linarith only [hL]
-- exported prices
lemma fog(K':Teller G)(p:G.Simple)(P:Patch)(h:P.Branches K'.bind G)(l n:ℕ)(hn:3 ≤ n)(W:Uniform.Before G K'.top.width K'.top.paths K'.j K'.bind (n+2)):
 ∃ A B e:ℝ,0<A∧0<B∧0<e∧∀ᶠ x in atTop,∀ {c f:Side}(S:StepData c f)(T:Tube G S)(F:Forest S.ratio), Cert P K' S T x → sizedP G P K' S T F →∀ (k:S.Choices)(s:Signed), let D:= A*(temp x)^(l+1)
 (∀ i,KnotP (freshB T x F k s l i) n D B e)∧(∀ i,KnotP (freshL T x F k s l i) n D B e)∧(∀ i,KnotP (freshQ T F k s i) n D B e) ∧(∀ i,KnotP (freshW T x F k s l i) n D B e)∧(∀ i,KnotP (freshY T x F k s i) n D B e):=by
 obtain ⟨A,b,e,hA,hb,he,h⟩:=commercial K' p P h l n hn W
 let Y:= riseK n b; let L:=2^n*b*b; have hy:0≤ Y:=by unfold Y riseK; positivity
 have hL:0≤ L:=by unfold L; positivity
 refine ⟨4*A*b,b+(Y+Y)+2*L,e,by positivity,by positivity,he,?_⟩
 filter_upwards [h, eventually_gt_atTop (0:ℝ)] with x hx hu c f S T F hr hk k s
 -- unfold notation D conflict local
 let Z:=A*temp x^(l+1); have hu:0≤ Z:=by unfold Z; have := Work.E09.temp_pos hu; positivity
 intro Cost; have hy':2 ≤ n:=by omega
 have hX:= hx S T F hr hk k s
 obtain ⟨h1,h2⟩:= dew hX hy' he; obtain ⟨h3,h4⟩:= frost hX hy' he hb.le hu
 have he: Z*(b+b)+ Z*(b+b)=Cost:=by unfold Z Cost; ring
 have ht: 4* Z*b=Cost:=by unfold Z Cost; ring
 have hv: Z*(b+b)≤ Cost:=by rw [←he]; linarith only [mul_nonneg hu hb.le]
 exact ⟨fun i=>(mist hX hy' (show 0<e by assumption) i).mono he.le (le_add_of_nonneg_right (by positivity)) le_rfl,fun i=>(h1 i).mono hv (by change b+Y ≤ _; linarith) le_rfl,fun i=>(h2 i).mono ((by positivity : 0 ≤ Z*(b+b)).trans hv) (by linarith only [hy,hL]) le_rfl,fun i=>(h4 i).mono ht.le (le_add_of_nonneg_left (by positivity)) le_rfl,fun i=>(h3 i).mono hv (by linarith only [hy,hL,hb]) le_rfl⟩
end YM.CF.Vol
