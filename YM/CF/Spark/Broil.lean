import YM.CF.Spark.Fever
import YM.CF.Mint.Hit
set_option autoImplicit false
noncomputable section
namespace YM.CF.Spark
open Function Filter Metric Finset NormedSpace Lattice Laurent Lat Tulip Rush Cube Tenant Mir Mir.Trip Phase Phase.Sample Branch MeasureTheory RG Wilson WilsonStartup RP Nova Kea Ave Fock SU CF.Jet Broc Petal Spire Scroll Peaks Pastry Pic Sods Paige Vault Graph Dial Brace Mint Bloch Fir Ember Onyx Emu
open scoped Topology BigOperators Matrix MatrixOrder ContDiff InnerProductSpace Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {L B m N: Side}{e H a b c d v σ h Y w r l t τ C S β:ℝ}{i j k n:ℕ}{O:Odd L.val}{T:Pricing j L O (Thread j)}{P:Grasp T B e}{V:Pearl P}{f:ℕ→Side}(F: Pic.Span V H b v c a r n)(R:Reg 0 e B)
local notation "n'"=>Domain m B
local notation "U'"=>Briar m B e
local notation "E'"=>Elf m B
local notation "M'"=>CSide m B
abbrev BagX(m B:Side)(e:ℝ):=Acres m→ Briar m B e→Ewe m B
def lure(K:BagX m B e)(x:U'):= amen R K P (scarf m) x-amen R K P (scarf m) (pole m B F.eP.le slate)
def shore (K:BagX m B e):= Complex.exp (-amen R K P (scarf m) (pole m B F.eP.le slate))
structure Corner (m:Side)(K:BagX m B e)(h d L τ v:ℝ):Prop where
 well: exists w,Effect (by rfl : (1:ℝ) ≤ 1) m B e 0 R (scarf m) h d K w P.baseY -- tune
 hall: CoolR F m τ v
 limit :(∀ (T:Briar m B e), (T.val∈ Calm group (Domain m B) v)→ ‖lure F R K T‖ ≤ L) -- positivity
variable (Z:Vial P R l Y h C d)
include Z
lemma shaft (g:Tendsto (bean f) atTop atTop)(hl:0<h):∃ (K:∀ i:ℕ,BagX (f i) B e) (A τ W:ℕ→ℝ), Aqua (bean f) A ∧ Aqua (bean f) τ ∧ ∀ᶠ i in atTop,Corner F R (f i) (K i) h d (A i) (τ i) (W i) ∧0<W i:=by
 obtain ⟨c,w,hc,h',Y'⟩:= cycle V F.stmt F.eP F.p 0 1 le_rfl; obtain ⟨N,g'⟩:= Z.valid.bond.well 1 le_rfl
 let H(i:ℕ):=Real.exp (-1*bean f i); let L'(i):=lid (f i) B h c (R.time (scarf (f i))) w Y
 let M(i)(x:BagX (f i) B e × ℝ × ℝ):Prop:= Corner F R (f i) x.1 h d (H i+L' i) x.2.1 x.2.2 ∧ 0<x.2.2∧x.2.1 ≤ H i
 have hx: ∀ᶠ i in atTop,∃ x,M i x:=by
    filter_upwards [ar_p (B:=B) g (4+n+N)] with i u; obtain ⟨hp,hv⟩:=u; let m:=f i; have he:n ≤ (CSide m B).val:=by change n ≤ _; unfold m; omega
    have ht:= (F.plan _ he).1; obtain ⟨K,w₀,v⟩:= g' (scarf (f i)) (show N≤_ from (le_trans (by omega : N≤(f i).val) (le_self_pow₀ (f i).property (by norm_num:9≠0)))) (f i)
    have hy:= (star_h F.eP.le R K (Y' _ ht firstM) hc hl Z.valid.bond v (by omega)); let Q:=amen R K P (scarf (f i)); have hH:0<H i:=Real.exp_pos _; obtain ⟨L,hL,X⟩:= throb Q hy.1 (H i) hH
    obtain ⟨x,u,hz,c,p⟩:= strategy F (m:=m) (min L (H i)) (lt_min hL hH) he
    refine ⟨(K,u,x),⟨⟨w₀,v⟩,c,fun t v=>?_⟩,hz,p.trans (min_le_right ..)⟩; change ‖Q t-Q (pole _ _ F.eP.le slate)‖ ≤ _; obtain ⟨g,d,b,f_a⟩:= c.roll _ v; rw [show Q t = Q _ from (hy.2.1 t g).symm] -- direction wrong
    let U:= routeS g t; let W:=pole (f i) B F.eP.le d; apply (norm_sub_le_norm_sub_add_norm_sub _ (Q W) _).trans; exact add_le_add (X U W (fun i=>(f_a i).trans (p.trans (min_le_left ..)))) (hy.2.2 _)
 obtain ⟨b,h⟩:= budgetO _ hx; have ht:Aqua (bean f) H:= Aqua.exp_neg g 1 one_pos; refine ⟨fun i=>(b i).1,_,fun i=>(b i).2.1,_, ht.panel (alive g R _ _ _ _ hl hc),ht.clip g (h.mono fun i u=> ⟨u.1.hall.pose.le,u.2.2⟩),h.mono fun i k=> ⟨k.1,k.2.1⟩⟩ -- replace
variable {α:Type*}
abbrev dart (o:Opt (α:=α) M')(U:Pack m B):= seekV m B (fun u=>Emu.muni o.o u o.R o.f o.L) U.1
def vision (o:Opt (α:=α) M')(q:Clip)(S β:ℝ)(u:Bkg (Domain m B)):=primal q (Domain m B) β S u • feel o u (changeM P u firstM) -- implicit P hidden
variable (W:Opt (α:=α) (CSide m B))(q:Clip)(K: BagX m B e)
def crossH(K:BagX m B e)(S β:ℝ)(x:Bkg n'):=∫ z, shore F R K * Spark.hoist q S β R (scarf m) (dart W) (x,z) ∂rains m
lemma hours (S β:ℝ): Integrable (crossH F R W q K S β) (prior group n') ∧ ∫ u,crossH F R W q K S β u ∂prior group n'= shore F R K * shire q S β R (scarf m) (dart W):=by
 let Xf:=dart W
 let G:=fun x:Pack m B=> shore F R K * Spark.hoist q S β R (scarf m) Xf x; have he : Integrable G (RP.wheel m B):=by
    exact (obtainR q S β R (scarf m) _ (show Continuous Xf from ((cxC _).comp (teg W.o W.R W.f W.L)).comp continuous_fst) Z.valid.bond.passesP).const_mul _
 refine ⟨he.integral_prod_left,?_⟩; change (∫ u, ∫ v,G (u,v) ∂_ ∂ (barrow m B))= _; rw [←integral_prod G he]; exact integral_const_mul ..
include F
lemma opt_pay {w': Wave (Single M')}(U:Bkg n')(p: Pic.Yep (H*(M').val) (mateK M') w' (2*c*Kea.angel m P firstM))(l:n≤ (M').val)(b:‖Emu.gain W.R‖ ≤ (M').val^ (2:ℕ)) : ‖feel W U w'‖ ≤ (H^W.dial * Greek M'^(3*W.dial))*(2*c*Kea.angel m P firstM):=by
 let c':=(H^W.dial * Greek M'^(3*W.dial))*(2*c*Kea.angel m P firstM); let A:= W.f
 have he(z): ‖Emu.wall W.o U z W.R A W.L w' 0‖≤ c':=by
    have hf:0≤ 2*c*Kea.angel m P firstM:=mul_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans F.cP)) (angel_p V F.stmt (F.plan _ l).1 F.p F.eP _ (F.plan _ l).2).le; unfold Emu.wall; rw [mul_zero,sub_zero]; exact Emu.kem p (paid_g W.o U _ _ _ W.L F.kP b) hf
 have hx:=vigor W.o U _ _ _ w' 0 he; rw [mul_zero,sub_zero] at hx; exact hx
abbrev yond (u:ℝ)(h d:ℝ):ℝ:= Real.exp u * (lite W*((Real.exp (skiff m h d (scarf m))-1)/Kea.angel m P firstM))+ (2*u)* ((H^W.dial*Greek M'^(3*W.dial))*(2*c)) -- implicits require explicit
-- statement using actual vision.Sharp.
lemma debtH (S β:ℝ)(a:Corner F R m K h d t τ σ)(s:0<S)(v:S ≤ σ)(k:0<h)(hj:t ≤ 1)(g: ‖Emu.gain W.R‖ ≤ Greek M'^2)(U:Bkg n'): ‖crossH F R W q K S β U - vision (P:=P) W q S β U‖ ≤ (primal q n' β S U)*(yond (H:=H) (c:=c) (P:=P) W t h d * Kea.angel m P firstM):=by
 let W'(U:Bkg n'):= primal q n' β S U; have hp:0≤ W' U:=prim_p ..; let T:=a.hall.frame; have u:=F.plan _ T; let M:= K
 obtain ⟨y,l⟩:= a.well
 rcases eq_or_lt_of_le hp with z|z; · unfold crossH hoist vision; unfold W' at z; simp [←z]
 have hx:=a.hall; have hc:= (Calder F hx S β s v firstM q).1; obtain ⟨f',r,A,e'⟩:=hc.inner U z; have hr:=CostKin F T firstM _ f' (spiral _ A) e' a.hall.pose a.hall.data a.hall.cap; let x:U':=⟨U,hr.1⟩; have hw: ‖lure F R K x‖ ≤ t:= a.limit x (by
    have he:U∈ Calm group n' S:=by by_contra h; unfold W' primal at z; rw [Set.indicator_of_notMem h] at z; exact lt_irrefl _ z
    change flags σ U=∅; apply Finset.eq_empty_iff_forall_notMem.mpr; intro j z; obtain ⟨i,w,t⟩:= (flags_spec ..).mp z; exact notMem_empty j ((show flags S U=∅ from he) ▸ ((flags_spec ..).mpr ⟨i,w,v.trans_lt t⟩))) -- orientation Cult: smaller S means flags at larger sigma none.
 let x':=Complex.exp (lure F R K x); let X:=chantV P (R.c m) K x; let Y:= changeM P U firstM; let g':= feel W U; let w':= W' U; let A':= Kea.angel m P firstM
 have hv:0<A':=angel_p V F.stmt u.1 F.p F.eP _ u.2; have hh: ‖x'-1‖ ≤ 2*t:= (Complex.norm_exp_sub_one_le (hw.trans hj)).trans (mul_le_mul_of_nonneg_left hw (by norm_num)); have ht: ‖x'‖≤ Real.exp t:= (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr hw)
 have hm: ‖g' X-g' Y‖ ≤ lite W*((Real.exp (skiff m h d (scarf m))-1)/A'*A'):=by
    unfold g'; rw [div_mul_cancel₀ _ (ne_of_gt hv), ←(feel_r W U _ _ 0).2]; exact (Graph.earn W _ _ g).trans (mul_le_mul_of_nonneg_left (worn R Z u.1 K x l k.le) (by unfold lite; positivity)) -- tune implicit shadow
 have he: ‖x'*g' X-g' Y‖ ≤ yond (H:=H) (c:=c) (P:=P) W t h d *A':=by
    rw [show _=x'*(g' X-g' Y)+(x'-1)*g' Y from (show x'*g' X-g' Y= _ by ring)]; refine (norm_add_le ..).trans ((add_le_add ((norm_mul x' (g' X-g' Y)).trans_le (mul_le_mul ht hm (norm_nonneg _) (Real.exp_pos _).le)) ((norm_mul (x'-1) (g' Y)).trans_le (mul_le_mul hh (opt_pay F R Z W U hr.2.1 T g) (norm_nonneg _) ((norm_nonneg _).trans hh)))).trans_eq ?_)
    unfold yond A'; ring
 have hg: crossH F R W q K S β U=w' • (x'*g' X):=by
    unfold crossH Spark.hoist; simp_rw [integral_const_mul]; let L:=fun u:Bkg n'=>muni W.o u W.R W.f W.L
    rw [show (∫ z, ratioR _ _ _ _ _ _ _ _ ∂rains m)=_ from (fired R Z u.1 K x L l)]; unfold x' lure; rw [Complex.exp_sub]; unfold shore; rw [Complex.exp_neg]; change _ * (_ * (_ * (feel W U X)))=w' • _; rw [Complex.real_smul]; field_simp; rfl
 change _≤ w'*_; rw [hg,vision]; change ‖w' • _ - w' • _‖≤_; rw [←smul_sub,norm_smul,Real.norm_of_nonneg z.le]; exact mul_le_mul_of_nonneg_left he z.le
end YM.CF.Spark
