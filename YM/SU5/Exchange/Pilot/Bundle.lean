import YM.SU5.Exchange.Pilot.Contour
import YM.SU5.Exchange.Reg.Incidence
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
variable {P:BudgetPoint}{X Y Z:Aura n}{V W:Firing n}{D:Support (More n)}
open Rill Branch Tenant Drapes Leaf Bake Ione
variable {k q:ℕ}{h a b c d s u:ℝ}
local notation "Hz"=> Scree.Hub n
variable {F:RegBudget n}
structure Sectoral (P:BudgetPoint)(q:ℕ)(V:Bag n)(h s c:ℝ):Prop where
    ink: 0 ≤ c
    jet: ∃ z:Aura n→ℝ,(∀ X:Aura n,Herb P q X h (V X) (z X)) ∧ ∀ x:Seat n, nook (z*tact s P.B) x ≤ c
lemma Sectoral.lessR {V:Bag n}(u:Sectoral P q V h a d)(l:s≤a): Sectoral P q V h s d:=by
 obtain ⟨z,f,p⟩:=u.jet; exact ⟨u.ink,z,f,fun x=>le_trans (sum_le_sum (s:=spark x) (fun i _=>mul_le_mul_of_nonneg_left (tact_para l _) (f i).price)) (p x)⟩
-- regulator tiles. Loom stance preserves its exact Mask sectors.
def scald(P:BudgetPoint)(F:RegBudget n)(Y:Aura n): Firing n:=∑ i:Hz, if Y=⟨i.val.2,i.val.1,i.property⟩ then wetPC P i (F i) else 0
lemma scald_sells (v:Hz→ℝ)(u:∀ i:Hz, PressB P i (F i) h (v i))(t:1 ≤ h)(s:ℝ)(c:ℝ)(p:∀ x:Seat n,(∑ i:Hz, if x∈i.val.2 then massPlus P s i.val.2 (v i) else 0) ≤ c)(w:0 ≤ c): Sectoral P q (scald P F) h (P.supportExponent+s) (chi_f P.order*c):=by
 let L:Hz→Aura n:=fun i=>⟨i.val.2,i.val.1,i.property⟩; let f:=fun (i:Hz)(X:Aura n)=> if X=L i then chi_f P.order*v i else 0; let V(X:Aura n):= ∑ i:Hz, f i X; let R:=tact (P.supportExponent+s) (n:=n) P.B
 refine ⟨mul_nonneg (spicy_f P.order) w,V,fun X=>?_ ,fun x=>?_⟩
 · apply Herb.whole; intro i _; unfold f; split_ifs with g; · exact Herb.growth t (u i) (show i.val.2⊆X.val from congrArg Subtype.val g|>.symm.le) -- tune
   exact Herb.zeroR
 apply le_trans _ (mul_le_mul_of_nonneg_left (p x) (spicy_f _)); apply le_of_eq; change (∑ i∈spark x,V i*R i)=_; simp_rw [V,sum_mul]; rw [mul_sum,sum_comm]; apply sum_congr rfl; intro i _; by_cases u:x∈i.val.2
 · have hp:L i∈spark x:=mem_filter.mpr ⟨mem_univ _,u⟩; rw [sum_eq_single_of_mem (L i) hp, if_pos u, show f i _= _ from if_pos rfl]; change (chi_f P.order * _)* (Real.exp _)=_* (Real.exp _* _); rw [mul_assoc,mul_comm (v i)] -- infer? tune
   intro j p g; rw [show f i j=0 from if_neg g,zero_mul]
 rw [if_neg u,mul_zero]; apply sum_eq_zero; intro j v; rw [show f i j=0 from if_neg (fun (g:j=L i)=> u ((mem_filter.mp (g ▸ v :L i∈spark x)).2)),zero_mul]
abbrev giveB (V:Bag n):Firing n:= ∑ i:Aura n, V i
lemma scald_at (x:Orbit n)(F:RegBudget n): giveB (scald P F) x=(exponentL P F x.1).val:=by
 rw [giveB]; simp_rw [scald,sum_comm (s:=univ) (t:=(univ:Finset (Scree.Hub n)))] -- loops
 simp; -- tune
 change _=(Dough (Dwell n)).val (∑ i:Hz,numbE P.threshold i.val.2 (F i) x.1); rw [map_sum]; rfl
-- bump convolution; omit disjoint even if flags exist all around Tape
abbrev cBump (V W:Firing n):Firing n:=V*W-W*V
abbrev regionW (V W:Bag n):Bag n:= Leaf.Ktw fun X Y=> cBump (V X) (W Y)
lemma Herb.pastR (f:Herb P q Y h V a)(p:Herb P q X h W b)(u: Disjoint X.val Y.val): cBump V W=0:=by
 unfold cBump; apply sub_eq_zero.mpr; funext i; change V i*W i= W i*V i
 have hm: Disjoint (camp Y.val) (camp X.val):=disjoint_left.mpr fun j h k=> disjoint_left.mp u (mem_filter.mp k).2 (mem_filter.mp h).2
 calc _ = (Fock.Sector.grainB false false) • (W i*V i):= (f.body i).apart (p.body i) hm
      _ = _:=one_smul ℂ _
variable {A: Support (More n)}{C Q: Bag n}
lemma attireV_fee (v:Barrage P q A h C (s+d) a b)(t:Sectoral P q Q h s c)(p:0 ≤ s)(w:0 < d) : let K:= 2*(spanV P.B*d⁻¹ * a*c); Barrage P q A h (regionW C Q) s K K:=by
 intro K; obtain ⟨L,J,z,t',Hc,_⟩:=v.price; obtain ⟨N,f,g⟩:=t.jet
 let W(Y:Aura n)(X:Aura n):= L Y* N X; let U:= fun X:Aura n=>2 * Ktw W X
 have hu'(X:Aura n): U X= Ktw (fun Y X=>2 * W Y X) X:=by unfold U Ktw; simp_rw [mul_sum, mul_ite,mul_zero]
 have hz(X:Aura n) : Herb P q X h (regionW C Q X) (U X):=by
    rw [hu']; apply Herb.whole; intro Y _; apply Herb.whole; intro Z _; split_ifs with p; swap; · exact Herb.zeroR
    have hy: Y.val⊆ X.val:=p ▸ subset_union_left; have hZ:Z.val⊆ X.val:=p ▸ subset_union_right
    simp only [cBump]; rw [sub_eq_add_neg]; let G:=(z Y).tube.mantle hy; let T:=(f Z).mantle hZ
    unfold W; rw [two_mul]; exact (G.mulR T).addR ((mul_comm (N Z) (L Y)) ▸ (T.mulR G).negR)
 have he := (show voyageB U P.B s≤ K from (by rw [show U=_ from (show U=fun X=> 2* Ktw W X from rfl),voyage_scale]; refine mul_le_mul_of_nonneg_left ((voyage_tw p w (fun i=> (z i).tube.price) (fun i=>(f i).price) g t.ink).trans ?_) (by norm_num); exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left Hc (mul_nonneg (show 0 ≤ spanV _ from Nat.cast_nonneg _) (by positivity))) t.ink)) -- syntax `rw` pointless
 refine ⟨⟨U,U,fun i=> Flight.once (hz i),fun i p=>?_ ,he,he⟩⟩
 have hp(Y Z:VX)(r:i=αK Y Z):¬ A⊆ Y.val:=fun v=> p (v.trans (r ▸ subset_union_left))
 have hx:U i=0:=by
    rw [hu']; apply sum_eq_zero; intro Y _; apply sum_eq_zero; intro Z _; split_ifs with z; · dsimp only [W]; rw [(t' Y (hp Y Z z)).2.1,zero_mul,mul_zero]
    rfl
 refine ⟨?_,hx,hx⟩; unfold regionW Leaf.Ktw; apply sum_eq_zero; intro Y _; apply sum_eq_zero; intro Z _; split_ifs with hP; · simp only [cBump]; rw [(t' Y (hp _ _ hP)).1,zero_mul,mul_zero,sub_self]
 rfl
lemma attireV_formula (v:Barrage P q A h C s a b)(t:Sectoral P q Q h u c): giveB (regionW C Q)= cBump (giveB C) (giveB Q):=by
 obtain ⟨L,J,z,_⟩:=v.price; obtain ⟨H,g,_⟩:=t.jet
 let F(Y X:Aura n):= cBump (C Y) (Q X); unfold giveB regionW; unfold Leaf.Ktw; rw [sum_comm]
 have hr(V V':Bag n):cBump (giveB V) (giveB V')= ∑ i:Aura n,∑ j:Aura n,cBump (V i) (V' j):=by unfold cBump giveB; simp_rw [sum_mul,mul_sum,sum_sub_distrib]; rw [sum_comm (f:=fun i j=> V' i* V j)]
 rw [hr]; apply sum_congr rfl; intro i _; rw [sum_comm]; refine Eq.trans (b:=∑ j∈Cadre.blaze i,F i j) ?_ (sum_subset (subset_univ _) ?_)
 · simp only [sum_ite_eq',mem_univ,ite_true]; rfl
 intro j _ p; exact Herb.pastR (z i).tube (g _) (by by_contra u; exact p (mem_filter.mpr ⟨mem_univ _,fun v=>u v.symm⟩)) -- orientation
variable (P:BudgetPoint)
def tailor (F:RegBudget n)(C:Bag n):Bag n:=let X:=scald P (head_L F); let T:= regionW C X; C + T + ((2:ℂ)⁻¹) • regionW T X
variable (t:Barrage P q A h C (s+d+d) a b)(p:Sectoral P q (scald P (head_L F)) h (s+d) c) (hx:0 ≤ s)(w:0 < d)
include t p hx w
lemma tailor_price : let T:= 2*(spanV P.B*d⁻¹*a*c); let R:= T+ (2:ℝ)⁻¹*(2*(spanV P.B*d⁻¹*T*c)); Barrage P q A h (tailor P F C) s (a+R) (b+R):=by
 let H:=attireV_fee t p (add_nonneg hx w.le) w; let hP:=p.lessR (le_add_of_nonneg_right w.le); let U:= attireV_fee H hP hx w; intro T R; have hZ:= (((t.lessR (d:=s) (by linarith)).plusR (H.lessR (by linarith))).plusR (U.swell ((2:ℂ)⁻¹))) -- p.letter argu
 rw [norm_inv,show ‖(2:ℂ)‖=(2:ℝ) by norm_num,add_assoc a,add_assoc b] at hZ; exact hZ
lemma tailor_at (x:Orbit n) : giveB (tailor P F C) x= attire (giveB C x) (exponentL P F x.1) :=by
 have H:=attireV_fee t p (add_nonneg hx w.le) w
 have ht(V W:Bag n):giveB (V+W)=giveB V+giveB W:=by simp_rw [giveB,Pi.add_apply, sum_add_distrib]
 let y:ℂ:=2⁻¹; have hk(V:Bag n):giveB (y • V)= y • giveB V:=by simp_rw [giveB,Pi.smul_apply,smul_sum]
 change giveB (_+y • _ :Bag n) x= _; rw [ht,ht,hk,attireV_formula H p,attireV_formula t p]; simp only [Pi.add_apply,Pi.smul_apply]; rw [← attireCut, maskExpHead]; unfold cBump attire bump; simp only [Pi.sub_apply,Pi.mul_apply, scald_at]; unfold y; simp only [← Complex.ofReal_ofNat (n:=2), ← Complex.ofReal_inv, Complex.coe_smul]; -- tune simp syntax
end YM.CF.Sour
