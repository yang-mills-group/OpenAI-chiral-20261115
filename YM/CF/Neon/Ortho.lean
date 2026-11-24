import YM.CF.Neon.Eco
import YM.CF.Neon.Pure
set_option autoImplicit false
noncomputable section
namespace YM.CF.Neon
open Lattice Function Filter Real Oath Fock Haro Hove Moto Vow
set_option linter.unusedSectionVars false
set_option maxHeartbeats 450000
variable (x a b c Q W Z :ℝ)
variable (hx:0≤x)(hu:x≤1) (ha:a≥0)(hb:b≥0)(hc:c≥0)(hq:0≤Q)(hw:0≤W)
variable (g d u v z w y t :ℝ)
abbrev mintR(x a b c Q W:ℝ):= x^4*a+x^3*b+x^4*c+x^5*Q+W
abbrev naxR(x a b c Q W:ℝ):= x^5*(a+b+c+Q)+W
abbrev nagR(x a b c Q W:ℝ):= naxR x a b c Q W + x^3*b
include ha hb hc hq hw hx hu
lemma laser_M : x^4*a ≤ mintR x a b c Q W ∧ x^3*b≤ mintR x a b c Q W ∧ x^4*c≤ mintR x a b c Q W ∧ x^5*Q≤ mintR x a b c Q W ∧ W≤ mintR x a b c Q W ∧ x^4*b ≤ mintR x a b c Q W:=by
 unfold mintR; have h1:= mul_nonneg (pow_nonneg hx 4) ha; have h2:= mul_nonneg (pow_nonneg hx 3) hb; have h3:= mul_nonneg (pow_nonneg hx 4) hc; have h4:= mul_nonneg (pow_nonneg hx 5) hq; have ht:= mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hx hu (by decide:(3:ℕ)≤4)) hb; refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> linarith
lemma faith_M : x^5*a≤ naxR x a b c Q W ∧ x^5*b≤naxR x a b c Q W ∧ x^5*c ≤naxR x a b c Q W ∧ x^5*Q ≤ naxR x a b c Q W∧W≤naxR x a b c Q W:=by
 unfold naxR; simp_rw [mul_add]; have h1:=mul_nonneg (pow_nonneg hx 5) ha; have h2:=mul_nonneg (pow_nonneg hx 5) hb; have h3:=mul_nonneg (pow_nonneg hx 5) hc; have h4:=mul_nonneg (pow_nonneg hx 5) hq; refine ⟨?_,?_,?_,?_,?_⟩<;>linarith
local notation "BM"=> (mintR x a b c Q W)
local notation "BN"=> (naxR x a b c Q W)
local notation "BO"=> (nagR x a b c Q W)
-- W includes post-ell absolute rents. One PH oscillator. bounds off-shell frame.
variable (ηφ ηκ :ℝ)
variable (Hg:g≥0)(Hd:d≥0)(Hu:u≥0)(Hv:v≥0)(Hz:z≥0)(Hw:w≥0)(Hy:y≥0)(Ht:t≥0)(Htφ:ηφ≥0)(Hk:ηκ≥0)
variable (G V D E X L P R S U A :ℝ)
variable (hp: G ≤ g*(x^4*a)+W) (hd:D≤u*(x^5*Q)+W) (he:E≤ d*(v*(x^3*b+8*x^4*(c+w*b))+ z*(x^5*Q))) (hs:S ≤ 2*x^5*a) (hR:R ≤ W)(hP:P ≤ W)
variable(hv:V ≤ t*z*(x^5*Q)+ (2*y*(x^5*b)+8*y*(x^5*(c+w*b))))(hU:U ≤ ηφ*(t*z*(x^5*Q)+ y*(x^3*b)+12*y*(x^5*(c+w*b))))
abbrev lush(g d u v z w:ℝ):=g +u +d*(v*(1+8*(1+w))+z)+4
abbrev loon(u:ℝ):=6+u
abbrev coil_T(u z w y t ηκ:ℝ):= ηκ*(u+3)+ (t*z+(2*y+8*y*(1+w)))
abbrev coin_T(u z w y t ηφ ηκ:ℝ):=ηκ*(u+3)+ ηφ*(t*z+y+12*y*(1+w))
include Hg Hd Hu Hv Hz Hw Hy Ht Htφ Hk hp hd he hs hR hP hv hU
lemma dower_s : G+(D+E)+P ≤ lush g d u v z w*BM ∧ S+2*R+D+P≤ loon u*BN ∧ηκ*(R+D+P)+V≤ coil_T u z w y t ηκ*BN ∧ηκ*(R+D+P)+U ≤ coin_T u z w y t ηφ ηκ*BO:=by
 obtain ⟨za,zb,zc,Qb,WB,zh⟩:= laser_M x a b c Q W hx hu ha hb hc hq hw; obtain ⟨xa,xb,xc,Qc,Cc⟩:= faith_M x a b c Q W hx hu ha hb hc hq hw
 have hl : x^4*(c+w*b)≤(1+w)*BM:=by rw [mul_add,add_mul,one_mul,mul_left_comm (x^_)]; exact add_le_add zc (mul_le_mul_of_nonneg_left zh Hw)
 have hΨ: E≤ d*(v*(1+8*(1+w))+z)*BM:=by
    refine he.trans ((mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left (add_le_add zb ((mul_assoc ..).le.trans (mul_le_mul_of_nonneg_left hl (by norm_num)))) Hv) (mul_le_mul_of_nonneg_left Qb Hz)) Hd).trans_eq ?_); ring
 have hD: D≤ u*BM+ BM:= hd.trans (add_le_add (mul_le_mul_of_nonneg_left Qb Hu) WB); have hG:G≤ g*BM+BM:=hp.trans (add_le_add (mul_le_mul_of_nonneg_left za Hg) WB)
 have hL:x^5*(c+w*b)≤ (1+w)*BN:=by rw [mul_add,add_mul,one_mul,mul_left_comm (x^_)]; exact add_le_add xc (mul_le_mul_of_nonneg_left xb Hw)
 have hZ:=mul_le_mul_of_nonneg_left Qc (mul_nonneg Ht Hz); have hn: D≤ u*BN+BN:=hd.trans (add_le_add (mul_le_mul_of_nonneg_left Qc Hu) Cc); have hp:=hP.trans Cc; have hr:=hR.trans Cc
 have hϵ:ηκ*(R+D+P)≤ ηκ*(u+3)*BN:=by refine (mul_le_mul_of_nonneg_left (add_le_add (add_le_add hr hn) hp) Hk).trans_eq ?_; ring
 have hpW := hP.trans WB; have hz:0≤BM:=hw.trans WB; have hb1:BN≤ BO:=le_add_of_nonneg_right (mul_nonneg (pow_nonneg hx 3) hb); have hγ:x^3*b≤BO:=le_add_of_nonneg_left (hw.trans Cc)
 refine ⟨?_,?_,?_,?_⟩
 · unfold lush; linarith only [hpW,hD,hG,hΨ,hz]
 · have h₀:S≤2*BN:=hs.trans ((mul_assoc ..).le.trans (mul_le_mul_of_nonneg_left xa (by norm_num))); unfold loon; linarith only [h₀,hp,hn,hr]
 · refine (add_le_add hϵ (hv.trans (add_le_add hZ (add_le_add (mul_le_mul_of_nonneg_left xb (mul_nonneg (by norm_num:0≤(2:ℝ)) Hy)) (mul_le_mul_of_nonneg_left hL (mul_nonneg (by norm_num:0≤(8:ℝ)) Hy)))))).trans_eq ?_; unfold coil_T; ring
 refine (add_le_add (hϵ.trans (mul_le_mul_of_nonneg_left hb1 ?_)) (hU.trans (mul_le_mul_of_nonneg_left (add_le_add (add_le_add (hZ.trans (mul_le_mul_of_nonneg_left hb1 (mul_nonneg Ht Hz))) (mul_le_mul_of_nonneg_left hγ Hy)) (mul_le_mul_of_nonneg_left (hL.trans (mul_le_mul_of_nonneg_left hb1 (by positivity))) (mul_nonneg (by norm_num:0≤(12:ℝ)) Hy))) Htφ))).trans_eq ?_; positivity; unfold coin_T; ring
end YM.CF.Neon
