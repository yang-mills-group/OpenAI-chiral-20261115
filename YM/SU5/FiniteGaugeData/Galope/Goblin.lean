import YM.SU5.FiniteGaugeData.Galope.Allee
/-! # Explicit boundary & dirt count. need powers of log λ here, and side much larger. Allows uniform in cutoff even w arbitrarily large actual period. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 20000
set_option linter.flexible false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Galope
open Function Finset Filter MeasureTheory Matrix Lattice Wilson RG Precision Avenue
open scoped Topology InnerProductSpace Matrix ContDiff BigOperators Classical Kronecker Matrix.Norms.Frobenius
variable {G:Gauge}{k w M:ℕ}{n:Side}
namespace RouteM
abbrev coreN (w:ℕ):= w^3
def lic (w:ℕ):= coreN w+2*w+10
abbrev parcelM(Z:Finset (Site n))(k:ℕ):= (buy Z k).card
abbrev tB(k:ℕ):= 2*k*shank k^3*3
abbrev tileC(n:Side):=Fintype.card (Site n)
abbrev unload(n:Side):=3*(tileC n)+1
abbrev disc(Z: Finset (Site n))(k:ℕ):= unload n-parcelM Z k
lemma allotA (u:2*(lic w+1)<n.val)(A:Finset (Face (Per n))) :
 (degreeP n (lic w))^4*tB (coreN w) ≤ parcelM (glow A (lic w)) (coreN w)+ A.card*tB (coreN w):=by
 have hp: coreN w ≤ lic w:=by unfold lic; omega
 rw [parcelM,buys_count _ (glow_in ..) hp u]; unfold tB; rw [← add_mul]; gcongr ?x * _; exact glow_count .. -- tune
lemma registered{k:ℕ}{Z:Finset (Site n)}(v:Z⊆ zones n M)(h:k≤M): parcelM Z k≤ unload n:= by
 rw [parcelM, unload,tileC, ←Next.Rank.Axial.free_count,← Fintype.card_coe]; let f(i:↥(buy Z k)) : (Next.Rank.Axial.axle n).Free:=⟨i.val,(excluded v h i i.2).2.2⟩; exact Fintype.card_le_of_injective f fun i j e=>Subtype.ext (congr_arg (fun j:(Next.Rank.Axial.axle n).Free=> j.val) e)
lemma disc_book{Z: Finset (Site n)} (hp:Z⊆ zones n M)(v:k≤M): disc Z k + parcelM Z k=unload n:=Nat.sub_add_cancel (registered hp v)
-- sufficiently high
abbrev Intro (n:Side)(w:ℕ): Prop:= 2 ≤ w ∧ 2*(lic w+1)<n.val ∧ w^5 ≤ n.val
def diamC:ℝ:= 5000 -- very coarse; context.J.
private lemma fourth(x y K τ:ℝ)(he:0≤x)(hp:x≤y)(ht:0≤K)(z:0≤τ)(h:(y-x)*τ≤K*y): (y^4-x^4)*τ ≤ 4*K*y^4:=by
 have hv:=sub_nonneg.mpr hp; have hy:=he.trans hp; let L:= y^3 +y^2*x+y*x^2+x^3; have hh : 0≤L := by unfold L; positivity
 have Hz:L≤4*y^3:=by
    have he:= pow_le_pow_left₀ he hp 2; have h2:=pow_le_pow_left₀ ‹0≤x› hp 3
    unfold L; linarith only [mul_le_mul_of_nonneg_left hp (sq_nonneg y), mul_le_mul_of_nonneg_left he hy, h2]
 calc
    _=(y-x)*τ*L:=by unfold L; ring
    _≤K*y *(4*y^3):= mul_le_mul h Hz hh (mul_nonneg ht hy)
    _ =_:=by ring
private lemma boundL (p:Intro n w):
 let b:=degreeP n (lic w); let x:ℝ:=(↑b)*(2*(coreN w:ℝ)); let t:ℝ:=n.val; x≤ t ∧ (t-x)*(w:ℝ)^2 ≤ 100*t :=by
 intro b x t; obtain ⟨p,h0,p'⟩:=p; let S:ℕ:= shank (lic w); obtain ⟨l,r⟩:=lang n (lic w); let m:ℝ:= w; have hm :2≤m:=by unfold m; exact_mod_cast p -- tune
 let t':ℝ:=coreN w; have hz: (S:ℝ)=2*(t'+2*(w:ℝ)+10)+1:=by unfold S shank lic t'; push_cast; ring
 have hW:0≤t':= Nat.cast_nonneg _; have he:t'=m^3:= Nat.cast_pow ..; have ht: m^5≤t:=by unfold m t; exact_mod_cast p'
 have hv: x=(b:ℝ)*(2*t'):=rfl
 let b':ℝ:=b; have hL:b' * S≤ t:=by unfold t b'; exact_mod_cast (show b*S ≤ n.val from le_trans (Nat.le_add_left _ _) l) -- tune
 have hb: 0 ≤ b' := Nat.cast_nonneg _; have hl:x ≤ b'* S:=by
    rw [hv]; refine mul_le_mul_of_nonneg_left ?_ hb; rw [hz]; change _≤2*(t'+2*m+10)+1; linarith only [hm]
 have hr:t ≤ b'*S+S+1:=by
    have he:t ≤ 1+((b:ℝ)+1)*S:=by unfold t; exact_mod_cast r.le -- tune
    unfold b'; linarith only [he]
 have hG: (S:ℝ)-2*t'=4*m+21:=by rw [hz]; unfold m; ring
 have ha: ((S:ℝ)-2*t')*m^2 ≤ 30*(2*t'):=by rw [hG,he]; nlinarith only [mul_le_mul_of_nonneg_right hm (sq_nonneg m), sq_nonneg m]
 have hc:((S:ℝ)+1)*m^2≤50*t:=by
    rw [hz]; change (2*(t'+2*m+10)+1+1)*_≤_; rw [he]; have hh: m^2 ≤ m^3:=by nlinarith only [mul_le_mul_of_nonneg_right hm (sq_nonneg m),sq_nonneg m]
    have H:m^3≤m^5:=by
       have ht:1≤m^2:=by nlinarith only [hm,mul_self_le_mul_self (by norm_num:0≤(2:ℝ)) hm]
       nlinarith only [mul_le_mul_of_nonneg_left ht (pow_nonneg (show 0≤m by linarith) 3)] -- tune
    linarith only [ht,hh,H,show 0≤ t from Nat.cast_nonneg _]
 refine ⟨hl.trans hL,?_⟩; have H: t-x ≤ ((b':ℝ)*S-x)+(S+1):=by linarith only [hr]
 change _ * m^2≤100*t; apply (mul_le_mul_of_nonneg_right H (sq_nonneg m)).trans; rw [show b' *S-x=b'*((S:ℝ)-2*t') by unfold x b' t'; ring]; have hw:= hl.trans hL; unfold x at hw; linarith only [mul_le_mul_of_nonneg_left ha hb,hw,hc,he,show 0≤t from Nat.cast_nonneg _]
-- bound.E multiplied by w²
lemma qualify (p:Intro n w)(A:Finset (Face (Per n))):
 ((((disc (glow A (lic w)) (coreN w)):ℕ):ℝ)+1)*(w:ℝ)^2 ≤ diamC*(tileC n:ℝ)+ A.card*(tB (coreN w):ℕ)*(w:ℝ)^2:=by
 let Z:=glow A (lic w); let k:=coreN w; let W:ℝ:=w; let m:ℝ:=n.val; let L:= degreeP n (lic w); let x:ℝ:=L*(2*(k:ℝ)); obtain ⟨h1,h2⟩:= boundL p
 let u:=parcelM Z k; have hx:=allotA p.2.1 A; have hc: (3:ℝ)*x^4 ≤ (u:ℕ)+ A.card*(tB k:ℝ):=by
    calc
       (3:ℝ)*x^4 ≤ (L:ℝ)^4*(tB k:ℝ):=by
          have ht:(2*(k:ℝ))^3 ≤ (shank k:ℝ)^3:= by unfold shank; push_cast; gcongr ?x ^ _; linarith
          unfold tB; push_cast; unfold shank at ht; push_cast at ht; unfold x; linarith only [mul_le_mul_of_nonneg_left ht (show 0≤(k:ℝ)*(L:ℝ)^4 by positivity)] -- tune
       _ ≤ _:=by exact_mod_cast hx -- tune
 have hy: disc Z k+u= unload n:= disc_book (glow_in ..) (by unfold lic; omega) -- tune
 have hv:3*m^4+1=(disc Z k:ℕ)+(u:ℝ):=by unfold m; exact_mod_cast (show 3*n.val^4+1= disc Z k+u from (by rw [hy]; unfold unload tileC; rw [site_card])) -- tune
 have hg:m^2 ≤ m^4:=by
    have z:n.val ≥ 1:=n.property; have hz:(1:ℝ)≤m:=by unfold m; exact_mod_cast z
    exact pow_le_pow_right₀ hz (by omega)
 have hτ: W^2≤m^2:=by unfold W m; gcongr ?x ^ 2; exact_mod_cast ( le_trans (Nat.le_self_pow (by omega) w) p.2.2)
 unfold tileC; rw [site_card,Nat.cast_pow]; change ((disc Z k:ℝ)+1)*W^2 ≤ diamC*m^4+_; unfold diamC; have hh:0≤ x:= by unfold x; positivity
 linarith only [fourth x m 100 (W^2) hh h1 (by norm_num) (sq_nonneg W) h2, congr_arg (fun u=> u*W^2) hv, mul_le_mul_of_nonneg_right hc (sq_nonneg W), hg,hτ,show 0≤ m^4 by positivity]
end RouteM
end YM.SU5.FiniteGaugeData.Galope
