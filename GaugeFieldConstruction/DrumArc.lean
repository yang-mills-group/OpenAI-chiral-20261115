import GaugeFieldConstruction.FernLog
import GaugeFieldConstruction.Delve
set_option autoImplicit false
set_option maxHeartbeats 130000
noncomputable section
namespace YM.GaugeFieldConstruction.Wick.Yacht
open StressFHeat MeasureTheory Analysis Function Filter Metric Maxwell Finset Gap Complex Cauchy Row Phys Flux.One Lamp
open Lattice CF CF.XGarden CF.XGarden.MastTin CF.XGarden.MastTin.ArtCart CF.XGarden.MastTin.ArtCart.Violets CF.Py.Rate.LocalLimit.Papal
open scoped Topology ContDiff BigOperators Classical
open HopeC CF.Buffered CF.Buffered.Lifted
-- sum over stencil. unitaries factors. weights. arbitrary n0.
namespace Trackℓ
open FlightFlux Fluxim TableF.Lenten.Loden TableF
open BluffV BluffV.Lave
variable {N:Side}{a b c:ℕ→Payν N}{x y z:E4}{V Y W:Genre}{X K B:ℝ}{t:ℕ→ℝ}
abbrev Inn (v:Payν N)(s:ℝ)(d:ℕ):= (((s:ℂ)^d)⁻¹) • RankBook s 6 v
abbrev Comply (U:ℕ→Book)(x:Book):Prop:=∀ (f:ℕ→Book→ₗ[ℂ]ℂ)(F:Book→ₗ[ℂ]ℂ),(∀ x,Tendsto (fun k=> f k x) atTop (𝓝 (F x)))→Tendsto (fun k=> f k (U k)) atTop (𝓝 (F x))
abbrev VaultB (a:ℕ→Payν N)(t:ℕ→ℝ)(n:ℕ)(P:Book):=Comply (fun i=>Inn (a i) (t i) n) P
-- generic ranking.Bv. Price consistent comp. no rep metrics
lemma carryB {F:ℕ→Book→ₗ[ℂ]Book→ₗ[ℂ]ℂ}{U:Book→ₗ[ℂ]Book→ₗ[ℂ]ℂ}{a b:ℕ→Book}{x y:Book}(p: Comply a x)(v:Comply b y)(H:∀ i j,Tendsto (fun k=>F k i j) atTop (𝓝 (U i j))): Tendsto (fun i=>F i (a i) (b i)) atTop (𝓝 (U x y)):= p (fun i=> (F i).flip (b i)) (U.flip y) (fun i=> v (fun k=>F k i) (U i) (H i))
lemma carryD {F:ℕ→Book→ₗ[ℂ]Book→ₗ[ℂ]Book→ₗ[ℂ]ℂ}{U:Book→ₗ[ℂ]Book→ₗ[ℂ]Book→ₗ[ℂ]ℂ}{a b c:ℕ→Book}{x y z:Book}(p: Comply a x)(v:Comply b y)(h:Comply c z)(H:∀ i j z,Tendsto (fun k=>F k i j z) atTop (𝓝 (U i j z))): Tendsto (fun i=>F i (a i) (b i) (c i)) atTop (𝓝 (U x y z)):= p (fun i=> ((F i).flip (b i)).flip (c i)) ((U.flip y).flip z) (fun i=>carryB v h (F:=fun k=>F k i) (U:=U i) (H i))
-- estimates.Oh μº complement sum.V.
def Shelter (t:ℕ→ℝ)(p:ℕ→ℂ)(P:ℂ)(d e:ℕ):Prop:=Tendsto (fun i=> p i/(t i:ℂ)^(d+e)) atTop (𝓝 P) -- tune ν align
private lemma beam_p (q e:ℕ)(p M c:ℂ)(a:ℝ): let v:ℂ:=a; p/v^(q+e) = p/v^q*(v^e)⁻¹:=by intro t; rw [pow_add, div_mul_eq_div_div]; exact div_eq_mul_inv ..
private lemma ηstep (L:Tendsto t atTop (𝓝 0))(l:∀ᶠ i:ℕ in atTop,0<t i) {U Q:ℕ→ℂ}(y:ℂ)(H:Tendsto Q atTop (𝓝 y))(C:ℝ)(k:ℕ)(e:k ≤ 6)(p:∀ᶠ i in atTop, ‖U i-Q i‖≤ C*(t i)^(6+1-k)):Tendsto U atTop (𝓝 y):=by
 have hx:Tendsto (fun i=>U i-Q i) atTop (𝓝 0):=by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr; have hz:6+1-k≠0:=by omega
    apply squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) p; simpa [zero_pow hz] using ((L.pow (6+1-k)).const_mul C)
 have ht:= hx.add H; rw [zero_add] at ht; exact ht.congr (fun i=> sub_add_cancel ..)
private lemma ηBill (a:ℝ)(p:0<a)(F G:ℂ)(C:ℝ)(n:ℕ)(h:n ≤6)(t:‖F-G‖ ≤ C*a^(6+1)): ‖(a:ℂ)^(- (n:ℤ))*F - (a:ℂ)^(-(n:ℤ))*G‖≤ C*a^(6+1-n):=by
 simp_rw [zpow_neg,zpow_natCast]; rw [← mul_sub,norm_mul,norm_inv,norm_pow, norm_real,Real.norm_of_nonneg p.le]; refine le_trans (mul_le_mul_of_nonneg_left t (by positivity)) (le_of_eq ?_); rw [show a^(6+1)=a^n * a^(6+1-n) from (by rw [←pow_add]; rw [show n+(6+1-n)=6+1 from (by omega)])]; field_simp
private lemma roof (a:ℝ)(p:0<a)(F G U:ℂ)(n d:ℕ)(h:n≤6)(q:ℂ)(v:F=q/(a:ℂ)^d)(w:U=((a:ℂ)^n)⁻¹*G)(C:ℝ)(t:‖F-G‖ ≤ C*a^(6+1)) : ‖q/(a:ℂ)^(d+n)-U‖ ≤ C*a^(6+1-n):=by
 have he:= ηBill _ p _ _ C n h t; rw [w, beam_p d n q 0 0 a,←v,mul_comm F]; simpa only [zpow_neg,zpow_natCast] using he
variable {g w f:Book}
variable (p: Wagon a V X) (A:Sails t a x)
variable (P: Wagon b Y K) (B':Sails t b y)
variable (u:300<N.val)(h:x≠y)(L:Tendsto t atTop (𝓝 0))(l:∀ᶠ i in atTop,0<t i)
def Qn (a b:ℕ→Payν N)(i:ℕ):ℂ:= quotaZ (a i) (b i) κg κF
include p A P B' u h L l
lemma Shelter2 {d j:ℕ}(X:VaultB a t d g)(Y': VaultB b t j w)(v:d+j≤6): Shelter t (Qn a b) (BigP x y g w) (BaseD V+BaseD Y) (d+j):=by
 let Yk(i:ℕ):=BigP (Mouth (a i) (t i)) (Mouth (b i) (t i)); let hl:ℕ→ℂ:=fun i=>Yk i (Inn (a i) (t i) d) (Inn (b i) (t i) j)
 have hv(a b:Book):Tendsto (fun i=>Yk i a b) atTop (𝓝 (BigP x y a b)):= (healthy (pair a b) (sub_ne_zero.mpr h.symm)).continuousAt.tendsto.comp (B'.sub A)
 have ht:=carryB (F:=Yk) (U:=BigP x y) X Y' hv; change Tendsto hl atTop (𝓝 _) at ht
 obtain ⟨C,e,H⟩:=Fount2 t L l 6 u p P A B' h
 unfold Shelter; refine ηstep L l (Q:=hl) _ ht C (d+j) v ?_; filter_upwards [l,H] with i ti Hi; let F:=Qn a b i/(t i:ℂ)^(pPow (a i)+pPow (b i)); let D:= RankBook (t i) 6 (a i); let Z:=RankBook (t i) 6 (b i); let G:=Yk i D Z; change ‖ _-hl i‖≤_
 have hg: ‖F-G‖ ≤ C * (t i)^(6+1):= Hi.error
 refine roof (t i) ti F G (hl i) (d+j) _ v _ ?_ ?_ C hg
 · rw [show BaseD V=pPow (a i) from congrArg BaseD (p i).1.symm,show BaseD Y=pPow (b i) from congrArg BaseD (P i).1.symm]
 change Yk i (((t i:ℂ)^d)⁻¹ • D) (((t i:ℂ)^j)⁻¹ • Z)= _; rw [map_smul (Yk i),LinearMap.smul_apply,map_smul,smul_eq_mul,smul_eq_mul,pow_add,mul_inv_rev]; change _⁻¹*( _⁻¹*G)= _; ring
omit p P u h A B' l L
abbrev Qk (a b c:ℕ→Payν N)(i:ℕ):= quotas (a i) (b i) (c i) κg κF
lemma trioC(hx:y≠z)(h:x≠y)(q:x≠z){S:ℕ→E4×E4×E4}(u:Tendsto S atTop (𝓝 (x,y,z)))(a b c: Book):
 Tendsto (fun i=>prism (S i).1 (S i).2.1 (S i).2.2 a b c) atTop (𝓝 (prism x y z a b c)):=by
 let P(r:E4×E4×E4):ℂ:=tri r.1 r.2.1 r.2.2 a b c; have hp:Tendsto (fun i=>P (S i)) atTop (𝓝 (P (x,y,z))):= (Flux.One.contTri (x:=fun i:E4×E4×E4=>i.2.1) (y:=fun i:E4×E4×E4=>i.2.2) (z:=fun i:E4×E4×E4=>i.1) (u:=(x,y,z)) (by fun_prop) (by fun_prop) (by fun_prop) hx h.symm q.symm a b c).tendsto.comp u
 exact hp
include p P u h A B' l L
lemma Shelter3 {d j q:ℕ}(C:Wagon c W B)(v: Sails t c z)(T:V≠Genre.mixed)(Z:x≠z)(F:y≠z)(X: VaultB a t d g)(Y':VaultB b t j w)(H:VaultB c t q f)(e:d+j+q≤6): Shelter t (Qk a b c) (prism x y z g w f) (BaseD V+BaseD Y+BaseD W) (d+j+q):=by
 let Vx(i:ℕ):=Mouth (a i) (t i); let Vy(i:ℕ):=Mouth (b i) (t i); let Vz(i:ℕ):=Mouth (c i) (t i); let Yk(i):=prism (Vx i) (Vy i) (Vz i); let hl(i):=Yk i (Inn (a i) (t i) d) (Inn (b i) (t i) j) (Inn (c i) (t i) q)
 let S(i): E4×E4×E4:=(Vx i,Vy i,Vz i)
 have hs:Tendsto S atTop (𝓝 (x,y,z)):= A.prodMk_nhds (B'.prodMk_nhds v)
 have hv(a b c:Book):Tendsto (fun i=>Yk i a b c) atTop (𝓝 (prism x y z a b c)):= trioC F h Z hs ..
 have ht:=carryD (F:=Yk) (U:=prism x y z) X Y' H hv; change Tendsto hl atTop (𝓝 _) at ht
 obtain ⟨E,h',HP⟩:=Fount3 t L l 6 u p P C T A B' v h F Z
 unfold Shelter; refine ηstep L l (Q:=hl) _ ht E (d+j+q) e ?_; filter_upwards [l,HP] with i ti Hi; let Y0:=Qk a b c i/(t i:ℂ)^(pPow (a i)+pPow (b i)+pPow (c i)); let D:=RankBook (t i) 6 (a i); let G:=RankBook (t i) 6 (b i); let R:=RankBook (t i) 6 (c i); let W':=Yk i D G R; have hg : ‖Y0-W'‖≤ E*(t i)^(6+1):=Hi.error
 refine roof (t i) ti Y0 W' (hl i) (d+j+q) _ e _ ?_ ?_ E hg
 · rw [show BaseD V=pPow (a i) from congrArg BaseD (p i).1.symm,show BaseD Y=pPow (b i) from congrArg BaseD (P i).1.symm,show BaseD W=pPow (c i) from congrArg BaseD (C i).1.symm]
 change Yk i (((t i:ℂ)^d)⁻¹ • D) (((t i:ℂ)^j)⁻¹ • G) (((t i:ℂ)^q)⁻¹ • R)=_; rw [map_smul (Yk i),LinearMap.smul_apply,LinearMap.smul_apply,map_smul ((Yk i) D),LinearMap.smul_apply,map_smul, smul_eq_mul,smul_eq_mul,smul_eq_mul,pow_add,pow_add,mul_inv_rev,mul_inv_rev]; change _⁻¹*( _⁻¹* ( _⁻¹ * W'))= _; ring
-- actual Waves.Note namespace.F... combine $
end Trackℓ
end YM.GaugeFieldConstruction.Wick.Yacht
end
