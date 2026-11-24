import YM.CF.Reef.Inert
import YM.CF.Cascade.May
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Reef
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {L B A m:Side}{ho:Odd L.val}{j k:ℕ}{a b d r s u v n X η e:ℝ}{Y:Pricing j L ho (Thread j)}{P:Grasp Y B e}
variable {G:Ratio (CSide m B) (CSide A B)}{T:Roam m A B}{F:Forest T.ratio}{z:Vox m B→ AxisChart group F}{K: Aim (CSide A B)} {M:Male}
variable (H:Hull j L ho a b d e k m A B G T F z Y P){R:RG.PathData group}{q:RG.Clip}
abbrev CryK {m r:Side}{T:RG.StepData (More m) (More r)} (F:Forest T.ratio)(z: Cloud m→AxisChart group F):Prop:= ∀ᶠ x in 𝓝 0,z (cloak _ x)=cloak _ (z x)
def Cry {N:Side}(F:Aim N):Prop:= Neat F.x∧ Neat F.y
lemma cry_p{N:Side}{F:Aim N}(p:Cry F)(x:Bkg (More N)): F.den (echo x)=rally N (F.den x):=by simp only [Aim.den,Pi.add_apply]; rw [p.1,p.2,map_add]
include H
lemma salute (p:CryK F z):∀ᶠ x in 𝓝 0, ears F z (cloak _ x)=stanza G diva (xtra true) (ears F z x):=by
 filter_upwards [p] with x hx; let S:=stanza G diva (xtra true) (ears F z x); refine Prod.ext ?_ ?_
 · change lifting F (represent _) (z _)= stir (xtra _) (Shape.broad G diva) _; simp only [ContinuousLinearEquiv.apply_symm_apply]; rw [hx,repr_c,lift_c,stanza_d,stir_d]; congr 1 -- tune
 rw [show (ears F z _).2= _ from (repr_c x), show S.2= _ from stir_d (N:=CSide m B) (represent x)] -- tune S
lemma heed (p:CryK F z)(c:Cry K)(h: Aim.toll K r s u v)(M:Male):let f:=emergence L j ho G F z M K.den
 let W:=coatG L ho j G M K.den ∘ ears F z;∀ᶠ x in 𝓝 0, f (cloak _ x)=rally (CSide m B) (f x) ∧ invoice (W (cloak _ x))=star (invoice (W x)):=by
 intro f W; filter_upwards [H.native.melod _ H.hi G,salute H p,H.native.melod _ H.po G, H.nickP M (den_r h|>.self)] with x hx hp hU hV
 let w:= ears F z x; let w':= stanza G diva (xtra true) w
 let X:=crux j G M w (K.den w.1); let D:=foal j true M G (unionP w); let V:= pflux diva G axS (xtra true); let U:=crux j G M w' (K.den w'.1); have ht:= H.tape.AlongC G H.fromL H.request M w hU true
 have he:= unitedX H.stamp H.hi H.above G H.fromL H.size_p M w hx X (tag_g _ ht.lead) (H.tape.tape _ H.fromL H.request M (unionP w) (ambient _ _ H.po le_rfl hU)) diva (xtra true) axS cloneSX hV.1 hV.2
 have hz: Odd G.count.val:=H.fromL.symm ▸ ho
 have hm(i): (stanza G diva (xtra true) i).1=echo i.1:=by change stir _ _ _= _; rw [stanza_d]; exact stir_d _
 have hg:U=sings true V X:=by
    unfold U X crux; rw [show w'.1=echo w.1 from hm w,cry_p c,rally_p]; let C:=K.den w.1
    have he:= portFoot G hz diva (xtra true) axS C; rw [stanza_d] at he; rw [show foot G (sings true _ _)= sings true V (foot G C) from he.symm]; have ht: sings true V D=foal j true M G (unionP w'):= (hoarD G hz diva (xtra true) axS cloneSX j H.above M _ w ⟨hx.fg.shrink P.gem,hx.cg.shrink P.gem,fun i=>(hx.follow i).trans P.gem⟩ (H.stamp.fields_one _ (P.needed.trans H.size_p)) (H.stamp.fields_one _ (P.needed.trans (P.clock_fine G H.size_p))) true).1 -- issue L
    rw [← ht]; change _=twist V (cc ((1-D)*foot G C*D)); rw [cc_mul,cc_mul,cc_sub,cc_one,map_mul,map_mul,map_sub,map_one]; rfl -- tune
 rw [show f (cloak _ x)=fruit L j ho G M w' U from ?_, show W (cloak _ x)=desire L j ho G M w' U from ?_,hg]; exact ⟨he.2.2,he.2.1⟩
 · change coatG L ho j G M _ (ears F z _) = _; rw [hp]; rfl
 change fruit L j ho G M (ears F z (cloak _ x)) (crux j _ _ _ (K.den ((ears F z _).1)))= _; rw [hp]
lemma ton_p (M:Male): ContDiffAt ℝ ω (spar j (upMale L ho M) (N:=CSide m B) ∘represent) 0:=by
    let V:=wh j L ho true M G
    have he: legal G d∈𝓝 (unionP (ears F z 0)):= (Peaks.cabin ..).mem_nhds (ambient _ _ H.po le_rfl (H.native.melod d H.po G).self_of_nhds)
    have hh:ContDiffAt ℝ ω (fun i=>V (unionP (ears F z i))) 0:= (crown_air G (H.tape.U M G H.fromL H.request) _ he).comp (f:=unionP ∘ ears F z) _ H.native.tarnish
    let f(i:Vox m B):= spar j (upMale L ho M) (represent i); have hz(i): f i=summit (patchQ G) (V (unionP (ears F z i))-lobe G true*(1-hood G)):=by
       rw [show V _= _ from (show V _=lobe G true*(1-hood G)+ endorse G (f i) from rfl),add_sub_cancel_left]; rw [←edgeDesk]; ext x y; exact (desk_at (patchQ G) (f i) x y).symm
    change ContDiffAt ℝ ω f 0; rw [funext hz]; refine Nacre.tort.mpr fun i j=>?_ ; exact Nacre.tort.mp (hh.sub (g:=fun _=> lobe G true*(1-hood G)) contDiffAt_const) _ _
def dod(W: Aim A):Aim A:= ⟨dolphin W.x,dolphin W.y⟩ -- shadow
lemma bike(M:Male)(W:Aim (CSide m B))(p:Aim.toll W r s u v): Cry (dod W)∧(dod W).toll r s u v ∧ ∀ᶠ x in 𝓝 0, let g(X:Aim (CSide m B)):= flareP L j ho M X.den; g (dod W) x=(2:ℝ)⁻¹ • (g W x+rally _ (g W (cloak _ x))):=by
 obtain ⟨h,V,t⟩:=ferocious W.x p.1; obtain ⟨hp,U,z'⟩:=ferocious W.y p.2; refine ⟨⟨h,hp⟩,⟨V,U⟩,?_⟩
 filter_upwards [H.native.melod _ H.hi G] with x hx; intro g; let R:= represent x; let S(X:Bkg (More (CSide m B))): Op (Single (CSide m B)):= spar j (upMale L ho M) X
 have he: rally _ (S R)= S (echo R):=by
    have he: sings true (axle _) (S R)= S (stir (xtra true) diva R):= funde_f diva (xtra true) axS cloneSX R _ H.above (upMale L ho M) _ (H.stamp.fields_one _ (P.needed.trans H.size_p)) (hx.cg.shrink P.gem)
    rw [←stir_d]; exact he
 let G(X: Bkg (More (CSide m B))) := capT (S X)
 have hv:g W (cloak _ x) = capT (S (echo R)) (W.den (echo R)):=by change capT (S (represent _)) (W.den (represent _))= _; rw [repr_c]
 let c:= (2:ℝ)⁻¹
 have hk(A K:Op (Single (CSide m B))): rally _ (capT A K)=capT (rally _ A) (rally _ K):=by
    unfold capT; change twist _ (cc _) = _; rw [cc_mul,cc_mul,map_mul,map_mul,cc_sub,map_sub,cc_one,map_one]; rfl -- tune order
 rw [hv,hk,← he, relay_n]; change capT (S R) (colorX _ R+colorX _ R)= c • (capT (S R) (W.den R)+capT (S R) (rally _ (W.den _)))
 rw [show colorX (dod W).x R= _ from t R,show colorX (dod W).y R= _ from z' R]; unfold capT Aim.den; simp only [Pi.add_apply,map_add,mul_add,add_mul,Matrix.mul_smul,Matrix.smul_mul,smul_add]; change _+_= _; unfold c; abel
section table
variable {D Z:Type}[NormedAddCommGroup D][NormedSpace ℝ D][NormedAddCommGroup Z][NormedSpace ℝ Z]
omit H
lemma avg_c {f g: D→Z}(p:ContDiffAt ℝ (↑(2:ℕ)) f 0)(h:cFoot 3 f)(L:D→L[ℝ] D)(R:Z→L[ℝ] Z)(he: g=ᶠ[𝓝 0] ((2:ℝ)⁻¹ • (f+(R ∘ (f ∘ L))))): cFoot 3 g:=by
 intro i hi;
 have hx : ContDiffAt ℝ i (f ∘ L) 0:= (show ContDiffAt ℝ (↑(2:ℕ)) f (L 0) from by rw [map_zero]; exact p).comp (f:=L) 0 L.contDiff.contDiffAt |>.of_le (by exact_mod_cast Nat.le_of_lt_succ hi)
 have hu:p=p:=rfl; clear hu; let H:= f ∘ L; have hm: ContDiffAt ℝ i (R ∘ H) 0:= R.contDiff.contDiffAt.comp _ hx; have h':ContDiffAt ℝ i f 0:= p.of_le (by exact_mod_cast Nat.le_of_lt_succ hi); change g =ᶠ[_] _ • (f+(R ∘ H)) at he
 rw [(he.iteratedFDeriv ℝ i).eq_of_nhds,iteratedFDeriv_const_smul_apply (f:=(f+(R∘H))) (h'.add hm), iteratedFDeriv_add_apply h' hm,R.iteratedFDeriv_comp_left hx le_rfl,Next.Foundations.jets_linear _ h',h i hi]; simp; ext1 x; exact map_zero R -- tune
end table
lemma mood (w:CryK F z)(p:Cry K)(v':Aim.toll K r s u v)(M:Male) (U:Aim (CSide m B))(t: Aim.toll U r s u v)(y:cFoot 3 (emergence L j ho G F z M K.den-flareP L j ho M U.den)) : Cry (dod U)∧(dod U).toll r s u v∧ cFoot 3 (emergence L j ho G F z M K.den-flareP L j ho M (dod U).den):=by
 obtain ⟨ht,hq,hg⟩:= bike H M U t; refine ⟨ht,hq,?_⟩
 let p':=ton_p H M; let f(X:Aim (CSide m B)):=flareP L j ho M X.den; let r:= emergence L j ho G F z M K.den; have hd: ContDiffAt ℝ ω (r - f U) 0:= (H.terms M (den_r v').self).2.2.2.sub (((contDiffAt_const.sub p').mul (den_r t).self.2).mul p': ContDiffAt ℝ ω (f U) 0)
 apply avg_c (hd.of_le le_top) y (cloak _) (rally _)
 filter_upwards [hg,heed H w p v' M] with x h hh; change r x - f (dod U) x=(2:ℝ)⁻¹ • ((r x-f U x)+rally _ (_-_)); rw [show f (dod U) x=_ from h, map_sub, show r (cloak _ x)= _ from hh.1, relay_n]; let X:= r x; let W:= f U x; let Y:= rally _ (f U (cloak _ x)); change X-(2:ℝ)⁻¹ • (W+Y)= (2:ℝ)⁻¹ • ((X-W)+(X-Y)); rw [show (X-W)+(X-Y)=(2:ℝ) • X - (W+Y) by rw [two_smul]; abel, smul_sub, smul_smul]; simp
end YM.CF.Reef
