import YM.CF.Cour.Vista
import YM.CF.Cour.Thrush
import YM.CF.Cour.Tul
import YM.CF.Cour.EdgeC
import YM.CF.Levier.Hymn
import YM.CF.Hom.Sally
import YM.CF.Cour.Monet
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Cour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Tenant Proa Broc Jet MeasureTheory
open Pec Reef Levier
open scoped Matrix.Norms.L2Operator Topology BigOperators NNReal Classical ContDiff InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {ι:Type}{N m X B L:Side}{n k j:ℕ}{e d t x u C A:ℝ}
variable{G:Ratio (CSide m B) (CSide X B)}
variable {p': Aim (CSide X B)}{o: Odd L.val}{Y:Pricing j L o (Thread j)}{P:Grasp Y B e}{M:Male}
lemma drawZ (n:Side)(k:ℕ)(a b:ℝ)(h:0≤b): CardK n k (0:Toy k n) b a:=by
 constructor; · intro t i j s; ext1 x; change (0:ℂ)= (Rush.wind _ _*Rush.wind _ _) • (0:ℂ); simp
 constructor; intro u v x C g; rw [show Nacre.halo 0 u v x _= (0:Op Slot) from rfl,show Nacre.halo 0 u v x C= (0:Op Slot) from rfl,map_zero]
 intro i; simpa [balance]
abbrev QuotaH (u v a b:ℝ): Type:= (Π n:Side,{Q:Aim n//Q.toll u v a b})× Male
variable{a b r s:ℝ}
lemma xx0(n:Side)(h:0≤a)(p:0≤b):Aim.toll (⟨0,0⟩:Aim n) r s a b:=⟨drawZ _ _ _ _ h,drawZ _ _ _ _ p⟩ -- tune dots
lemma demand (n:Side)(k:0≤a)(h:0≤b)(P:Aim n)(p:P.toll r s a b)(M:Male) :∃ x:QuotaH r s a b,(x.1 n).val=P ∧ x.2=M:=by
 let U:Π N:Side,{F:Aim N//F.toll r s a b}:= Function.update (fun N=>⟨_,xx0 N k h⟩) n ⟨P,p⟩; exact ⟨(U,M),by simp [U],rfl⟩
abbrev arcB (u v a b:ℝ):WG (QuotaH u v a b):= fun i n=> Moire.bloom (i.1 n).val
lemma alum (g:0≤a)(f:0≤b)(p:0<r)(h:0<s): Lively (arcB r s a b)∧∀ i n, arcB r s a b i n 1=0:=⟨Moire.terrace _ g f p h fun i n=>(i.1 n).property,fun i n=>Moire.bloom_zero _⟩
variable {c w:ℝ}
lemma mythU (a:ℝ)(p:0<a)(u:ℝ)(v:1≤u)(k:ℕ)(w:ℝ)(ht:0 ≤ w)(L:Side):∃ f C:ℝ,0<f∧0 ≤ C∧∀ {m X B:Side}(G:Ratio (CSide m B) (CSide X B)),G.count=L →∀ e:ℝ,(∀ P:Pride (CSide m B), (∀ x,cents (node x) (P x) a ≤ w)→Screen (dressL G e) (LineE k G u e) k (fun x=> pigment P x.val.2) f C) ∧ ∀ P:Pride (CSide X B), (∀ x,cents (node x) (P x) a ≤w)→ Screen (dressL G e) (LineE k G u e) k (fun x=> pigment P x.val.1) f C:=by
 obtain ⟨C,h,H⟩:=lumpP a p u v k w ht
 let A:= feeG L.val; let c:= min (a/18) (a/18/A); have hA:0<A:=by unfold A feeG; positivity
 have hx:0<c:=lt_min (by positivity) (by positivity)
 refine ⟨c,max C (A*C),hx,h.trans (le_max_left ..),fun {m r B} G hl e=>?_⟩
 let f(x:Rent0 G e):CapX m B e:=⟨x.val.2,x.property.cg⟩; let y(x:Rent0 G e):CapX r B e:=⟨x.val.1,x.property.fg⟩; have hz:= gainW G; rw [hl] at hz
 constructor
 · intro P p; have hu:= (H m B P p e).leaps (q:=c) (c:=dressL G e) (Ω:=LineE k G u e) (Φ:=poolG G) (v:=A) (w:=A) hz f ((continuous_snd.comp continuous_subtype_val).subtype_mk _) h hx.le ((le_div_iff₀ hA).mp (min_le_right ..)) (fun S x y h=>by intro i a b; exact h.2 i (cloud_pool G S a) (cloud_pool G S b)) (fun x g=>⟨scaleG G g,rfl⟩) (fun E _ _ _ V u f t x hx=>(t x hx).2); exact hu.reserve le_rfl (le_max_right ..)
 intro P p; have hy:=(H r B P p e).leaps (q:=c) (c:=dressL G e) (Ω:=LineE k G u e) (Φ:=id) (v:=1) (w:=1) (idemX (terr _)) y ((continuous_fst.comp continuous_subtype_val).subtype_mk _) h hx.le (by rw [mul_one]; exact min_le_left ..) (fun S x y h=>h.1) (fun x y=> ⟨y,rfl⟩) (fun E _ _ _ V u f t x hx=> (t x hx).1); rw [one_mul] at hy; exact hy.reserve le_rfl (le_max_left ..)
lemma desire_c (z:QuotaH r s a b)(x:nomA m X B)(W:Aim (CSide X B))(p:W=(z.1 _).val) : let U:= coatG L o j G z.2 W.den x; let V:=leftN L j o G z.2 x (W.den x.1); U=nuke L o j (arcB r s a b) Prod.snd z G (unionP x) ∧ V=nukeR j (arcB r s a b) Prod.snd o z G (unionP x):=by
 subst W; intro U V; unfold nukeR nuke vaseR Proa.prime; rw [revI]; change _=bentT _ _ _ (capT _ (foot G (arcB r s a b z _ (profile x.1)))) ∧_=bentT _ _ _ (-star (capT _ (foot G (arcB r s a b z _ (profile x.1))))); unfold arcB; rw [Moire.bloom_P]; exact ⟨rfl,rfl⟩
section
variable (p:0≤a)(f:0≤b)(v:0<r)(q:0<s)(hd:0<d)(hp:Spack j L o C A d k)(H:Stamped j L o Y)(h:1≤j)(he:Even j)
include p f v q hd hp H h he
lemma cost_c (n:ℕ)(A':ℝ)(hA:1≤ A'):∃ c:ℝ,0<c ∧ ∀ {e B}(P:Grasp Y B e),0<e → e ≤ c → Pearl P → ∀ (α β:ℝ),0<α→0≤β→ ∃ r' C:ℝ,0<r'∧0 ≤C∧∃ m:ℕ,∀ {l w:Side}(G:Ratio (CSide l B) (CSide w B)), G.count=L → m ≤(CSide l B).val →∀ (I:Pride (CSide l B))(J:Pride (CSide w B))(K:Aim (CSide w B))(M: Male), Lac I α β → Lac J α β → ClearP I→ClearP J→ K.toll r s a b → Cry K → (∀ y:Rent0 G e,Hops G j o K M y.val) ∧ ∀ σ:ℝ,∃ Y:Msca l w B G e,Tally Y (shipA G P M K.den J I) σ A' r' C n∧ tyke G Y:=by
 obtain ⟨Q,hQ,U⟩:=cityP n hA; obtain ⟨hB,fB⟩:=alum p f v q; let F:=arcB r s a b; obtain ⟨j',t,c,h',ht,hc,L',hp'⟩:= Cour.helix n Q (hA.trans hQ) o he h F hB fB Prod.snd; obtain ⟨c'',hE,z,H'⟩:= Levier.soarR j F Prod.snd L o he h hB fB
 let c':= min (min c'' c) d; refine ⟨c',lt_min (lt_min hE hc) hd,fun {e B} P g u Z α β hα hβ=>?_⟩
 obtain ⟨r₁,v₁,h₁,w₁,Q₁⟩:= coffer Z H g h n Q (hA.trans hQ)
 obtain ⟨r₂,v₂,h₂,w₂,Q₂⟩:=mythU α hα Q (hA.trans hQ) n β hβ L
 let p:=min (min r₁ r₂) j'; let M:=v₂+ (v₁+t) + v₂; have ho:0 <p:=lt_min (lt_min h₁ h₂) h'; let S:=L'+k+ P.roundZ+z; refine ⟨p,M,ho,(by unfold M; positivity),S,fun {l w} G hx hz I J K M hv hw hh hK hR hT=>?_⟩
 have ht:S=L'+k+P.roundZ+z:=rfl; have hu:=u.trans (min_le_left ..); obtain ⟨y,D,D'⟩:=demand (CSide w B) (show 0 ≤ a from by assumption) f K hR M; rw [←D']
 obtain ⟨Q3,H3⟩:=hp' e g (hu.trans (min_le_right ..)) G hx (by omega) y; let f:=coatG L o j G y.2 K.den; have hN(x): f x=nuke L o j F Prod.snd y G (unionP x):=(desire_c y x _ D.symm).1
 have hw'(x:Rent0 G e):Hops G j o K y.2 x.val:=by
    unfold Hops; rw [show coatG _ _ _ _ _ _ _=_ from hN x.val, show leftN _ _ _ _ _ _ _ =_ from (desire_c y x.val K D.symm (j:=j) (G:=G) (o:=o)).2]
    refine ⟨H3 x, (H' y G hx (by omega) (unionP x.val) (ambient _ _ g (hu.trans (min_le_left ..)) x.property)).trans_lt (by norm_num), hp.tape G hx (by omega) _ _ (ambient _ _ g (u.trans (min_le_right ..)) x.property)⟩
 refine ⟨hw',fun σ=>?_⟩
 have hr:= (Q₁ l w G hx (by omega) y.2).reserve ((min_le_left ..).trans (min_le_left ..) : p ≤ r₁) le_rfl
 have hhJ:Screen (dressL G e) (LineE n G Q e) n (fun i=> invoice (coatG L o j G y.2 K.den i.val)) p t:=by
    simp_rw [show ∀ x,coatG L o j G y.2 K.den x=nuke L o j F Prod.snd y G (unionP x) from hN]; exact Q3.reserve (min_le_right ..) le_rfl
 obtain ⟨hg,hg'⟩:= Q₂ G hx e
 have hu:= (hg I hv.pay).reserve ((min_le_left ..).trans (min_le_right ..) : p ≤ r₂) le_rfl; have hp:= (hg' J hw.pay).reserve ((min_le_left ..).trans (min_le_right ..) : p ≤ r₂) le_rfl
 obtain ⟨Y,V,h₃,h₄,h₅⟩:=(hp.plus (hr.minus.plus hhJ.minus)).plus hu.minus; have hf:Tally Y (shipA G P y.2 K.den J I) σ Q p (v₂+(v₁+t)+v₂) n:=by
    refine ⟨⟨_,h₃,h₄⟩,fun v hv=>?_⟩; rw [←h₅ ⟨v,hv⟩]; unfold shipA lush; abel
 exact ⟨patina Y,U G _ _ _ _ _ hf (fun j v=> ship_t J I y.2 Z H hx j.charge (castX j) v.val v.property h (den_r hR) hT (by omega) g (hw' v) hw.lead hv.lead hK hh),patina_T Y⟩
end
end YM.CF.Cour
