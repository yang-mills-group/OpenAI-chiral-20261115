import YM.CF.Thera.Fun
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Thera
open Function Filter NormedSpace Finset Fock Lat Lattice Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Spire
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {L A m B:Side}{j:ℕ}{ho:Odd L.val}{Y:Pricing j L ho (Thread j)}{e:ℝ} {P: Grasp Y B e}(H:Stamped j L ho Y)(p:0<e)(q:1≤j)
variable (G:Ratio (CSide m B) (CSide A B)) (h:G.count=L)(k:P.roundZ ≤(CSide m B).val)(M:Male)(x:nomA m A B)(g:JointB G x e)
variable (C: Op (Iota G))(t:TagG (foal j true M G (unionP x)) C)(J:IsUnit (Peaks.cloth j M G (unionP x)))(a:Shape){b r:Bool}(F:ColorT b)(U:UNI SpinIdx)(w:JetS a.s b r U)
private lemma switchR {n:Type*}[LinearOrder n][Fintype n](b r:Bool)(V:UNI n)(C:Op n): sings b V (jazz r C)=jazz r (sings b V C):=by cases r; rfl; change sings b _ (-star _) = -star _; rw [singT,singT,win_n,win_s,map_neg,map_star]
private lemma neg_bill (z:ℂ) (b:Bool):cSignX b (star z)=cSignX (b.xor true) z:=by cases b<;>simp [cSignX]
include t H p q g k h J w
set_option maxHeartbeats 650000 in
lemma unitedX (v:‖desire L j ho G M x C‖ <1)(z:‖bentT (pine j L ho (Thread j) false M G (unionP x)) (wh j L ho false M G (unionP x)) (ticketT (Thread j) false M G (unionP x)) (-star C)‖<1):let S:= pflux a G U F; let Y:=jazz r (sings b S C); let u:=stanza G a F x
 ‖desire L j ho G M u Y‖<1∧ invoice (desire L j ho G M u Y)= cSignX (b.xor r) (invoice (desire L j ho G M x C)) ∧ fruit L j ho G M u Y=jazz r (sings b (prepU a U F (CSide m B)) (fruit L j ho G M x C)):=by
 subst L
 intro S Y' x'
 have hv(y:nomA m A B)(r:JointB G y e): ∀ b,Along j G.count ho (Thread j) b M G (unionP y):=by
   obtain ⟨v,hx⟩:= cue_from y.2; let T:=starfish m B y.2 v; have ht:=pose_g P p G rfl k y r T (starK P.capY p.le r.cg hx); exact (Y.cap G rfl (P.needed.trans k) M _ ht.glyph).chart
 let Pk:= k; let L:= Thread j
 let X(i:Bool):=foal j i M G (unionP x); let B'(i:Bool):=wh j G.count ho i M G (unionP x); let K(i:Bool):=pine j G.count ho L i M G (unionP x); let W(i:Bool):=ticketT L i M G (unionP x)
 let P':=X true; let Y:=B' true; let f:=sings b S; let u:= prepU a U F (CSide m B)
 let X'(i:Bool):=foal j i M G (unionP x'); let B''(i:Bool):=wh j G.count ho i M G (unionP x'); let K'(i:Bool):=pine j G.count ho L i M G (unionP x'); let W'(i:Bool):=ticketT L i M G (unionP x'); have hx':= alongS F a G x _ g
 have ht(i): Clad (X i) (B' i) (W i) (W (!i)) (K i):=court _ _ _ _ _ i _ (hv x g i)
 have hp(i): Clad (X' i) (B'' i) (W' i) (W' (!i)) (K' i):=court _ _ _ _ _ i _ (hv _ hx' i)
 have he(i:Bool): f (X i)= X' (r.xor i) ∧ f (B' i)=B'' (r.xor i):=hoarD G ho a F U w j q M _ x ⟨g.fg.shrink P.gem,g.cg.shrink P.gem,fun i=>(g.follow i).trans P.gem⟩ (H.fields_one _ (P.needed.trans k)) (H.fields_one _ (P.needed.trans (P.clock_fine G k))) i
 have hc (i:Bool):f (W i)=W' (r.xor i):=titles _ ho _ _ _ w _ _ _ _ J
 have hb (i:Bool):f (K i)=K' (r.xor i):=frame_turn S _ _ _ _ _ _ _ _ _ _ (ht i) (hp _) b (he i).1 (he i).2 (hc i)
 let Fk(i:Bool)(C):=bentT (K i) (B' i) (W i) C
 have hk:r.xor (r.xor true)=true:=by cases r<;>decide
 set i:=r.xor true; have hy:Y'=f (jazz r C):= (switchR ..).symm
 let C':=jazz r C; have hd: desire G.count j ho G M x' Y'=f (Fk i C'):=by
   unfold desire; rw [show pine _ _ _ _ _ _ _ _=K' (r.xor i) from congrArg K' hk.symm,show wh _ _ _ _ _ _ _=B'' (r.xor i) from congrArg B'' hk.symm,show ticketT _ _ _ _ _= W' (r.xor i) from congrArg W' hk.symm,hy, ←hb,←hc,← (he i).2]; unfold Fk bentT f; simp_rw [singm]; rfl -- tune
 have hJ:‖Fk i C'‖<1:=by subst i; cases r; exact v; exact z
 refine ⟨hd ▸ ((singN b S _).trans_lt hJ),?_,?_⟩
 · rw [hd]; have hx: invoice (f (Fk i C'))=cSignX b (invoice (Fk i C')):=by
      have h:=icing (b:=b) S (B' i) _ _ C' hJ; unfold bentT at h; simp_rw [← singm] at h; exact h
   rw [hx]; subst i; cases r; simp only [Bool.xor_false]; rfl -- tune
   have hl:Clad (1-X true) (1-B' true) (W false) (W true) (K false):=by
      rw [←show X false=1-X true from foil_neg _ G true M (unionP x),←show B' false=1-B' true from wh_neg j _ ho G true M (unionP x)]; exact ht false
   rw [show invoice (Fk _ _)=star (invoice (desire G.count j ho G M x C)) from ?_, neg_bill];
   have he:B' false=1-B' true:=wh_neg j _ ho G true M _; change invoice (bentT (K false) (B' false) _ (-star _))=_; rw [he]; apply star_iv (ht true) hl t v; rw [←he]; exact z
 change summit (patchQ G) (traitP (B'' true) (K' true) (W' true) Y')= _; rw [←hk,← (he i).2,←hb,←hc, hy]; rw [show traitP (f (B' i)) _ _ _= _ from spice S (B' i) (W i) C' (K i) (close_c hJ)]
 subst i; cases r; change summit _ (sings b _ _)=sings _ _ _; exact everyK ..
 have ht': X false=1-X true:=foil_neg _ G true M (unionP x); have he:B' false=1-B' true:=wh_neg j _ ho G true M _
 have hl:Clad (1-X true) (1-B' true) (W false) (W true) (K false):=by rw [←he, ←ht']; exact ht false
 change summit _ (f (traitP (B' false) (K false) (W (!true)) (-star C)))= -star _; rw [he,reflectL (ht true) hl t (close_c v) ?_]; swap; rw [←he]; exact close_c z
 let Z:=traitP (B' true) (K true) (W true) C
 change summit _ (sings b S (-star Z))=-star (sings b (prepU a U F _) (summit _ Z)); rw [show sings b S (-star Z)= -star (sings b S Z) from switchR b true S Z]
 rw [←everyK G b _ a F U]; rfl
end YM.CF.Thera
