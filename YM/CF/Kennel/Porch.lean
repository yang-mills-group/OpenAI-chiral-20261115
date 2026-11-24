import YM.CF.Kennel.Dove
set_option autoImplicit false
noncomputable section
namespace YM.CF.Kennel
open Function Filter Lattice Wilson Laurent Precision Tree Finset Exterior Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m A B L:Side}{j:ℕ}{ho:Odd L.val}{d a b:ℝ}{n:ℕ}{G:Ratio (CSide m B) (CSide A B)}
variable {e:ℝ}{Y:Pricing j L ho (Thread j)}
lemma soil {N:Type*}[LinearOrder N][Fintype N](R: Bool)(P C Q:Op N)(B:UNI N)(p:IsStarProjection P)(q:IsStarProjection Q)(h:twist B P=swapX R Q): Thera.jazz R (twist B (capT P C))=capT Q (Thera.jazz R (twist B C)):=by
 have hx: twist B (capT P C)=capT (twist B P) (twist B C):=by unfold capT; simp
 rw [hx,h]; cases R; rfl
 unfold capT; change -star ((1-(1-Q))*_* (1-Q))= (1-Q)*(-star _)*Q
 rw [sub_sub_cancel,star_mul,star_mul, star_sub,star_one,q.2]; simp only [mul_neg, neg_mul, mul_assoc]
lemma duelX (q:1≤j){Q:Grasp Y B e}(h:0<e)(H: Stamped j L ho Y)(hp:G.count=L)(ht: Q.roundZ≤(CSide m B).val) {M:Male}{x:nomA m A B}(hx:JointB G x e)(hz:IsUnit (Peaks.cloth j M G (unionP x)))(C: Op (Single (CSide A B))) (w:Shape)(b:= capT (foal j true M G (unionP x)) (foot G C)) (hb:b=capT (foal j true M G (unionP x)) (foot G C))(U: ‖desire L j ho G M x b‖<1)(Z:‖bentT (pine j L ho (Thread j) false M G (unionP x)) (wh j L ho false M G (unionP x)) (ticketT (Thread j) false M G (unionP x)) (-star b)‖<1): let F:= stanza G w inert x; let V:=ZoneH (w.broad G) C; let Y:=capT (foal j true M G (unionP F)) (foot G V)
 fruit L j ho G M F Y= ZoneH w (fruit L j ho G M x b)∧ invoice (desire L j ho G M F Y)= cSignX (detX w.s) (invoice (desire L j ho G M x b)) ∧ ‖desire L j ho G M F Y‖<1:=by
 subst b; intro F V Y'; subst L; let R:=detX w.s; let T:= spinX w.s; let S:=pflux w G T inert; let P:=foal j true M G (unionP x); let D:=foal j true M G (unionP F)
 have hp(E:nomA m A B)(i:JointB G E e): IsStarProjection (foal j true M G (unionP E)):=by
    obtain ⟨t,hT⟩:= Phase.cue_from E.2; let X:= Brace.starfish m B E.2 t; have hv:=pose_g Q h G rfl ht E i X (Brace.starK Q.capY h.le i.cg hT); exact (Y.cap _ rfl (Q.needed.trans ht) M _ hv.glyph).chart true |>.lead
 let C':=capT P (foot G C); have Hp:IsStarProjection P:= hp x hx; have Hq:IsStarProjection D:= hp _ (alongS _ _ _ _ _ hx)
 have he:= (hoarD G ho w inert T (bud_s _) j q M _ x ⟨hx.fg.shrink Q.gem,hx.cg.shrink Q.gem,fun i=>(hx.follow i).trans Q.gem⟩ (H.fields_one _ (Q.needed.trans ht)) (H.fields_one _ (Q.needed.trans (Q.clock_fine G ht))) true).1
 have hk: twist S P=swapX R D:=by
    change twist S P= foal j (R.xor true) M G (unionP F) at he; rw [he]; cases h:R; rfl; exact foil_neg ..
 have ht': Y'=Thera.jazz R (sings false S C'):=by
    change capT D _= Thera.jazz R (twist S C'); rw [show Thera.jazz R (twist S C')= _ from soil R P _ D S Hp Hq hk]; congr 1; have hm:V=Thera.jazz R (twist (prepU (Shape.broad G w) T inert _) C):= zone_c ..
    rw [hm, ← show foot G (twist (prepU (Shape.broad G w) T inert _) C) = twist S (foot G C) from (portFoot G ho w inert T C).symm]; cases R <;> first|rfl|simp [Thera.jazz,foot] -- tune
 let K:=unitedX H h q G rfl ht M x hx C' (tag_g _ Hp) hz w inert T (bud_s _) U Z; rw [ht',zone_c]; exact ⟨K.2.2,by simpa only [Bool.false_xor] using K.2.1,K.1⟩ -- tune
end YM.CF.Kennel
