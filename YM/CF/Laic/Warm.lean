import YM.CF.Laic.Tear
set_option autoImplicit false
noncomputable section
namespace YM.CF.Laic
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Planned.JetPort Push.Uniform
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m A B L:Side}{j k:ℕ}{ho:Odd L.val}{d a b:ℝ}{n:ℕ}
variable {e:ℝ}{G:Ratio (CSide m B) (CSide A B)}{T:Roam m A B}{F:Forest T.ratio}{z:Vox m B→ AxisChart group F}{Y:Pricing j L ho (Thread j)}{V:Grasp Y B e}
abbrev folkM (F:Forest T.ratio)(U:Snap F→Op (Single (CSide m B)))(a b:ℝ)(k:ℕ):Prop:=HoldX (clothH T F) (popH T) U a b k
lemma sendM{X:Snap F→Op (Iota G)}(K:HoldX (clothH T F) (lookM G) X a b k) (p:T.ratio=ratio G)(h:Odd G.count.val):folkM F (fun y=> summit (patchQ G) (X y)) a b k:=by
 refine ⟨Nacre.tort.mpr (fun i j=> Nacre.tort.mp K.glow _ _),?_, K.funds⟩; unfold popH; have he:= congrArg Ratio.embed p; rw [he]; exact signV G h K.law -- tune unknown X
variable (L j ho G F) in
def floral (M:Male)(X:Dress (CSide A B))(x:Snap F): Op (Single (CSide m B)):=era L j ho G M (hats F x) (X (fine SU.group F x))
variable (L j ho) in
def partM (m B:Side)(M:Male)(X:Dress (CSide m B))(x:Bkg (More (CSide m B))): Op (Single (CSide m B)):=capT (spar j (upMale L ho M) x) (X x)
lemma groan (A:Op (Single (CSide m B)))(U:Dress (CSide m B))(u:Snap F)(M:Male): partM L j ho m B M U (outer group F u)=summit (patchQ G) (capT (wh j L ho true M G (unionP (hats F u))) (endorse G (U (outer group F u)))):=by
 let S:=wh j L ho true M G (unionP (hats F u)); let P:=spar j (upMale L ho M) (outer group F u)
 have he:S=lobe G true*(1-hood G)+ endorse G P:=rfl
 apply Thera.endorseI G; let T:= hood G; let V:= U (outer group F u); let K:=endorse G V; have ht (V): T* endorse G V= endorse G V:=by unfold T hood; rw [rude,one_mul]
 have hu (V): endorse G V*T=endorse G V:=by unfold T hood; rw [rude,mul_one]
 have hx:T*T=T:=(hood_proj G).1; have hv:T*(lobe G true)=lobe G true*T:= (spurH ..).eq.symm
 have hl:S*T=endorse G P:=by rw [he, add_mul,mul_assoc, show (1-T)*T=0 by rw [sub_mul,hx,one_mul, sub_self],mul_zero,zero_add,hu] -- tune def
 have hy:T*S=endorse G P:=by rw [he,mul_add,←mul_assoc,hv,mul_assoc,show T*(1-T)=0 from ?_,mul_zero,ht,zero_add]; rw [mul_sub,hx,mul_one,sub_self]
 rw [spry]; change endorse G ((1-P)*V*P)=T*((1-S)*K*S)*T; rw [←mul_assoc T,←mul_assoc T (1-S),mul_sub,mul_one,hy, sub_mul T,show T*K=K from ht _,mul_assoc _ S,hl]; unfold K; rw [rude, show endorse G V-endorse G (P*V)=endorse G (V-P*V) from ?_,rude,sub_mul (1:Op _) P V,one_mul]; ext i j; by_cases h:en G i ∧ en G j<;>simp [endorse,extendK,h] -- tune endorse_minus
lemma posta (j k n:ℕ)(a b d:ℝ)(L:Side)(h:Odd L.val)(p:Spack j L h a b d n)(v:0<a)(t:0<b)(hx:0<d)(r s:ℝ)(hg:0<r)(hy:0<s):∃ f u:ℝ,0<f∧0<u ∧∀ {m A B:Side}{G:Ratio (CSide m B) (CSide A B)}{T:Roam m A B} (F:Forest T.ratio) (l:T.ratio=ratio G)(e:G.count=L)(b':n≤ (CSide m B).val)(M:Male),
 (∀ U:Dress (CSide A B), ReadY F G (fun i=>foot G (U (fine group F i))) r s k→ U 1=0→ folkM F (floral L j h G F M U) f u k) ∧∀ U:Dress (CSide m B), ReadY F G (fun i=>endorse G (U (outer group F i))) r s k→ folkM F (partM L j h m B M U ∘ outer group F) f u k:=by
 obtain ⟨c,H,hc,hH,D⟩:= creed k v t hx L; let Y:=Fintype.card (SpinIdx × Slot); let q:= min c r; let K:= H+s; have hh:0<q:=lt_min hc hg; have hK:0<K:=add_pos hH hy; obtain ⟨w,y,h',hv,hk,C⟩:= pivM q K k Y hh hK
 let V:=2*((1+K)*K*conductor k Y w); let J:=slip k w; let Z:= 2*(V*K*conductor k Y J); let E:=slip k J; have hJ:=slip_pos k h'; have hY:=conductor_pos k Y h' -- order
 have hZ:0<Z:=by have hy:=conductor_pos k Y hJ; unfold Z V; positivity
 refine ⟨E,y+Z,slip_pos k hJ,add_pos hk hZ,fun {m A B G T} F he hp hb M=>?_⟩
 let Tt:= tally G; let X:=unionP ∘ hats F; have ht (F' :Coil (CSide m B) (CSide A B)→ Op (Iota G))(r0 s0:Bool)(H':Crown (badge (legal G d)) (Peaks.parcel G r0 d) (Peaks.parcel G s0 d) a b (fun i=> F' i.val)): ReadY F G (F'∘ X) q K k:=by
    obtain ⟨f,x⟩:=D F G he hp _ r0 s0 H'; exact ((HoldX.drop (⟨f,x,hH⟩: ReadY F G _ c H k) (min_le_left c r)).lift (le_add_of_nonneg_right hy.le)) -- shadow
 let W:= wh j L h true M G
 have hW:ReadY F G (W∘ X) q K k:= ht W false false (p.U M G hp hb)
 have hw:Odd G.count.val:=hp.symm ▸ h
 constructor
 · intro U Hn hQ
   let A:=fun x:Snap F=>foot G (U (fine group F x)); have hy':A 0=0:=by unfold A; rw [show fine group F 0=_ from (congrArg Prod.fst (hats0 (F:=F)): _ = _),Prod.fst_one, hQ]; rfl
   have hm:=C Tt ((Hn.drop (min_le_right _ _)).lift (le_add_of_nonneg_left hH.le)) (ht _ _ _ (p.K M _ hp hb)) (ht _ _ _ (p.W M _ hp hb)) hW (ht _ _ _ (p.P M _ hp hb)) hy'
   refine (sendM ((hm.drop ((slip_le k hJ.le).trans (slip_le k h'.le))).lift (le_add_of_nonneg_right hZ.le)) he hw) -- tune let def
 intro U Hn; have hU:ReadY F G (fun i=>endorse G (U (outer group F i))) w K k:=((Hn.drop (hv.trans (min_le_right c r))).lift (le_add_of_nonneg_left hH.le))
 let P:=hW.drop hv; have hz:= sendM (((((HoldX.blank h').opP P.minus).times hU h' Tt).times (P.drop (slip_le k h'.le)) hJ Tt).lift (le_add_of_nonneg_left hk.le)) he hw
 rw [show (partM L j h m B M U ∘ outer group F)=_ from funext fun i=>groan (G:=G) 0 U i M]; exact hz
end YM.CF.Laic
