import YM.CF.Acorn.Fresh
import YM.CF.Jet.Kip
set_option autoImplicit false
noncomputable section
namespace YM.CF.Acorn
open Function Filter Metric Lat Finset Tenant Branch Fock Dial MeasureTheory Phase Phase.Sample Lattice Cube Broc Drapes Tulip Peaks Brace Paige Rush Matrix
open scoped Topology Matrix BigOperators ContDiff NNReal Matrix.Norms.L2Operator InnerProductSpace
set_option synthInstance.maxSize 8000
attribute [local instance] opCStarAlgebra
private def dir (b c: Bool):AxisT:=(b,c)
def proto : Chop Male:=fun i _ _ G x=> squareD G false x
def coatL (j:ℕ)(i:Male){N P:Side}(G: Ratio N P)(x:Bale N P):= (zL (repeated j) (repeated j) (i,termJ 0 0) G x)⁻¹*(repeated j i G x)
def fluffy(j:ℕ) :Chop Male:=fun i _ _ G x=> -(coatL j i G x * proto i G x* cc (1-repeated j i G (chargeB x)))
def wheat(j:ℕ) : Chop Male:=fun i _ _ G x=> (1-repeated j i G x)*(proto i G x-proto i G x*coatL j i G x*proto i G x)*cc (1-repeated j i G (chargeB x))
private lemma steam(j:ℕ){N P:Side}(G:Ratio N P)(x:Sew N P)(i:Male): zL (repeated j) (repeated j) (i,termJ 0 0) G (post x)=stage (repeated j i G (post x)) (proto i G (post x)):=by rw [zL_at,lane_at,termJ]; simp [straightC,proto]
lemma wash(j:ℕ){N P:Side}(G:Ratio N P)(x:Sew N P)(i:Male): coatL j i G (post x)=reserve (repeated j i G (post x)) (proto i G (post x)):=by rw [coatL,steam,reserve]
private lemma camp_cost {u v:AxisT}{F:Chop Male}{L:Side}{e:ℝ}{a d:ℝ}{k:ℕ}(p:IndexB L u v F a d e k){g h:ℝ}{m:ℕ}(t:m≥k)(l:0<g)(s:g≤ e)(r:a≥ h){c:ℝ}(e':d≤ c): IndexB L u v F h c g m:=fun i _ _ G he v=> (((neck l s p) i G he (t.trans v)).drop r).books e'
private abbrev η: AxisT:=(false,true)
private abbrev κ: AxisT:=(false,false)
structure Repair (j:ℕ) where
 a:ℝ
 d:ℝ
 K:ℝ
 n:ℕ
 pa:0<a
 pd:0<d
 pK:0<K
 start:IndexB 1 η η (ingot false (repeated j)) a K d n
 cap:IndexB 1 κ η (@coatL j) a K d n
 sweet:IndexB 1 κ κ (fluffy j) a K d n
 room:IndexB 1 η κ (wheat j) a K d n
 bodyV:IndexB 1 η κ proto a K d n
 ahead(N:Side)(h:n≤N.val)(x:Sew N N)(p:Gild (idrat N) x d)(i:Male):
   let G:=idrat N
   let P:= repeated j i G (post x)
   let C:= proto i G (post x)
   Real.exp (((ingot false (repeated j) i G (post x)).trace).re/4)= ‖filled P C‖ ∧ IsUnit (stage P C)∧ IsStarProjection P
lemma restoreX(j:ℕ)(hj:1≤j):Nonempty (Repair j):=by
 have hp: Land 1 (repeated j) (repeated j) (repeated j):=monoto j hj
 obtain ⟨C,H⟩:=hp.helper (show Odd (1:Side).val from odd_one)
 obtain ⟨hx,hT⟩:=affluent false 1 (repeated j) hp.lay odd_one (hp.sky.forward (by intro N Q G h x u; exact fun i=> (u i).1)) (fun i N Q G he=>(hp.jet i G he).1)
 have ht : BoxD 1 κ η (@coatL j):=(C.reindex (fun i:Male=>(i,termJ 0 0))).chain hp.lay
 have hw : BoxD 1 η κ proto:= tablesB _ false 1 odd_one
 have hq:= BoxD.one.sub hp.lay
 have hp': BoxD 1 κ κ (fluffy j):=by
    have ht:= ((ht.chain hw).chain hq.abrade).scale (fun _=>-1) 1 (by simp); simp only [fluffy,Chop, neg_smul,one_smul] at ht; exact ht
 have hy: BoxD 1 η κ (wheat j) := (hq.chain (hw.sub ((hw.chain ht).chain hw))).chain hq.abrade
 obtain ⟨a,b,y,u,g,s,k,U,V⟩:=ht.brood hp'
 obtain ⟨e,f,z,p,o,R,m,F,X⟩:=hw.brood hy
 obtain ⟨c,d,e',l,r,p',q,A⟩:=hx
 obtain ⟨d',v',q',Y⟩:= (hT.plus (interest_g H).gilded).plus hp.sky
 let t:=min a (min e c); let L:= min (min y z) (min e' d'); let P:= max b (max f d); let N:=max (max k m) (max q q'); have hl : 0<L:=lt_min (lt_min s R) (lt_min p' v');
 have ht1:L≤min y z:= min_le_left ..; have ht2:L≤min e' d':=min_le_right ..; have hc:t≤ min e c:=min_le_right ..; have hL:max k m≤N:=le_max_left ..; have h0:max q q'≤ N:=le_max_right ..; have hb:max f d≤P:=le_max_right ..
 refine ⟨⟨t,L,P,N,lt_min u (lt_min p l),hl,lt_max_of_lt_left g, camp_cost A ((le_max_left ..).trans h0) hl (ht2.trans (min_le_left ..)) (hc.trans (min_le_right ..)) ((le_max_right ..).trans hb),camp_cost U ((le_max_left ..).trans hL) hl (ht1.trans (min_le_left ..)) (min_le_left ..) (le_max_left ..),camp_cost V ((le_max_left ..).trans hL) hl (ht1.trans (min_le_left ..)) (min_le_left ..) (le_max_left ..),camp_cost X ((le_max_right ..).trans hL) hl (ht1.trans (min_le_right ..)) (hc.trans (min_le_left ..)) ((le_max_left ..).trans hb),camp_cost F ((le_max_right ..).trans hL) hl (ht1.trans (min_le_right ..)) (hc.trans (min_le_left ..)) ((le_max_left ..).trans hb),fun Q k z h i=>?_⟩⟩ -- unused vars in camp
 let W:=idrat Q; obtain ⟨⟨R,U⟩, V⟩:= Y W rfl (((le_max_right ..).trans h0).trans k) z (h.breadth W (ht2.trans (min_le_right ..)))
 exact ⟨R i,(steam j W z i) ▸ U (i,termJ 0 0), (V i).1⟩
end YM.CF.Acorn
