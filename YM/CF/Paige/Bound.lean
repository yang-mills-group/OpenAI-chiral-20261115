import YM.CF.Brace.Carry
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Paige
open Function Filter Lattice Metric Lat Finset Cube Tenant SU Fock Dial Phase MeasureTheory Tulip Peaks Rush Brace
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {j:ℕ}{L:Side}{ho:Odd L.val}{T:Script Male}
def cExp (j:ℕ)(L:Side)(ho:Odd L.val)(T: Script Male)(n:ℕ):Chop Male:= earnings (mateF (wh j L ho true)) (mateF (lake j L ho T true)) n
def eExp (T: Script Male)(n:ℕ): Chop Male := earnings skirt (rack T) n
def iExp(j:ℕ):Chop Male:= ingot true (mateF (foal j true))
def fExp(j:ℕ)(L:Side)(ho:Odd L.val):Chop Male:= ingot false (mateF (wh j L ho true))
-- conditions for banking at all mixed records
variable (j L ho T)
structure Tender (n k:ℕ) {N P:Side}(G:Ratio N P)(M:Male)(x:Sew N P) : Prop where
 chart : ∀ u, Along j L ho T u M G (unionP x.1)
 projN : IsStarProjection (spar j (upMale L ho M) x.1.2)
 projP : IsStarProjection (spar j M x.1.1)
 pay : chargeA T G M (post x).1=Complex.exp ((eExp T k M G (post x)).trace)
 lit : Real.exp (((iExp j M G (post x)).trace).re/4)=‖filled (foal j true M G (post x).1) (squareD G true (post x))‖
 rod : Real.exp (((fExp j L ho M G (post x)).trace).re/4)=‖filled (wh j L ho true M G (post x).1) (squareD G false (post x))‖
 sea : effectK (lake j L ho T true M G (post x).1) (filled (foal j true M G (post x).1) (squareD G true (post x)))= Complex.exp ((cExp j L ho T n M G (post x)).trace) • filled (wh j L ho true M G (post x).1) (squareD G false (post x))
 fired (v : Wave (Iota G)) : inner ℂ (mateK N) (fire T G M (post x).1 v)=inner ℂ (oceanA G) v
-- exact support rates stored
structure Pricing (j:ℕ)(L:Side)(ho:Odd L.val)(T:Script Male) where
 n : ℕ
 k : ℕ
 e : ℝ
 range : 0<e
 N : ℕ
 A : ℝ
 C : ℝ
 rate : 0<A
 earningsK: IndexB L (false,true) (false,true) (cExp j L ho T n) A C e N
 beauty:IndexB L (false,true) (false,true) (eExp T k) A C e N
 income:IndexB L (true,true) (true,true) (iExp j) A C e N
 projected:IndexB L (false,true) (false,true) (fExp j L ho) A C e N
 cap {c f:Side}(G:Ratio c f)(u:G.count=L)(p:N≤c.val)(M:Male)(x:Sew c f):Gild G x e→Tender j L ho T n k G M x
include ho
lemma prices(p:Use j L T)(hj:Even j)(hg:1≤j): Nonempty (Pricing j L ho T):=by
 let H:=brass j L ho hj hg T p true; let B:= bonus j L ho hj hg T p
 obtain ⟨n,h,hv⟩:=H.youth ho
 obtain ⟨k,q,t⟩:= B.youth ho
 have ht : BoxD L (false,true) (false,true) (cExp j L ho T n):=H.stable ho h hv
 have hT : BoxD L (false,true) (false,true) (eExp T k):=B.stable ho q t
 obtain ⟨a,C,e,s,w,he,v,hC,hK⟩:= ht.brood hT
 obtain ⟨⟨F,f⟩,⟨I,Y⟩⟩:=scour j L ho hj hg T p true
 obtain ⟨a',C',e',s',w',he',v',hA,H'⟩:= (show BoxD L _ _ (iExp j) from I).brood (show BoxD L _ _ (fExp j L ho) from F)
 obtain ⟨p',hP,x,Q⟩:= ((((f.plus Y).plus (lobeInvoice j L ho hj hg T p k t q)).plus (parentheses j L ho hj hg T p true n h hv)).plus ((festival j hg L).plus (marginH j L ho hj hg T p)))
 let b:=min a a'; let R:=max C C'; let d:=min (min e e') p'; have hd:0<d:=lt_min (lt_min he he') hP; let Z:=max (max v v') x
 have hz:d≤e:= (min_le_left ..).trans (min_le_left ..); have hx:d≤e':= (min_le_left ..).trans (min_le_right ..)
 have he : v≤Z:= (le_max_left ..).trans (le_max_left ..); have he' : v'≤Z:=(le_max_right ..).trans (le_max_left ..);
 refine ⟨⟨n,k,d,hd,Z,b,R,lt_min s s',?_,?_,?_,?_,?_⟩⟩
 · exact fun i _ _ G hu hv=> (((neck hd hz hC) i G hu (he.trans hv)).drop (min_le_left a a')).books (le_max_left ..)
 · exact fun i _ _ G hu hv=> (((neck hd hz hK) i G hu (he.trans hv)).drop (min_le_left a a')).books (le_max_left ..)
 · exact fun i _ _ G hu hv=> (((neck hd hx hA) i G hu (he'.trans hv)).drop (min_le_right a a')).books (le_max_right ..)
 · exact fun i _ _ G hu hv=> (((neck hd hx H') i G hu (he'.trans hv)).drop (min_le_right a a')).books (le_max_right ..)
 intro N P G hG hp M U hV; obtain ⟨⟨⟨⟨s₁,t₁⟩,u⟩,x⟩,q,f⟩:= Q G hG ((le_max_right ..).trans hp) U (hV.breadth G (min_le_right ..))
 exact ⟨f M,(q _).2,(q _).1,(u _).1,t₁ M,s₁ M,(x M).2,(u M).2⟩ -- fix `_`
end YM.CF.Paige
