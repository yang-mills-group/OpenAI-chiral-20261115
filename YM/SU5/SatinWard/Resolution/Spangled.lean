import YM.SU5.SatinWard.Resolution.Jostle

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 700000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.QuadClock
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue Hake Jet Sault Stax Rill Ione Clock Salt Mew PowerSeries Sour Turning
attribute [local instance] opCStarAlgebra
open scoped Mew
variable {n N B:Side}
local notation "Ω"=> mid N B
open QuadClock Neon Bake Larch Roots Py Swell Analysis Pressure Oath Moto Porticus
variable {p:BudgetPoint}{q l m n₀:ℕ}{h w μ c d x a b v s' τ Q:ℝ} {F: ForceBudget (mid N B)}
variable {s:Sweep (mid N B)} {E: Bag (mid N B)}{o:Site (mid N B)}


open Waxy SweepSign
open Vow.TreasuryFog Buffered Swell.Porticus Hive Roots
namespace Lampshade
variable {χ:SweepSign (mid N B)}
abbrev BodyPull (s:Sweep n):Mark n→ₗ[ℝ]Mark n where
 toFun:= flyMark s⁻¹
 map_add' _ _:=funext fun i=>map_add ..
 map_smul' r y:= by
    funext i; change teen s⁻¹ (r • _) = r • _
    rw [←Complex.coe_smul r, show teen s⁻¹ _= _ from Scree.cumin s⁻¹.charge (detX s⁻¹.s) _ _ (r:ℂ), show cSignX (s⁻¹.charge.xor (detX s⁻¹.s)) (r:ℂ)=(r:ℂ) from by cases (s⁻¹.charge.xor (detX s⁻¹.s))<;> simp [cSignX]]; rfl -- tune
abbrev CartPull (s:Sweep n): phy n→ₗ[ℝ]phy n where
 toFun:= cartPrice s⁻¹
 map_add' _ _:=funext fun i=>map_add ..
 map_smul' r y:= by
    funext i; change teen s⁻¹ (r • _) = r • _
    rw [←Complex.coe_smul r, show teen s⁻¹ _= _ from Scree.cumin s⁻¹.charge (detX s⁻¹.s) _ _ (r:ℂ), show cSignX (s⁻¹.charge.xor (detX s⁻¹.s)) (r:ℂ)=(r:ℂ) from by cases (s⁻¹.charge.xor (detX s⁻¹.s))<;> simp [cSignX]]; rfl
abbrev StockPull (s:Sweep n): Bag n→ₗ[ℝ]Bag n where
 toFun:=cartTurn s⁻¹
 map_add' _ _:=funext fun i=>funext fun x=>map_add (Urn.lotY ..) ..
 map_smul' r y:= by
    funext i x; change sauce _ _ _ (r • _) = r • _
    simp only [sauce,singT,win_r,map_smul]; rfl
lemma BodyPull_mult {s t:Sweep n}{X:Mark n}(S:Support (More n))(pS:AtSupport false S X): BodyPull (s*t) X=BodyPull s (BodyPull t X):= by
 change flyMark (s*t)⁻¹ _ = _; rw [mul_inv_rev]; exact (fliesCombine t⁻¹ S s⁻¹ pS).symm
lemma CartPull_mult {s t:Sweep n}{X:phy n}{S:Support (More n)}(pS:∀ i,Sector (modesIn n S) false (X i)): CartPull (s*t) X=CartPull s (CartPull t X):=by
 funext i; change teen (s*t)⁻¹ (X (yellA (s*t)⁻¹⁻¹ _))=teen s⁻¹ (teen t⁻¹ _); rw [inv_inv,mul_inv_rev, yetL _ _ _ (paritySale.checked (pS _)), ←yell_t]; simp -- expect simpl tune
lemma StockPull_mult {s t:Sweep n}{X:Bag n}(pS:∀ i y,Sector (camp i.val) false (X i y)): StockPull (s*t) X=StockPull s (StockPull t X):=by
 funext i v; obtain ⟨i,rfl⟩:=(moldA s⁻¹).surjective i; obtain ⟨v,rfl⟩:=yspec s⁻¹ v; change cartTurn (s*t)⁻¹ X _ _= cartTurn s⁻¹ (cartTurn t⁻¹ X) _ _; rw [mul_inv_rev]; exact (crosses X pS t⁻¹ s⁻¹ i v).trans (runs ..).symm
lemma parcel_old {V:Type*}[AddCommGroup V][Module ℝ V](P:Sweep n→ V →ₗ[ℝ] V)(M:V)
 (p:∀ s t:Sweep n,P (s*t) M=P s (P t M))(i:Site n)(χ:SweepSign n): SignBent χ P (orbitAverage P i χ M):=by
 intro s hp x y q; rw [orbitAverage,alleyS, reprice_eq χ x y i s hp q,map_smul,map_sum]; simp_rw [map_smul]; rw [smul_comm (χ.sgn s),Finset.smul_sum (r:=χ.sgn s)]
 refine congrArg (fun v:V=> reprice χ x i • v) (sum_equiv (Equiv.mulLeft s) (sameWay χ x y i s hp q) (fun j (ii:j∈ways χ y i)=>?_)); rw [← p]; change _= χ.sgn s • χ.sgn (s*j) • _; rw [χ.mult hp ((ways_iff ..).mp ii).1,smul_smul,←mul_assoc,χ.sq hp,one_mul]; rfl
variable {j:ℕ}{φ:ArcΦ}{U:Cusp (mid N B)}{ζ:ℂ}{L:RegBudget (mid N B)} {S:Support (More (mid N B))} {e z β:ℝ}
variable {k τL:ℕ}{L':Side}{p':Odd L'.val}{X : Pricing k L' p' (Thread k)}{Y:Grasp X B d}{W:Scree.Loom (mid N B)}{R:GramM (mid N B)}
local notation "Zβ" => offsetMask j
local notation "Zr" p:max y:max=> grooveB m p (node y)
structure Tab (K:Bag Ω)(T:Mark Ω)(V:phy Ω)(A:RegBudget Ω)(B_:Cusp Ω)(t:ℂ)(Φ:ArcΦ) (Y:Grasp X B d)(W:Scree.Loom (mid N B))(R:GramM (mid N B))(j m:ℕ)(o:Site (mid N B))(q s:ℕ)(h x a b w u z g:ℝ) : Prop where
  vlease:WindowTag T o j g
  visit:Contact W (offsetMask j o) T V
  hot:Vessel Y R W K V
  prices:Flint R.p K (grooveB m R.p (node o)) A B_ t Φ o s q h x a b w u z
-- not defeq bench.Omega inside signature must not shadow N B
variable {T:Mark (mid N B)}{V:phy (mid N B)}{U₀:RegBudget (mid N B)}{F₁: Bag (mid N B)}{ZQ:phy (mid N B)}
lemma Tab_zero: Tab (X:=X) 0 0 0 0 0 0 0 Y W R j m o q l h x 0 0 0 0 0 0:= ⟨WindowTag.zero,⟨AtSupport.zeroM,fun _=>Sector.zero _, fun _=>rfl⟩,vessel_nil,voidFlint (halo_subset _ _ (mem_singleton_self _))⟩
lemma Tab_upgrade (f:Tab E T V L U ζ φ Y W R j m o q l h x a b e z w β){a' b' c' d' e' f':ℝ}(p:a≤a')(t:b≤b')(H:e≤c')(v:z≤d')(y:w≤e')(q':β≤f'):Tab E T V L U ζ φ Y W R j m o q l h x a' b' c' d' e' f':=
 ⟨{ f.vlease with price:=fun i=> (f.vlease.price i).trans q'},f.visit,f.hot,Flint_gain f.prices p t H v y⟩
lemma Tab_down (v:Tab E T V L U ζ φ Y W R j m o q l h x a b e z w β){i l':ℕ}{r:ℝ}(g:j ≤ l')(t:i ≤ m)(e':r ≤ x):Tab E T V L U ζ φ Y W R l' i o q l h r a b e z w β:=by
 let S:= offsetMask j o; let Z:= offsetMask l' o; have ht:S⊆Z:=Corona.halo_mono g le_rfl
 refine ⟨v.vlease.transfer ht,⟨v.visit.pitch.mono ht,fun i=> lift_v (v.visit.oscillator _) (modes_monotone ht),v.visit.bra⟩,v.hot, Flint_fade ?_ e'⟩
 obtain ⟨H,V,w,Y,W,hᵢ⟩:=v.prices.step.price; have hu:grooveB i R.p (node o)⊆ Zr (R.p) o:= Corona.halo_mono (Nat.mul_le_mul_right R.p.B t) le_rfl; exact ⟨halo_subset _ _ (mem_singleton_self _), ⟨H,V,w,fun x p=> Y x (fun t=> p (hu.trans t)),W,hᵢ⟩,v.prices.mood⟩
lemma Tab_add (v:Tab E T V L U ζ φ Y W R j m o q l h x a b e z w β){U':Cusp Ω}{ζ':ℂ}{φ':ArcΦ} {c' d' e' v' w' b':ℝ}{T':Mark Ω}(k':Tab F₁ T' ZQ U₀ U' ζ' φ' Y W R j m o q l h x c' d' e' v' w' b')(f:0≤h): Tab (E+F₁) (T+T') (V+ZQ) (L+U₀) (U+U') (ζ+ζ') (φ+φ') Y W R j m o q l h x (a+c') (b+d') (e+e') (z+v') (w+w') (β+b'):= ⟨v.vlease.add k'.vlease,v.visit.add k'.visit, vessel_more v.hot k'.hot,Flint_bag v.prices k'.prices f⟩
lemma Tab_coin (v:Tab E T V L U ζ φ Y W R j m o q l h x a b e z w β)(g:ℝ)(u:0≤h): Tab (g • E) (g • T) (g • V) (g • L) (g • U) (g • ζ) (g • φ) Y W R j m o q l h x (|g| *a) (|g| *b) (|g| * e) (|g| *z) (|g| *w) (|g| *β):=by
 refine ⟨?_,?_,?_,Flint_coin v.prices u g⟩; simpa only [Complex.norm_real,Real.norm_eq_abs,Complex.coe_smul] using v.vlease.scale (g:ℂ); exact v.visit.scale (g:ℂ); exact vessel_sized (g:ℂ) v.hot
lemma Tab_sum {ι:Type*}(S:Finset ι)(K:ι→Bag Ω)(T:ι→Mark Ω)(V:ι→phy Ω)(A:ι→RegBudget Ω)(B_:ι→ Cusp Ω)(t:ι→ ℂ)(φ:ι→ArcΦ)(a b c d' e f:ι→ ℝ)(Z:∀ i∈ S,Tab (K i) (T i) (V i) (A i) (B_ i) (t i) (φ i) Y W R j m o q l h x (a i) (b i) (c i) (d' i) (e i) (f i))(v:0≤h): Tab (∑ i∈S,K i) (∑ i∈S,T i) (∑ i∈S,V i) (∑ i∈S,A i) (∑ i∈S,B_ i) (∑ i∈S,t i) (∑ i∈S,φ i) Y W R j m o q l h x (∑ i∈S,a i) (∑ i∈S,b i) (∑ i∈S,c i) (∑ i∈S,d' i) (∑ i∈S,e i) (∑ i∈S,f i):=by
 induction S using Finset.induction_on with
 | empty=> simp only [sum_empty]; exact Tab_zero
 | insert i S t ih=>simp only [sum_insert t]; exact Tab_add (Z i (mem_insert_self ..)) (ih fun j v=> Z j (mem_insert_of_mem v)) v
lemma Tab_pull (χ:SweepSign Ω)(t:Tab E T V L U ζ φ Y W R j m o q l h x a b e z w β)(f:0≤h)(i:Site (mid N B))(p:Earlier s i o)(t':s ∈ χ.group)(j':HavenL Ω R.p l)(ship:∀ s:Sweep Ω,Vessel Y R W (cartTurn s E) (cartPrice s V)): Tab (StockPull s E) (BodyPull s T) (CartPull s V) (Eρ s L) (Kρ s U) (tρ s ζ) (turnD s φ) Y W R j m i q l h x a b (duty_Q R.p.order R.p.power*e) (strive_E R.p.order*z) w β:=by
 have hz:(boxA s⁻¹).symm (node o)=node i:=by rw [sitU]; exact p
 have hp:actY s⁻¹ (offsetMask j o)=offsetMask j i:=by ext i; unfold offsetMask actY; rw [mem_map_equiv, ←hz]; have hD:=sitT s⁻¹ ((boxA s⁻¹).symm (node o)) i; rw [Equiv.apply_symm_apply] at hD; simp [halo_spec,hD] -- tune
 exact ⟨spectral_charge s⁻¹ t.vlease hz, hp ▸ charge_contact s⁻¹ _ _ t.visit t.vlease.pane, ship _, FlintPull χ t.prices f i p j' t'⟩
structure Tabular (K:Site Ω→ Bag Ω)(T:Site Ω→Mark Ω)(V:Site Ω→phy Ω)(A:Site Ω→RegBudget Ω)(D:Site Ω→Cusp Ω)(Φ:ArcΦ)(Y:Grasp X B d)(W:Scree.Loom (mid N B))(R:GramM (mid N B))(j m q s:ℕ)(χ:SweepSign Ω)(h x a b w u z g:ℝ):Prop where
 deeds:∀ i, Tab (K i) (T i) (V i) (A i) (D i) 0 Φ Y W R j m i q s h x a b w u z g
 books : SignBent χ StockPull K ∧ SignBent χ BodyPull T ∧ SignBent χ CartPull V ∧ SignBent χ Eρ A ∧ SignBent χ Kρ D ∧ χ.Eigenspace Φ ∧ InΦ Φ
lemma tabular (χ:SweepSign Ω)(u:Tab E T V L U ζ φ Y W R j m o q l h x a b e z w β)(f:0≤h)(k:HavenL Ω R.p l)(s:χ.KillsScalar)(ship:∀ s:Sweep Ω,Vessel Y R W (cartTurn s E) (cartPrice s V)): let Φ:=alleyS o χ turnD φ o; let K:=orbitAverage StockPull o χ E; let T_:=orbitAverage BodyPull o χ T; let V_:=orbitAverage CartPull o χ V; let A:=orbitAverage Eρ o χ L; let D:=orbitAverage Kρ o χ U; Tabular K T_ V_ A D Φ Y W R j m q l χ h x a b (duty_Q R.p.order R.p.power*e) (strive_E R.p.order*z) w β:=by
 intro Φ K T_ V_ A D; let Z:=alleyS o χ turnD φ; let Zc(y:Site Ω):=(offsetMask j y); have hb(y:Site Ω):Tab (K y) (T_ y) (V_ y) (A y) (D y) 0 (Z y) Y W R j m y q l h x a b (duty_Q R.p.order R.p.power*e) (strive_E R.p.order*z) w β:=by
    let S:= ways χ y o; have he(i:Sweep Ω)(v:i∈S): Tab (χ.sgn i • StockPull i E) (χ.sgn i • BodyPull i T) (χ.sgn i • CartPull i V) (χ.sgn i • Eρ i L) (χ.sgn i • Kρ i U) (χ.sgn i • tρ i ζ) (χ.sgn i • turnD i φ) Y W R j m y q l h x a b (duty_Q R.p.order R.p.power*e) (strive_E R.p.order*z) w β:=by
       obtain ⟨p,h⟩:=(ways_iff ..).1 v; have hx:=Tab_coin (Tab_pull χ u f y h p k ship) (χ.sgn i) f; simpa only [χ.abs_sgn p,one_mul] using hx
    rw [←show orbitAverage tρ o χ ζ y=0 from congrFun (s _ (orbitAvg_t χ o ζ)) y]; have hp:=Tab_coin (Tab_sum S _ _ _ _ _ _ _ _ _ _ _ _ _ he f) (reprice χ y o) f; simpa only [abs_of_pos (reprice_pos ..),sum_const,nsmul_eq_mul,S,reprice_pr] using hp
 have hz:SignBent χ Eρ A:=orbitAvg_E χ o L
 let δ:=duty_Q R.p.order R.p.power
 have moves (g:Sweep Ω)(v:g∈χ.group)(i y:Site Ω)(p:Earlier g i y): turnD g (Z y)=χ.sgn g • Z i:=by
    have Vμ:=(Flint_emit (hb i).prices).1; have χb:= wheelTwo g (χ.fits v) i y p f k (Flint_emit (hb y).prices).1; have t:=(real_E i (χ.sgn g) Vμ f); rw [show base_Q g (A y)=_ from (hz g v i y p)] at χb
    have hu:=χb.flair (Φrap Ω i 10) (atRim k i); have hv:= t.flair (Φrap Ω i 10) (atRim k i); rw [if_pos rfl] at hu hv; exact hu.2.symm.trans hv.2
 have everywhere (x:Site Ω) : Z x= Φ:=by
    have h₁:=moves _ (χ.translations _) x o (earlier_translate x o); have h₂:= moves _ (χ.translations _) o o (earlier_translate o o); rw [χ.space, one_smul] at h₁ h₂; exact h₁.symm.trans h₂
 have he(g:Sweep Ω)(p:g∈χ.group) : turnD g Φ= χ.sgn g • Φ:=by
    have he:= moves g p (mPath g o) o ((earlier_mills ..).mpr rfl); rw [everywhere, everywhere] at he; exact he
 exact ⟨fun y=> everywhere y ▸ hb y,parcel_old StockPull E (fun _ _=> StockPull_mult (Flint_owner u.prices)) o χ, parcel_old BodyPull T (fun _ _ => BodyPull_mult _ u.vlease.ticket) o χ,parcel_old CartPull V (fun _ _=> CartPull_mult u.visit.oscillator) o χ,hz,orbitAvg_K χ o U, he, claim_T _ _ ⟨l,(by have hd:=k.door; omega)⟩ k.door Φ (A o) (Flint_emit (hb o).prices).1 k.pay f⟩ -- tune
end Lampshade
end YM.CF.QuadClock
