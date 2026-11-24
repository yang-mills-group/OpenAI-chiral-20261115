import YM.CF.BProof.Contour.Delicacy

/- Activation & true-core tests. Bridges to excited-state indexed product.
Assist hypothesis allows freshness a.e. (i.e., all angular noise already in balls).
No assumption on phases outside accepted range. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Contour.Battery
open Function Filter NormedSpace TopologicalSpace MeasureTheory Relation Finset RG
open Lattice Prox Grid Moment Account Tower Season
open scoped Topology BigOperators Classical
variable {n:ℕ}(s: Fin n→Side)(r:ℕ)
abbrev Zone(X:Vertex s→Type*):=(i:Vertex s)→ X i
variable {s}{X:Vertex s→Type*} [∀ i,MeasurableSpace (X i)] (P:Pot X)
structure Solar (E:Zone s X→ Exc s)(fresh:Zone s X→Prop) where
 meas : Vis E
 ae (b:Exc s) : ∀ᵐ x∂πμ X P.μ P.ν b, E x=b∧fresh x
variable (E:Zone s X→ Exc s)(adm fresh:Zone s X→Prop)
-- define Fact.Pantry. witness `condition` characteristic; local occupancy in core; not require meas of Exc as finset. G weight domain via densityB Borel & Uniform envelope. null off state else skip. Point.
structure Gold where
 test : CoreX s r→ Zone s X→Prop
 bought (i:CoreX s r) : Virtue s X (test i) -- may require enlarge counts etc
 reads (i): Contour.reads X (test i) (Grid.collar i.val r)
 licence(x: Zone s X) : fresh x →(adm x ↔∀ i∈ chooseE r E x,test i x)
structure Night (C:Gold r E adm fresh)(q:CoreX s r→ℝ) where
  money : CoreX s r→Zone s X→ℝ
  wage_m (i): Envelope (money i)
  ok (i): Contour.reads X (money i) ((plan s r).T i)
  hp (i x): 0≤money i x
  price(i): (∫ x, money i x ∂πμ X P.μ P.ν i.val)≤q i
structure Bronze (G:CoreX s r→Zone s X→ℂ){C:Gold r E adm fresh}{q:CoreX s r→ℝ}(D:Night r P E adm fresh C q): Prop where
  bill (i): Measurable (G i)
  cent(i)(x y:Zone s X) : beams ((plan s r).T i) x y → adm x→adm y→ i∈chooseE r E x→ i∈chooseE r E y→G i x=G i y
  tax(i)(x:Zone s X) : adm x→ i∈chooseE r E x→ ‖G i x‖≤ D.money i x
variable {P}{adm fresh E}
variable {C:Gold r E adm fresh}{q:CoreX s r→ℝ}
variable [∀ i,Nonempty (X i)][∀ i,StandardBorelSpace (X i)]
variable (v:Virtue s X adm) {G:CoreX s r→ Zone s X→ℂ}(D:Night r P E adm fresh C q)(B: Bronze r P E adm fresh G D)
include D B v
lemma metal (g:Solar P E fresh) (i:CoreX s r) : ∃ f:Zone s X→ℂ, reads X f ((plan s r).T i)∧ Envelope f ∧(∫ x,‖f x‖ ∂πμ X P.μ P.ν i.val) ≤ q i ∧ (∀ x,adm x→fresh x→ i∈ chooseE r E x → f x= G i x)∧ ∀ x, ¬ C.test i x → f x=0 :=by
 let V:Set (Zone s X):= {x| adm x ∧ i∈chooseE r E x}; have h: MeasurableSet V:= MeasurableSet.inter v (vis E g.meas (fun P=> i∈ Contact s r P))
 obtain ⟨f,k,u,l,t⟩:= keep s X (B.bill i) ((plan s r).T i) V h (fun x (p:x∈ V) y (q:y∈V) h=> B.cent i x y h p.1 q.1 p.2 q.2) _ (D.wage_m i).meas (D.ok i) (D.hp i) (fun x (p:x∈V)=> B.tax i x p.1 p.2)
 let F(x):= if C.test i x then f x else 0; have hl(x:Zone s X):‖F x‖≤ D.money i x:=by unfold F; split; exact l x; rw [norm_zero]; exact D.hp i x
 have ht:Envelope F:=⟨u.ite (C.bought i) measurable_const,(D.wage_m i).cost.choose,fun x=> (hl x).trans ((le_abs_self _).trans ((D.wage_m i).cost.choose_spec x))⟩
 refine ⟨F,fun x y p=>?_,ht,(integral_mono (Law.pay ht).norm (Law.pay (D.wage_m i)) hl).trans (D.price i), ?_, fun _ h=> if_neg h⟩
 · unfold F; have he:= C.reads i x y (Tower.whole s r i ▸ p); rw [he,k x y p]
 intro x h g v; unfold F; rw [if_pos ((C.licence x g).mp h i v)]; exact t x (show x∈ V from ⟨h,v⟩)
variable {u:Zone s X→ℂ}
-- include no exclusion; L-hsy
lemma plant(g:Solar P E fresh) :∃ Q:Course P (plan s r), (∀ i,(∫ x,‖Q.G i x‖ ∂πμ X P.μ P.ν i.val) ≤ q i)∧∀ x,fresh x→ eye P Q (chooseE r E x) x= if adm x then ∏ j∈ chooseE r E x,G j x else 0:=by
 choose f h m p t l using metal r v D B g -- order?
 refine ⟨⟨f,m,h⟩,p,fun x u=>?_⟩; unfold eye; split; next g=> exact prod_congr rfl fun i v=> t i x g u v
 next H=>
   rw [C.licence x u] at H; push Not at H; obtain ⟨j,p,q⟩:= H; exact prod_eq_zero p (l j x q)
def stock (f:Zone s X→ℂ):=∑ i:Exc s,∫ x,f x ∂πμ X P.μ P.ν i
-- maybe P implicit now ; tune below
structure Silver (f:Zone s X→ℂ)(G:CoreX s r→Zone s X→ℂ)(u:Zone s X→ℂ): Prop where
    charge (x:Zone s X)(l:fresh x)(q:adm x): f x=(∏ i∈ chooseE r E x,G i x)* Complex.exp (u x)
    night (x:Zone s X)(l:fresh x)(q:¬adm x): f x=0
lemma pilot {f:Zone s X→ℂ}(g:Solar P E fresh)(h:Silver r (adm:=adm) (fresh:=fresh) (E:=E) f G u){J:Type*}[Fintype J][DecidableEq J](T:Teller (gridBase s) adm (esp r E) J u 4 (1/8))(p:Toll (plan s r).T q 4 (1/4)) : Real.exp (-(Fintype.card (Vertex s):ℝ)) ≤ ‖stock (P:=P) f‖:=by
 obtain ⟨R,hr,t',m⟩:= candy r E T g.meas v; obtain ⟨Q,p',t⟩:= plant r v D B g
 have ht:landing s r P Q R=stock (P:=P) f:=by
    apply sum_congr rfl; intro i _; apply integral_congr_ae; filter_upwards [g.ae i] with x hx; change tunic P Q R _ _=f x; rw [← hx.1] -- tune
    change eye P Q (chooseE r E x) x * _= f x; rw [t x hx.2]; split; next b=> rw [h.charge x hx.2 b]; change _*Complex.exp (∑ i,R.A i (chooseE r E x) x)=_; rw [m x b]
    next a=> rw [zero_mul,h.night x hx.2 a]
 rw [← ht,contourT]; apply diner P Q R q; exact ⟨hr,p',p⟩
-- wrapper with ξ cost
lemma billing {f:Zone s X→ℂ}(g:Solar P E fresh)(h:Silver r (adm:=adm) (fresh:=fresh) (E:=E) f G u){J:Type*}[Fintype J][DecidableEq J](T:Teller (gridBase s) adm (esp r E) J u 4 (1/8)){χ:ℝ}(p:feeχ n r≤χ)(k:q= Tower.χwage s r χ): Real.exp (-(Fintype.card (Vertex s):ℝ)) ≤ ‖stock (P:=P) f‖:= by
 apply pilot r v D B g h T; rw [k]; exact Tower.exp_pay s r p
end YM.CF.BProof.Contour.Battery
