import YM.CF.Acorn.Merry
set_option autoImplicit false
noncomputable section
namespace YM.CF.Acorn
open Function Filter Metric Lat Finset Tenant Branch Fock Dial MeasureTheory Phase Phase.Sample Lattice Cube Broc Drapes Tulip Peaks Brace Paige Rush Matrix Jet
open scoped Topology Matrix BigOperators ContDiff NNReal Matrix.Norms.L2Operator InnerProductSpace
set_option synthInstance.maxSize 8000
attribute [local instance] opCStarAlgebra
variable {j:ℕ}{L B:Side}{ho:Odd L.val}{T:Script Male}{Y:Pricing j L ho T}{e:ℝ}{m:Side}(g:Grasp Y B e)(n:ℕ)(K:ℝ)(R:Repair j)
variable (p:e≤R.d)(q:g.baseline≤ R.d)
def neat (g:Grasp Y B e)(m:Side)(i:Male)(x: Skin m B): Wave (Iota (idrat (CSide m B))):= cartsL (switchG (idrat (CSide m B))).symm (tune g i x)
def billV:=min (R.a/2) (radF g)
lemma billVP:0<billV g R:=lt_min (half_pos R.pa) (rad_pos _)
lemma burst (ht:1≤K): ∃ C D:ℝ,0≤C ∧0≤D ∧ ∀ m:Side, R.n ≤(CSide m B).val→g.roundZ≤(CSide m B).val→∀ M:Male, let G:=idrat (CSide m B)
           let X:=Tier m B n e g.baseline K; let J:=liftC (m:=m) g R p q; let A:=fun x:Senso m g=> repeated j M G (post (J x).val); let P:=fun x:Senso m g=>proto M G (post (J x).val)
           ∃ F:Senso m g→ℂ, Acorn.Funds X (tempo G 1).home A P (fun i=> neat g m M i.val.1) F (billV g R) (4*C) C D:=by
 obtain ⟨C,c,h⟩:=exc_shop n K R ht; obtain ⟨D,d,T'⟩:=savings g n ht
 obtain ⟨V,v,H⟩:=vw (K:=R.K) n (zero_le_one.trans ht) R.pa R.pd; have hv:0≤ V:=zero_le_one.trans v
 have hp:0≤ quartzK R.a R.K:= qp _ _ R.pK.le
 refine ⟨C,‖facet‖*(V*quartzK R.a R.K)+‖folio'‖*D,c,by positivity,fun m u f i=>?_⟩; intro G X J A P
 let F(x:Loom G R.d):=Matrix.trace (ingot false (repeated j) i G (post x.val)); let Y:= song m B (g.cost m i)
 let Z(x:Brace.Chord m B e g.p):= Y x.val.1 x.val.2
 obtain ⟨p₁,p₂⟩:=h (idrat (CSide m B)) rfl u i
 have he := lx (m:=m) g n K R p q
 have hg : Screen _ _ _ F (R.a/2) _:= H G (ingot false (repeated j) i G) _ (R.start i G rfl u)
 have Q₁:= (flash_d ((hg.reserve (min_le_left (R.a/2) (radF g)) le_rfl).lin facet le_rfl)).pull he
 let U':=plusC (m:=m) g
 have Q₂ : Wallet X (billV g R) (‖folio'‖*D) ((folio' ∘ Z) ∘ U') := (flash_d (((T' m f i).reserve (min_le_right ..) le_rfl).lin folio' le_rfl)).pull (cop_t g n K)
 let t:=(facet ∘ F) ∘ J+ ((folio' ∘ Z) ∘ U')
 have hT (x:Senso m g) := R.ahead (CSide m B) u (J x).val (J x).property i
 refine ⟨t,⟨((p₁.pull _ he).weak le_rfl (min_le_left ..)), (p₂.pull _ he).weak le_rfl (min_le_left ..), Q₁.add Q₂,fun x=> ⟨(hT x).2.2,skew_square ..,(hT x).2.1⟩,fun x=>?_⟩⟩
 let L:=switchG G
 let u:=coneP j i x.val.1 x.val.2
 have hv: filled (A x) (P x)=cartsL L.symm u:=by unfold P proto; rw [chord_same]; exact relabelF L.symm (starC (hook x.val.2 ∘ node) (fun _=>hookN ..)) ((g.broadness _ f i).projection _ x.property.1)
 have hy: ‖u‖=Real.exp ((F (J x)).re/4):=by rw [← carts_n L.symm,←hv]; exact (hT x).1.symm
 rw [hv, show u= Complex.exp (t x) • tune g i x.val.1 from ?_,carts_s]; rfl
 unfold t; rw [Pi.add_apply,Function.comp_apply,Function.comp_apply,Function.comp_apply,Function.comp_apply,facetP,folioT]
 exact phaseLift g.topB g.baseY.1 (g.couture f i) _ x.property.1 _ (plusC g x).property.2 ((F (J x)).re/4) hy
end YM.CF.Acorn
