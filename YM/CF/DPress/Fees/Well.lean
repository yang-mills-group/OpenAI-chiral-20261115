import YM.CF.DPress.Fees.Jewel
/-!
 Diameter on Cusp.Stake, nothing tested by differentiating Tome witnesses.
 -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.DPress.Fees
open Function Lattice MeasureTheory Filter Metric Analytic Finset
open Lat Cube RG Fock Pastry Skye Scree Vow Mew Jet Hake JetRead Wray -- joinV
open scoped Topology Classical BigOperators ContDiff Matrix Matrix.Norms.L2Operator YM.CF.Mew
attribute [local instance] opCStarAlgebra
variable {n:Side}(P:BudgetPoint)(h:ℝ)(R:Scree.Hub n)(X:Force n)(S t:Support (More n)) {a L:ℝ}
namespace Rails
abbrev γGood (P:BudgetPoint)(S:Support (More n)):Set (Orbit n):={x| x.1∈Good P S}
abbrev ηPulse (i: Cribs n)(D:Support (More n))(x: Orbit n) (u: Copy n) (v:tangD n):ℂ:= crumb (u (pressQ P D x.1 v,x.2)).val i
abbrev scroll (x:Orbit n)(i:Cribs n) := cover (fun D:Support (More n)=>hood (ηPulse P i D x) (Launch P.order)) {D| t⊆ D}
abbrev armor(i:Cribs n):Dial (Copy n):= cover (fun x=>scroll P t x i) (γGood P (S\t))
abbrev shield: Dial (Copy n):= staff (armor P S t) (stake h) univ
variable {F:Copy n}
lemma spineH (p:∃ d, Medal P S t F h d)(i:Cribs n): Live (armor P S t i) F:=by
 obtain ⟨d,z⟩:=p; obtain ⟨b,v,h,V⟩:=z.pays; have he(i):0≤ b i:= v i; refine ⟨b i,(covering ..).2 ⟨he _,fun x g=> (covering ..).2 ⟨he _,fun d u=>landing.mp ?_⟩⟩⟩; exact (LaunchQ P.order (ηPulse P i _ _ F)|>.2 ((h x g (Y:=d) u).haveP i).earned)
variable (p:1≤h)
include p
lemma armourC : Receipt (fun f v=> Medal P S t f h v) (shield P h S t):=by
 let A:=armor P S t; let w:=fun i:Cribs n=>stake h i; have hu(i):1 ≤ w i:= one_le_pow₀ p; constructor; · intro x a H; obtain ⟨c,u,q,v⟩:=H.pays; refine (staff_up A w (fun i _=>zero_le_one.trans (hu i)) c (fun i (_:i ∈ univ)=> (covering (x:=x) _ _).2 ⟨u _,fun V h=> (covering _ _).2 ⟨u _,fun D g=>landing.mp ?_⟩⟩)).up v; exact (LaunchQ P.order (ηPulse P i _ _ x)).2 ((q _ h (show t⊆ D from g)).haveP i).earned
 rintro x a ⟨q,V⟩ f; let u:=fun i=> meter (A i) x; let p':=spineH P h S t ⟨q,V⟩; refine { V with pays:=⟨u,fun i=>(Live.pays (p' i)).p, fun x' p {D} b=> ?_, staff_due A w (fun i _=>zero_le_one.trans (hu i)) f (fun i _=>p' i)⟩}; obtain ⟨c,l,y,z⟩:=V.pays; let W:=y x' p b; refine ⟨W.own,fun i=> ?_ ⟩; let f0:= W.haveP i; have hv:=landing.mpr ((covering _ _|>.1 ((covering _ _|>.1 (Live.pays (p' i))).2 x' p)).2 D b); exact ⟨f0.smooth,(LaunchQ ..|>.1 hv)⟩
lemma armorB(f:ℂ → Copy n)(g:Listen L f (γGood P (S\t)))(e:∀ z∈ank L,Medal P S t (f z) h a)(k:1<L):Brings L f (f 1-f 0) (shield P h S t):=by
 apply Brings.stage; intro i _; apply Brings.covered; intro U x; apply Brings.covered; intro D v; apply Brings.hold; refine JetRead.merit (x:=fun z V=>crumb (f z (V,U.2)).val i) x (fun s v=>holoB _ (s,U.2) _ (g _ v)) (a:=a) (fun z y v b=>?_ ) k; obtain ⟨r,c,q,T⟩:= (e z y).pays; let g:= (q (v,U.2) b (Y:=D) ‹D∈ {D|t⊆D}›).haveP i; exact ⟨g.smooth,g.earned.trans (by_bill (fun i=>c i) (fun _=>one_le_pow₀ p) i T)⟩ -- tune n.
section Force
abbrev sure (X:Force n)(i:Cribs n)(x:Orbit n)(u:Copy n)(v:tangD n):ℂ:= crumb (u (sting P X.val.2 x.1 v,x.2)).val i
abbrev soul(H:Force n) := H.val.1.val
abbrev χPulse (i:Cribs n): Dial (Copy n):= cover (fun x=> hood (sure P X i x) (loft P (soul X).1)) (γGood P ((soul X).2 \ X.val.2))
abbrev βs(X: Force n):= Scree.tariff P (soul X).1 h
abbrev streak: Dial (Copy n):=staff (χPulse P X) (βs P h X) univ
private lemma hb(i:Cribs n):1 ≤ βs P h X i:=one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by simp)) (one_le_pow₀ p)
lemma spirit(f:Copy n)(t:∃ b:ℝ,ForceB P X f h b)(i:Cribs n): Live (χPulse P X i) f:=by obtain ⟨a,t⟩:=t; obtain ⟨c,v,u,t⟩:= t.costP; exact ⟨c i,(covering ..).2 ⟨v _,fun z hv=> landing.mp ((loftQ _ (u z hv i).paid).1 (u z hv i))⟩⟩
lemma chiC : Receipt (fun f v=> ForceB P X f h v) (streak P h X):=by
 let A:=χPulse P X; constructor; · intro x a b; obtain ⟨c,l,g,v⟩:= b.costP; refine (staff_up A _ (fun i _=>zero_le_one.trans (hb P h X p i)) c (fun i (_:i∈univ)=> (covering (x:=x) _ _).2 ⟨l i,fun V t=> landing.mp ?_⟩)).up v; exact (loftQ _ (g V t i).paid).1 (g V t i)
 rintro x a ⟨b,v⟩ o; let H:=spirit P h X p x ⟨b,v⟩; obtain ⟨t,k,y,u⟩:=v.costP; refine {v with costP:=⟨fun i=>meter (A i) x,fun i=>(Live.pays (H i)).p,fun U h i=>?_,staff_due A (βs P h X) (fun i _=>zero_le_one.trans (hb P h X p i)) o (fun i _=>H i)⟩}; exact (loftQ (sure P X i U x) (y _ h i).paid).2 (landing.mpr ((covering _ _|>.1 (Live.pays (H i))).2 U h)) -- tune h shadow
lemma chiB(f:ℂ→ Copy n)(g:Listen L f (γGood P ((soul X).2\ X.val.2)))(v:∀ z∈ank L,ForceB P X (f z) h a)(k:1<L):Brings L f (f 1-f 0) (streak P h X):=by
 apply Brings.stage; intro i _; apply Brings.covered; intro C x; apply Brings.hold; apply JetRead.coal (x:=fun z V=> crumb (f z (V,C.2)).val i) x (fun s v=>holoB _ (s,C.2) _ (g _ v)) (a:=a) _ k; intro z p' U q; obtain ⟨b,t,u,W⟩:= (v z p').costP; exact Prism.high (u (U,C.2) q i) (by_bill t (hb P h X p) i W) -- tune
end Force
end Rails
end YM.CF.DPress.Fees
