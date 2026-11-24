import YM.SU5.SatinWard.Resolution.Fly
import YM.SU5.SatinWard.Resolution.Chamber
import Anomaly.Scoff.Stamp
import Anomaly.Compass.Lute

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 700000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Vow.TreasuryFog
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
lemma wears_velvet (g:s∈twoPlanes (mid N B)):Bay.C.Velvet s:=by
 let V:= Levier.spinU s.charge s.s; let t:=(spinningWithCharge s.s g s.charge V (Levier.spinZ ..)); obtain ⟨f,h⟩:=Ione.Clock.nice_eq V t; intro i j k u v; exact f.injective ((h i j u).symm.trans (h i k v))
lemma sparkle (p':Barrage p q (grooveB m p (node o)) h E x a b)(z:s∈twoPlanes (mid N B))(y:Site Ω)(v:Earlier s o y): Barrage p q (grooveB m p (node y)) h (cartTurn s E) x a b:=by
 have ht:=Bay.C.crew s (wears_velvet z) p'; have h': actY s (grooveB m p (node o))=grooveB m p (node y):=by
    unfold grooveB; ext i; unfold actY; rw [mem_map_equiv, ←show boxA s (node y)=node o from v]; simp [halo_spec,sitT] -- tune
 rw [h'] at ht
 rw [show cartTurn s E= _ from (?_: _=Bay.C.quiver s E)]
 · exact ht
 funext i V; obtain ⟨i,rfl⟩:=(moldA s).surjective i; obtain ⟨V,rfl⟩:= yspec s V; exact (runs ..).trans (Bay.C.salute ..).symm
open Swell
variable {Φ:ArcΦ}{U:Cusp (mid N B)}{ξ:ℂ}{L:RegBudget (mid N B)} {S:Support (More (mid N B))} {e z:ℝ}{l':ℕ}
lemma marks_target {G F' M' N':Aura (mid N B)→ℝ}(H:∀ i,YM.CF.Sour.Flight p q i h (E i) (G i) (F' i))(t:Ids (mid N B))(y:Site Ω)(u:Earlier s y o) (W:∀ i,YM.CF.Sour.Flight p q i h (cartTurn s⁻¹ E i) (M' i) (N' i)):
    turn_V s (marksCopy p (singlePole t E H (node o)))= marksCopy p (singlePole t (cartTurn s⁻¹ E) W (node y)):=by
 funext x; let T':=marksTurn (N:=N) (B:=B) s⁻¹ (o:=fun _=>o) (u:=fun _=>y) (fun (_:Fin 1) i=> H i) (fun (_:Fin 1) i=> W i) t (0:Fin 1) (0:Fin 1) (fun U _ i=> runs s⁻¹ E U i) ((QuadClock.earlier_mills ..).mp u.backward) (yellA s x)
 rw [Clock.y_rev] at T'; exact T'.symm
lemma FlintPull (χ:SweepSign Ω)(V:Flint p E (grooveB m p (node o)) L U ξ Φ o l q h x a b e z w)(hp:0≤h)(y:Site Ω)(i: Earlier s y o)(v:HavenL Ω p l)(p':s∈χ.group) : Flint p (cartTurn s⁻¹ E) (grooveB m p (node y)) (Eρ s L) (Kρ s U) (tρ s ξ) (turnD s Φ) y l q h x a b (duty_Q p.order p.power*e) (strive_E p.order*z) w:= by
 have hu:= χ.fits p'; obtain ⟨G',Q,H,z'⟩:= V.step.price
 refine ⟨halo_subset _ _ (mem_singleton_self _),sparkle V.step ((twoPlanes Ω).inv_mem hu) _ i.backward,?_⟩
 intro t X G W; rw [←marks_target H _ y i W]; exact restoreTwo s hu y o i hp v (V.mood t G' Q H)
lemma Flint_owner (V:Flint p E S L U ξ Φ o l q h x a b e z w) :∀ (i:Aura Ω)(x:Orbit Ω),Sector (camp i.val) false (E i x):=by
 obtain ⟨G,F,Q,t⟩:=V.step.price; exact fun i x=>(Q i).tube.body x
lemma Flint_bag {E':Bag Ω}{L':RegBudget Ω}{U':Cusp Ω}{ξ':ℂ}{Φ':ArcΦ}{τ ψ b₁ β b':ℝ}(V:Flint p E S L U ξ Φ o l q h x a b e z w)(Y:Flint p E' S L' U' ξ' Φ' o l q h x τ b' ψ b₁ β) (hp:0≤h): Flint p (E+E') S (L+L') (U+U') (ξ+ξ') (Φ+Φ') o l q h x (a+τ) (b+b') (e+ψ) (z+b₁) (w+β):=by
 refine ⟨V.yard,V.step.plusR Y.step, fun t X U p'=>?_⟩; obtain ⟨G,F,Q,g⟩:= V.step.price; obtain ⟨b,d,h,g'⟩:=Y.step.price
 rw [poles_up Q t (node o) h p',show marksCopy p (_+_)=_ from funext fun v:Orbit Ω=> ripe_H p v _ _]
 exact Ice.plan_ADD o l (V.mood t G F Q) (Y.mood t b d h) hp
lemma Flint_coin (V:Flint p E S L U ξ Φ o l q h x a b e z w)(hp:0≤h) (v:ℝ): Flint p (v • E) S (v • L) (v • U) (v • ξ) (v • Φ) o l q h x (|v| *a) (|v| *b) (|v| *e) (|v| *z) (|v| *w):=by
 rw [← Complex.coe_smul v E]; have ht:v=(v:ℝ):=rfl
 refine ⟨V.yard,?_,fun t X Q F=>?_⟩
 · simpa only [Complex.norm_real,Real.norm_eq_abs] using V.step.swell (v:ℂ)
 obtain ⟨H,G,P,Q'⟩:= V.step.price
 rw [pole_scale P t (node o) (v:ℂ) F]; let J:= singlePole t E P (node o)
 rw [show marksCopy p ((v:ℂ) • J)= v • marksCopy p J from ?_]; exact realV _ v (V.mood t H G P) hp
 funext i; change exponentL p _ i.1=_; rw [voc_E p _ _ i]; exact Complex.coe_smul ..
lemma Flint_gather {ι:Type*} (F:Finset ι)(SΨ:node o∈ S)(G:ι→ Bag (mid N B))(U:ι→RegBudget (mid N B))(Z:ι→Cusp (mid N B))(c:ι→ ℂ)(Φ:ι→ArcΦ)(a b y z w:ι→ ℝ)(V:∀ i∈F,Flint p (G i) S (U i) (Z i) (c i) (Φ i) o l q h x (a i) (b i) (y i) (z i) (w i))(hp:0≤h): Flint p (∑ i∈F,G i) S (∑ i∈F,U i) (∑ i∈F,Z i) (∑ i∈F,c i) (∑ i∈F,Φ i) o l q h x (∑ i∈F,a i) (∑ i∈F,b i) (∑ i∈F,y i) (∑ i∈F,z i) (∑ i∈F,w i):=by
 induction F using Finset.induction_on with
 | empty=> simp only [sum_empty]; exact voidFlint SΨ
 | insert i F t ih=> simp only [sum_insert t]; exact Flint_bag (V i (mem_insert_self ..)) (ih fun j u=> V j (mem_insert_of_mem u)) hp
lemma Flint_fade (V:Flint p E S L U ξ Φ o l q h x a b e z w) {ψ:ℝ}(pΨ:ψ≤x):Flint p E S L U ξ Φ o l q h ψ a b e z w:= ⟨V.yard,V.step.lessR pΨ,V.mood⟩ -- name shadow
end YM.CF.Vow.TreasuryFog
