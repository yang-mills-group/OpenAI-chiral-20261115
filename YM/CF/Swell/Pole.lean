import YM.CF.Swell.Pod
import YM.CF.Sour.Lumen
import YM.CF.Nor.Pile
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant Hove Haro Hest Dial Proa Tye
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Prism Moto Oath Font Levier Rill
attribute [local instance] loreM loreN boreKSpace boreXN
variable {N B m:Side}{r:ℕ}(k:ℕ) {a b c d t e:ℝ}
-- per support trace, compress down.PAYS polynomial power of S not inflated Halo from P.S
variable {P:BudgetPoint}{L:Scree.Loom N}(U:Roof N a e r L)(h:0<e)(hp:P.threshold≤ a)(hT:r+10≤ P.B)(hP:3 ≤ P.B)(hpκ:cipherK r≤ 5*P.B)(hx:HopeT e b t P.order)(hW:P.threshold ≤ t)
variable (S:Support (Cube.More N))(o: Seat N)(p:o∈ S)(X:Scree.Hub N)(xP:X.val.1=o)(p': X.val.2=Lattice.halo P.B S)
variable (C:Toll (Single N))(F:Raw (Openc (Cube.More N) e) (Single N))(g:Suite (badge _) (bail N e) (bail N e) S C F)(T:Ids N)
abbrev spineH(F:Raw (Openc (Cube.More N) e) (Single N))(V:Orbit N):ℂ:= Matrix.trace (F (roller h U V))
abbrev ironM(N:Side)(A:Op (Single N)):FC (Dwell N):= Matrix.trace A • 1
abbrev crest_r(X:Scree.Hub N):Firing N:=coll_T P (lagE X) ∅ (Glyph.cure (ironM N) U h F)
abbrev rent_Φ:InkD N:= fun V=>hollow (crumb (crest_r (P:=P) U h F X (V,T)) ∅) -- unused V!!!!!
include U hp g p' hT
lemma warp_P: Crate P (lagE X) ∅ (lagE X) (Glyph.cure (ironM N) U h F):= Glyph.horn (oreV 1 le_rfl _) U h g hp (by simp [Lattice.halo]) (show halo (r+10) S ⊆ X.val.2 from p' ▸ Corona.halo_mono hT (Subset.refl _)) le_rfl
lemma clean_ψ(V:Orbit N)(Y:Ids N)(t:V.1∈ Sour.σX P (lagE X) ∅): F (roller h U V)=F (roller h U (V.1,Y)):=pact_p h U g V (V.1,Y) (fun i j k=> (fern U hp S ( (show (lagE X).val=Lattice.halo P.B S from p') ▸ (Corona.halo_mono hT (Subset.refl _))) V.1 t i j rfl V.2).trans (fern U hp S ( (show (lagE X).val=Lattice.halo P.B S from p') ▸ (Corona.halo_mono hT (Subset.refl _))) V.1 t i j rfl Y).symm)
lemma clear_K (V:Orbit N)(q:Ids N) : crest_r (P:=P) U h F X V= crest_r (P:=P) U h F X (V.1,q):=by
 let T:=lagE X; let W:=gloss P T ∅ V; unfold crest_r coll_T; split; swap; rfl
 next hv=>exact congrArg (ironM N) (clean_ψ U h hp hT S X p' C F g W q ((pillar T.val (open_l P.threshold T.val (∅:Support (Cube.More N)))).choose_spec.2 V.1 |>.2 hv)) -- tune pillar ambig
lemma sketch(V:Orbit N)(g':pingS P.threshold X.val.2 V.1): rent_Φ (P:=P) U h X F T V.1 = hollow (spineH U h F V):=by
 let W:=crest_r (P:=P) U h F X; unfold rent_Φ; rw [←clear_K U h hp hT S X p' C F g]; refine congrArg hollow ?_; rw [crest_r,(warp_P U h hp hT S X p' C F g).pointV V (by simp [Sour.σX,litres,g',lagE])]; simp [crumb,ironM,Glyph.cure,spineH] -- order.T
include g T
lemma pond_L:LocalOn X.val.2 (rent_Φ (P:=P) U h X F T):= fun V W' p=> congrArg (fun a=> hollow (n:=Dwell N) (crumb a ∅)) ((warp_P U h hp hT S X p' C F g).latch (V,T) (W',T) p (fun _ _=>rfl))
lemma stampK (V:Pane N)(Q:Seat N→SU.E):rent_Φ (P:=P) U h X F T (Lattice.gauge Q V) = Scree.paintR false false (tradew N Q) (rent_Φ (P:=P) U h X F T V):=by
 let U':=Lattice.gauge Q V; let V': Orbit N:=(V,T); let W:Orbit N:= (U',threadG Q T)
 have hx:= ((warp_P U h hp hT S X p' C F g).tanG V' Q); let Ω:= crest_r (P:=P) U h F X; change hollow (n:=Dwell N) (crumb (crest_r (P:=P) U h F X _) ∅)=_
 have hxP(A:FC (Dwell N)):crumb (sauce false false (tradew N Q) A) ∅=crumb A ∅:=by
    let K:=quantU (spice (tradew N Q) false); let T:=vacuum (Dwell N); have he:acts K.val T=T:=quant_vac ..; have hh(A):crumb A ∅=inner ℂ T (acts A T):=by rw [basis_inner, Sault.col]; -- tune
    rw [hh,hh]; unfold sauce; change inner ℂ T (acts (twist K A) T)= _; nth_rw 1 [←he]; rw [show acts _ _=acts K.val (acts A T) from Eq.symm ((Fock.swivel ..).trans (congrArg (acts (twist K A)) he))]; exact act_unit_inner K T _ -- tune actual lemma
 rw [←clear_K U h hp hT S X p' C F g W,show crest_r (P:=P) U h F X W=_ from hx,hxP]; exact (show _ from (Pastry.fold_hollow ..).symm)
lemma muskP: Measurable (rent_Φ (P:=P) U h X F T):=by
 have he:Measurable (fun V:Pane N=> crest_r (P:=P) U h F X (V,T)):= (warp_P U h hp hT S X p' C F g).virtue.comp (measurable_id.prodMk measurable_const)
 have hp:Continuous (fun x:ℂ=> hollow (n:=Dwell N) x):= Continuous.subtype_mk (continuous_id.smul continuous_const) _ -- tune
 exact hp.measurable.comp (((continuous_id.matrix_elem ∅ (∅: Finset (Dwell N))).measurable).comp he)
end YM.CF.Swell
