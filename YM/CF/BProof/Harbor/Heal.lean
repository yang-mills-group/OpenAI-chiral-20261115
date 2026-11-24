import YM.CF.BProof.Half.Vantage
import YM.CF.BProof.Harbor.Mix
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Bide
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory ProbabilityTheory Cube SU Fock Lat Spire Scroll Pressure Tree RG
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Skye Regard Vogue Mesh Shore
open Wager
namespace Frost
variable {I E D:Type} [Fintype I][DecidableEq I]
variable {N:Side}{u:ℝ}{r q:ℕ}
variable {F:Orbit N→ Pane N}(Q:Quartz N q u r F)
attribute [local instance] measureVal billVal
abbrev PairD (N: Side):= Pane N ×Pane N
abbrev poke {N:Side}(F:Orbit N→Pane N)(x:Orbit N):PairD N:= (x.1, F x)
def paint (Q:Quartz N q u r F)(x: Pane N)(t:Root N)(j:Fin q):= (joint Q.spice x (j,t)).2
-- lodges meet tag gap budget. covers all links consulted. with a det.E
lemma here (T A:Support (More N))(p:halo r A⊆T){x y: Pane N}{v w:Root N}(h:Set.EqOn v w (↑T))(g:Agrees (↑T) x y)(j:Fin q) :Agrees (↑A) (paint Q x v j) (paint Q y w j) :=by
 intro e t u; let U:= x; let W:=y; have ht:Skye.ends e ⊆ A := by simp only [Skye.ends,insert_subset_iff,singleton_subset_iff]; exact ⟨t,u⟩
 let V:Support (More N):=win Q.k e; let f:= Q.spice.P j; have hv:A⊆ T:= (halo_subset r A).trans p; have hh(y:Seat N)(v:y∈V): y∈T:=p (by obtain ⟨_,a,h⟩:=halo_spec.mp v; exact halo_spec.mpr ⟨_,ht a,h.trans Q.fit⟩)
 have hs:f (gauge v x) e = f (gauge w y) e:= (Q.spice.ok j).shore _ _ e (by
     intro l hl hw; specialize g l (hh _ hl) (hh _ hw); dsimp only [Lattice.gauge]; rw [h (hh _ hl),h (hh _ hw),g] -- coe
   )
 unfold paint joint; dsimp only; unfold Lattice.gauge; simp only [Pi.inv_apply]; -- g inside gauge unfolded breaks rewrite
 change (v e.1)⁻¹ * (f (gauge v x) e) *_ = (w e.1)⁻¹* (f (gauge w y) e)*_; rw [hs]; simp only [inv_inv]; rw [h (hv t), h (hv u)] -- h typed
section
variable [NormedAddCommGroup E][NormedSpace ℝ E][MeasurableSpace E][BorelSpace E][FiniteDimensional ℝ E]
abbrev heal (F:Orbit N→Pane N)(f:PairD N→E)(x:Pane N):=meanS (depot N) (fun i=> f (x,F (x,i)))
lemma heal_v (F:Orbit N→Pane N)(p:Measurable F){f:PairD N→E}(h:Envelope f): Envelope (heal F f):= by apply Law.fund (f:=f ∘ poke F) (depot N); exact Law.pull (q:=poke F) h (measurable_fst.prodMk p)
lemma fullM{M:Type*}[MeasurableSpace M](F:Orbit N→Pane N)(p:Measurable F)(v:M→ PairD N→ E)(X:M→Pane N)(h:Envelope (Function.uncurry v))(g:Measurable X) : Envelope fun i=> heal F (v i) (X i):= by apply Law.fund (f:=fun z : M× Ids N=>v z.1 (X z.1, F (X z.1,z.2))) (depot N); exact Law.pull (q:=fun z:M× Ids N=>(z.1,(X z.1,F (X z.1,z.2)))) h (by fun_prop)
lemma warmP (v:Pane N→ E)(p:Envelope v)(U:Pane N): meanS (depot N) (fun t=> v (F (U,t)))=∫ g,∫ i,v (paint Q U g i) ∂paperMeas (Fin q) ∂rootM N:=by
 haveI:= Q.spice.ne; let H(t:Ids N):=F (U,t); let Z(i:Fin q× Root N):=paint Q U i.2 i.1; have hm:Measurable H:= Q.bill.comp measurable_prodMk_left; have hk:Measurable Z:= measurable_snd.comp (joint_m Q.spice U); let μ:=(paperMeas (Fin q)).prod (rootM N)
 change (∫ i, v (H i)∂depot N)=_; rw [←integral_map hm.aemeasurable p.meas.aestronglyMeasurable,show (depot N).map H= _ from (Quartz.lawful Q U), show (fun t: Fin q × Root N=> (joint _ _ t).2)=Z from rfl, integral_map hk.aemeasurable p.meas.aestronglyMeasurable]; exact integral_prod_symm (v ∘ Z) (Law.pay (ν:=μ) (Law.pull (q:=Z) p hk)) -- tune
/-- the mean (not random field) retains the seam property. Forest not used here. -/
lemma hMirror (F:Orbit N→Pane N){a k:ℝ}{z:ℕ}(v:Roof N a k z F)(i:Axis)(g:Pane N→ E)(w: Pane N)(p:Measurable g) : (∫ x, g (Fixed.reflConfig N i (F (w,x))) ∂ depot N)= ∫ x, g (F (Fixed.reflConfig N i w,x)) ∂depot N:=by
 let U:=Fixed.reflectSweep N i; rw [← Law.apply_pres (f:=fun x:Ids N=> g (F (_,x))) (tuft U) (p.comp (v.bill.comp (measurable_prodMk_left)))] -- tune pattern
 apply integral_congr_ae; filter_upwards [sepT (n:=N)] with x hx; rw [← Fixed.flash_reflect i w,v.move w x (Fixed.reflectSweep N i) hx,Fixed.flash_reflect]
end
end Frost
end YM.CF.BProof.Bide
