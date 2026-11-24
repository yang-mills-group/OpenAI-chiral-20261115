import GaugeFieldConstruction.MarinStockNX
import GaugeFieldConstruction.PhysicalBook
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3600
set_option linter.unusedSectionVars false
set_option maxHeartbeats 440000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Ballad
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Lifted Bilinear Window Skye
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker InnerProductSpace Topology Classical
attribute [local instance] opCStarAlgebra
variable {R:ℕ}{B N:Side}
open YM.CF.Lamour.Bridge.Celeste
open Py.Rate.LocalLimit.Papal (Weaver household)
open Kea
open Flare
open YM.GaugeFieldConstruction.Matter
-- `Λbasis` Canonical 72, spin-paired arbitrary birth nonzero or not.Use D(ΦMask).
open Lead
-- Need weights combine real lease into a spin-stake. Any G-neutral W price. helper ℂ. not anti-charge formulas.
variable (p:Cover)(n:Side)(K:Calibration)
private lemma book_emptySt {N:Side} (x:Fields N)(k:VFlavorNX) : VLeadNX k 1=bookColorNX k:=by rw [VLeadNX,map_one]; exact mul_one _
local notation "I#" => VFlavorNX × Fin 2 × Fin 2
local notation "c#" => SpinIdx × SU.Slot
abbrev noLagSt (p:Cover): Lead 0 := ⟨p,p,0,false,[],(by simp [direction,sail]),rfl,rfl⟩
abbrev perCallSt (A: Op SpinIdx)(p: VFlavorNX→ℂ)(i:VFlavorNX × Fin 2 × Fin 2) := A (upSpin i.2.1) (dnSpin i.2.2)*p i.1
noncomputable abbrev onMarkSt (o:Cover)(i:I#):Family K:= fun j=> (noLagSt o).rollNX i.1 i.2.1 i.2.2 (K.c j)
private lemma reading_prices_st (A: Op SpinIdx)(W: Op SU.Slot)(p: VFlavorNX→ℂ)(q:W=coeffs p) (t s:SU.Slot)(i j:Fin 2) : (A ⊗ₖ W) (upSpin i,t) (dnSpin j,s)=∑ k:VFlavorNX,perCallSt A p (k,i,j)*bookColorNX k t s:=by
 have hv: W=∑ k:VFlavorNX,p k • (bookColorNX k):= by
    refine q.trans ?_; change jordan p=_; rw [show jordan p= _ from congrArg (fun x=>jordan x) (YM.GaugeFieldConstruction.Phys.diagonals p).symm, map_sum]; simp_rw [map_smul]; rfl
 rw [hv,Matrix.kroneckerMap_apply, Matrix.sum_apply,mul_sum]; refine sum_congr rfl fun k _=>?_ ; change _* (p k * _)=(_* p k)*_; ring

lemma plusPaneSt : plusHalf = univ.image upSpin :=by decide +kernel
lemma minusPaneSt : plusHalfᶜ= univ.image dnSpin:=by decide +kernel
private lemma gridIndex_st {α A :Type}[Fintype α][DecidableEq α][AddCommMonoid A](z:Finset SpinIdx)(F:SpinIdx × α→A)(g:Fin 2→SpinIdx)(h:Injective g)(p: z=Finset.univ.image g):
   (∑ i∈ Finset.univ.filter (fun i:SpinIdx × α => i.1∈ z),F i)= ∑ j:Fin 2,∑ k:α,F (g j,k):=by
 rw [show Finset.univ.filter (fun i:SpinIdx × α=> i.1∈ z)= z ×ˢ Finset.univ from (Finset.ext (fun _=>by simp)),Finset.sum_product,p, Finset.sum_image (fun _ _ _ _=>@h _ _)]
local notation "U#" => Finset.univ.filter (fun i:SpinIdx × SU.Slot => i.1∈ plusHalf)
local notation "D#" => Finset.univ.filter (fun i:SpinIdx × SU.Slot => i.1∉ plusHalf)
variable {o:Cover}
lemma truePocket_st {G:Family K} {W:Op SU.Slot}{A:Op SpinIdx}{p:VFlavorNX→ℂ}(q:W= coeffs p)(h:G= ∑ i∈ Finset.univ.filter (fun i:SpinIdx × SU.Slot => i.1∈ plusHalf),∑ l∈ Finset.univ.filter (fun i:SpinIdx × SU.Slot => i.1∉ plusHalf), (A⊗ₖ W) i l • (creation K o i.1 i.2 * removal K o l.1 l.2)) : G=∑ i:VFlavorNX × Fin 2 × Fin 2,perCallSt A p i • onMarkSt K o i:=by
 let Z(b c:SpinIdx × SU.Slot) := (creation K o b.1 b.2 * removal K o c.1 c.2); let x:= fun b c:SpinIdx × SU.Slot => (A ⊗ₖ W) b c • Z b c;
 let Q(i j:Fin 2)(u v:SU.Slot):= x (upSpin i,u) (dnSpin j,v); let up:= upSpin; let dn:= dnSpin
 have he: (Finset.univ.filter (fun i:SpinIdx × SU.Slot=> i.1∉ plusHalf))= Finset.univ.filter (fun i:SpinIdx × SU.Slot=> i.1∈ plusHalfᶜ):= Finset.ext fun _=>by simp
 have p₁:Injective up:=by decide
 have p₂:Injective dn:=by decide
 have h₂(i: Fin 2)(u:SU.Slot): (∑ c∈ Finset.univ.filter (fun i:SpinIdx × SU.Slot=> i.1∉ plusHalf),x (up i,u) c)= ∑ j:Fin 2,∑ v:SU.Slot,Q i j u v:= he ▸ gridIndex_st (plusHalfᶜ) _ dn p₂ minusPaneSt -- tune
 have h₀:G=∑ i:Fin 2,∑ j:Fin 2,∑ u:SU.Slot,∑ w:SU.Slot,Q i j u w:=by
    refine h.trans ?_; refine Eq.trans (gridIndex_st plusHalf (fun i=>∑ x'∈ Finset.univ.filter (fun i:SpinIdx × SU.Slot=> i.1∉ plusHalf),x i x') up p₁ plusPaneSt) ?_; simp_rw [h₂]; refine sum_congr rfl (fun i _=> Finset.sum_comm)
 rw [h₀]; funext n V
 let k(i:I#)(u v:SU.Slot): FC (Single (K.c n)) := bookColorNX i.1 u v • (Z (up i.2.1,u) (dn i.2.2,v) n V)
 have hm(c:I#): onMarkSt K o c n V =∑ u:SU.Slot,∑ v:SU.Slot,k c u v:=by
    change ∑ u:SU.Slot,∑ v:SU.Slot,VLeadNX c.1 1 u v • _= _; rw [book_emptySt V]; rfl
 let f(i j:Fin 2)(b:VFlavorNX)(u l:SU.Slot):= perCallSt A p (b,i,j) • (k (b,i,j) u l)
 have ht(i j:Fin 2)(u l:SU.Slot): Q i j u l n V=∑ b:VFlavorNX, f i j b u l:=by
    change (A⊗ₖ W) (upSpin i,u) (dnSpin j,l) • Z _ _ n V= _; rw [reading_prices_st A W p q,Finset.sum_smul]; apply Finset.sum_congr rfl; intro t h; exact mul_smul (perCallSt A p (t,i,j)) (bookColorNX t u l) _
 simp_rw [Finset.sum_apply,ht,Pi.smul_apply,hm,Finset.smul_sum]
 have hp(i j) : (∑ u, ∑ l, ∑ b,f i j b u l)= ∑ b:VFlavorNX,∑ u:SU.Slot,∑ l:SU.Slot,f i j b u l:=by
    apply Eq.trans ((Finset.sum_congr rfl (fun u _=> Finset.sum_comm (f:=fun l b=> f i j b u l)))); exact Finset.sum_comm
 let Z':= fun (x:I#)=>∑ u,∑ v,f x.2.1 x.2.2 x.1 u v; let ZC i j b:=∑ u,∑ l,f i j b u l
 simp_rw [hp]; change (∑ i,∑ j,∑ b,ZC i j b)= ∑ x:I#, Z' x; rw [Fintype.sum_prod_type Z']; simp_rw [Fintype.sum_prod_type (fun i:Fin 2 × Fin 2=> Z' (_,i))]; change _= ∑ b,∑ i,∑ j,ZC i j b
 refine Eq.trans (?_:_=∑ i,∑ b,∑ j,ZC i j b) Finset.sum_comm
 exact sum_congr rfl fun i _=> Finset.sum_comm
#print axioms truePocket_st
end YM.CF.Buffered.Ballad
end
